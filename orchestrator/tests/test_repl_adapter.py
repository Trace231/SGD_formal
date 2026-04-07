"""Unit tests for native REPL adapter normalization/error mapping."""

from __future__ import annotations

import json

from orchestrator import repl_adapter


class _FakeStdin:
    def __init__(self) -> None:
        self.writes: list[str] = []
        self.closed = False

    def write(self, payload: str) -> None:
        self.writes.append(payload)

    def flush(self) -> None:
        return None

    def close(self) -> None:
        self.closed = True


class _FakeStdout:
    def __init__(self, responses: list[str]) -> None:
        self._responses = list(responses)

    def readline(self) -> str:
        if not self._responses:
            return ""
        return self._responses.pop(0)


class _FakeProc:
    def __init__(self, responses: list[str]) -> None:
        self.stdin = _FakeStdin()
        self.stdout = _FakeStdout(responses)
        self.stderr = _FakeStdout([])
        self._rc = None

    def poll(self):
        return self._rc

    def terminate(self) -> None:
        self._rc = 0

    def wait(self, timeout=0):  # noqa: ARG002
        self._rc = 0
        return 0

    def kill(self) -> None:
        self._rc = -9


def test_verify_with_repl_normalizes_success(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()

    class _Proc:
        stdout = json.dumps(
            {
                "env": 1,
                "messages": [
                    {"severity": "info", "pos": {"line": 1, "column": 1}, "data": "ok"},
                ],
                "sorries": [],
            }
        )

    monkeypatch.setattr(
        repl_adapter.subprocess,
        "run",
        lambda *args, **kwargs: _Proc(),
    )
    out = repl_adapter.verify_with_repl(
        code="theorem t : True := by\n  trivial\n",
        repl_workspace=ws,
        project_root=None,
        lake_path="lake",
        timeout=10,
    )
    assert out["pass"] is True
    assert out["complete"] is True
    assert out["backend_used"] == "apollo_repl"
    assert out["backend_reason"] == "repl_success"


def test_verify_with_repl_timeout_maps_error(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()

    def _raise_timeout(*args, **kwargs):
        raise repl_adapter.subprocess.TimeoutExpired(cmd=["lake"], timeout=1)

    monkeypatch.setattr(repl_adapter.subprocess, "run", _raise_timeout)
    try:
        repl_adapter.verify_with_repl(
            code="theorem t : True := by\n  sorry\n",
            repl_workspace=ws,
            project_root=None,
            lake_path="lake",
            timeout=1,
        )
        assert False, "expected timeout runtime error"
    except RuntimeError as exc:
        assert "repl_timeout" in str(exc)


def test_verify_with_repl_invalid_json_maps_protocol_error(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()

    class _Proc:
        stdout = "NOT_JSON"

    monkeypatch.setattr(
        repl_adapter.subprocess,
        "run",
        lambda *args, **kwargs: _Proc(),
    )
    try:
        repl_adapter.verify_with_repl(
            code="theorem t : True := by\n  sorry\n",
            repl_workspace=ws,
            project_root=None,
            lake_path="lake",
            timeout=10,
        )
        assert False, "expected protocol runtime error"
    except RuntimeError as exc:
        assert "repl_protocol_error" in str(exc)


def test_repl_session_prime_and_verify(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()
    responses = [
        json.dumps({"env": 5, "messages": [], "sorries": []}) + "\n",
        json.dumps({"env": 5, "messages": [], "sorries": []}) + "\n",
    ]
    fake_proc = _FakeProc(responses)

    monkeypatch.setattr(repl_adapter.subprocess, "Popen", lambda *args, **kwargs: fake_proc)
    monkeypatch.setattr(repl_adapter.select, "select", lambda *args, **kwargs: ([fake_proc.stdout], [], []))

    with repl_adapter.ReplSession(ws, "lake", 5) as session:
        env_id = session.prime_header("import Main")
        out = session.verify("theorem t : True := by\n  trivial\n", env=env_id)
        assert out["pass"] is True
        assert out["env_id"] == 5

    assert len(fake_proc.stdin.writes) == 2
    first_cmd = json.loads(fake_proc.stdin.writes[0].split("\r\n\r\n")[0])
    second_cmd = json.loads(fake_proc.stdin.writes[1].split("\r\n\r\n")[0])
    assert first_cmd["cmd"] == "import Main"
    assert second_cmd["env"] == 5


def test_repl_session_accepts_multiline_json(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()
    prime_lines = json.dumps({"env": 5, "messages": [], "sorries": []}, indent=2).splitlines(True)
    verify_lines = json.dumps({"env": 5, "messages": [], "sorries": []}, indent=2).splitlines(True)
    fake_proc = _FakeProc(prime_lines + verify_lines)

    monkeypatch.setattr(repl_adapter.subprocess, "Popen", lambda *args, **kwargs: fake_proc)
    monkeypatch.setattr(repl_adapter.select, "select", lambda *args, **kwargs: ([fake_proc.stdout], [], []))

    with repl_adapter.ReplSession(ws, "lake", 5) as session:
        env_id = session.prime_header("import Main")
        out = session.verify("theorem t : True := by\n  trivial\n", env=env_id)
        assert out["pass"] is True
        assert out["env_id"] == 5


def test_repl_session_prime_protocol_error(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()
    fake_proc = _FakeProc(['{"message":"Unknown environment."}\n'])
    monkeypatch.setattr(repl_adapter.subprocess, "Popen", lambda *args, **kwargs: fake_proc)
    monkeypatch.setattr(repl_adapter.select, "select", lambda *args, **kwargs: ([fake_proc.stdout], [], []))

    with repl_adapter.ReplSession(ws, "lake", 5) as session:
        try:
            session.prime_header("import Main")
            assert False, "expected protocol error"
        except RuntimeError as exc:
            assert "repl_session_protocol_error" in str(exc)


def test_verify_with_repl_unknown_environment_is_protocol_error(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()

    class _Proc:
        stdout = '{"message":"Unknown environment."}'

    monkeypatch.setattr(
        repl_adapter.subprocess,
        "run",
        lambda *args, **kwargs: _Proc(),
    )
    try:
        repl_adapter.verify_with_repl(
            code="theorem t : True := by\n  trivial\n",
            repl_workspace=ws,
            project_root=None,
            lake_path="lake",
            timeout=10,
        )
        assert False, "expected protocol runtime error"
    except RuntimeError as exc:
        assert "repl_protocol_error" in str(exc)


def test_verify_with_repl_uses_project_lake_env(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    (ws / ".lake" / "build" / "bin").mkdir(parents=True)
    repl_bin = ws / ".lake" / "build" / "bin" / "repl"
    repl_bin.write_text("", encoding="utf-8")
    project_root = tmp_path / "proj"
    project_root.mkdir()
    (project_root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
    seen: dict[str, object] = {}

    class _Proc:
        stdout = json.dumps({"env": 1, "messages": [], "sorries": []})

    def _fake_run(*args, **kwargs):
        seen["args"] = args[0]
        seen["cwd"] = kwargs.get("cwd")
        return _Proc()

    monkeypatch.setattr(repl_adapter.subprocess, "run", _fake_run)
    out = repl_adapter.verify_with_repl(
        code="theorem t : True := by\n  trivial\n",
        repl_workspace=ws,
        project_root=project_root,
        lake_path="lake",
        timeout=10,
    )
    assert out["pass"] is True
    assert seen["args"] == ["lake", "env", str(repl_bin)]
    assert seen["cwd"] == str(project_root)

