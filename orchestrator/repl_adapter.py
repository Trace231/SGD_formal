"""Native Lean REPL adapter with schema-compatible normalization."""

from __future__ import annotations

import json
import re
import select
import subprocess
import tempfile
import threading
import time
from pathlib import Path
from typing import Any


def _format_message(msg: dict[str, Any], target_label: str | None = None) -> str:
    pos = msg.get("pos") or {}
    line = int(pos.get("line", 0) or 0)
    col = int(pos.get("column", 0) or 0)
    data = str(msg.get("data", "")).strip()
    severity = str(msg.get("severity", "error") or "error").lower()
    level = "warning" if severity == "warning" else "info" if severity == "info" else "error"
    prefix = f"{target_label}:" if target_label else ""
    if line > 0 and col > 0:
        return f"{prefix}{line}:{col}: {level}: {data}"
    if line > 0:
        return f"{prefix}{line}: {level}: {data}"
    return data


_HEADER_LINE_RE = re.compile(r"^\s*(import|open|set_option)\b")


def _extract_header_lines(code: str) -> str:
    """Extract Lean header lines used for environment priming."""
    return "\n".join(ln for ln in code.splitlines() if _HEADER_LINE_RE.match(ln))


def _count_source_sorrys(source_text: str) -> int:
    import re

    block_comment_re = re.compile(r"/-.*?-/", re.DOTALL)
    sorry_re = re.compile(r"\bsorry\b")
    admit_re = re.compile(r"\badmit\b")
    stripped = block_comment_re.sub("", source_text)
    count = 0
    for line in stripped.splitlines():
        code = line.split("--")[0]
        count += len(sorry_re.findall(code))
        count += len(admit_re.findall(code))
    return count


def _count_sorry_declarations(warnings_raw: list[dict[str, Any]]) -> int:
    return sum(
        1
        for warning in warnings_raw
        if "declaration uses 'sorry'" in str(warning.get("data", ""))
    )


def _build_repl_command(
    *,
    repl_workspace: Path,
    lake_path: str,
    project_root: Path | None,
) -> tuple[list[str], Path]:
    workspace = Path(repl_workspace).resolve()
    if not workspace.exists():
        raise RuntimeError(f"repl_workspace_missing: {workspace}")

    if project_root is None:
        return [lake_path, "exe", "repl"], workspace

    execution_root = Path(project_root).resolve()
    if not execution_root.exists():
        raise RuntimeError(f"repl_project_root_missing: {execution_root}")
    if not (
        (execution_root / "lakefile.lean").exists()
        or (execution_root / "lakefile.toml").exists()
    ):
        raise RuntimeError(
            f"repl_project_root_invalid: missing lakefile in {execution_root}"
        )

    repl_binary = workspace / ".lake" / "build" / "bin" / "repl"
    if not repl_binary.exists():
        raise RuntimeError(
            f"repl_binary_missing: {repl_binary} "
            f"(build the REPL workspace at {workspace})"
        )

    return [lake_path, "env", str(repl_binary)], execution_root


def _normalize_repl_output(
    *,
    raw: dict[str, Any],
    source_text: str,
    elapsed: float,
    target_label: str | None = None,
) -> dict[str, Any]:
    messages = raw.get("messages", []) or []
    sorries = raw.get("sorries", []) or []
    errors_raw = [
        m for m in messages if isinstance(m, dict) and str(m.get("severity", "")) == "error"
    ]
    warnings_raw = [
        m for m in messages if isinstance(m, dict) and str(m.get("severity", "")) == "warning"
    ]
    infos_raw = [
        m for m in messages if isinstance(m, dict) and str(m.get("severity", "")) == "info"
    ]

    errors = [_format_message(m, target_label) for m in errors_raw]
    warnings = [_format_message(m, target_label) for m in warnings_raw]
    infos = [_format_message(m, target_label) for m in infos_raw]

    passed = len(errors_raw) == 0
    complete = (
        passed
        and len(sorries) == 0
        and not any(
            "declaration uses 'sorry'" in str(w.get("data", ""))
            or "failed" in str(w.get("data", "")).lower()
            for w in warnings_raw
        )
    )
    source_sorry_count = _count_source_sorrys(source_text)
    sorry_declarations = _count_sorry_declarations(warnings_raw)

    return {
        "pass": passed,
        "complete": complete,
        "sorries": sorries,
        "errors": errors_raw,
        "warnings": warnings_raw,
        "infos": infos_raw,
        "errors_text": errors,
        "warnings_text": warnings,
        "infos_text": infos,
        "verify_time": elapsed,
        "backend_used": "apollo_repl",
        "backend_reason": "repl_success",
        "source_sorry_count": source_sorry_count,
        "sorry_declarations": sorry_declarations,
        "blocked_sorry_count": max(0, source_sorry_count - sorry_declarations),
        "env_id": int(raw.get("env", 0) or 0),
    }


def verify_with_repl(
    *,
    code: str,
    repl_workspace: Path,
    project_root: Path | None,
    lake_path: str,
    timeout: int,
    last_env: int | None = None,
    extra_args: dict[str, Any] | None = None,
    target_label: str | None = None,
) -> dict[str, Any]:
    command_args, cwd = _build_repl_command(
        repl_workspace=repl_workspace,
        lake_path=lake_path,
        project_root=project_root,
    )

    command: dict[str, Any] = {"cmd": code}
    # Important: first request must NOT force env=0 for this REPL protocol.
    # Passing env=0 can produce {"message":"Unknown environment."}.
    if last_env is not None:
        command["env"] = int(last_env)
    if extra_args:
        command.update(extra_args)
    payload = json.dumps(command, ensure_ascii=False)

    start = time.time()
    try:
        with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as temp_file:
            temp_file.write(payload + "\r\n\r\n")
            temp_file.seek(0)
            proc = subprocess.run(
                command_args,
                stdin=temp_file,
                capture_output=True,
                text=True,
                cwd=str(cwd),
                timeout=timeout,
            )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f"repl_timeout: {timeout}s") from exc
    except FileNotFoundError as exc:
        raise RuntimeError(f"repl_binary_missing: {lake_path}") from exc
    except Exception as exc:  # noqa: BLE001
        raise RuntimeError(f"repl_runtime_error: {exc}") from exc

    elapsed = time.time() - start
    stdout = (proc.stdout or "").strip()
    if not stdout:
        raise RuntimeError("repl_protocol_error: empty stdout")
    try:
        raw = json.loads(stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"repl_protocol_error: invalid json: {stdout[:300]}") from exc
    if not isinstance(raw, dict):
        raise RuntimeError("repl_protocol_error: non-object response")
    if "message" in raw and not (raw.get("messages") or raw.get("sorries")):
        raise RuntimeError(f"repl_protocol_error: {raw.get('message')}")

    return _normalize_repl_output(
        raw=raw,
        source_text=code,
        elapsed=elapsed,
        target_label=target_label,
    )


class ReplSession:
    """Persistent REPL session with env chaining."""

    def __init__(
        self,
        repl_workspace: Path,
        lake_path: str,
        timeout: int,
        *,
        project_root: Path | None = None,
    ):
        self._workspace = Path(repl_workspace).resolve()
        if not self._workspace.exists():
            raise RuntimeError(f"repl_workspace_missing: {self._workspace}")
        self._project_root = Path(project_root).resolve() if project_root is not None else None
        self._lake_path = lake_path
        self._timeout = int(timeout)
        self._lock = threading.Lock()
        self._closed = False
        self._header_env_id: int | None = None
        command_args, cwd = _build_repl_command(
            repl_workspace=self._workspace,
            lake_path=self._lake_path,
            project_root=self._project_root,
        )
        try:
            self._proc = subprocess.Popen(
                command_args,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                cwd=str(cwd),
                bufsize=1,
            )
        except FileNotFoundError as exc:
            raise RuntimeError(f"repl_binary_missing: {self._lake_path}") from exc
        except Exception as exc:  # noqa: BLE001
            raise RuntimeError(f"repl_runtime_error: {exc}") from exc
        if self._proc.stdin is None or self._proc.stdout is None:
            raise RuntimeError("repl_session_error: missing stdio pipes")

    @property
    def header_env_id(self) -> int | None:
        return self._header_env_id

    def prime_header(self, header_code: str) -> int:
        raw = self._send_cmd({"cmd": header_code})
        self._header_env_id = int(raw.get("env", 0) or 0)
        return self._header_env_id

    def verify(
        self,
        code: str,
        *,
        env: int | None = None,
        target_label: str | None = None,
    ) -> dict[str, Any]:
        start = time.time()
        command: dict[str, Any] = {"cmd": code}
        if env is not None:
            command["env"] = int(env)
        raw = self._send_cmd(command)
        elapsed = time.time() - start
        return _normalize_repl_output(
            raw=raw,
            source_text=code,
            elapsed=elapsed,
            target_label=target_label,
        )

    def _send_cmd(self, command: dict[str, Any]) -> dict[str, Any]:
        if self._closed:
            raise RuntimeError("repl_session_dead: session is closed")
        payload = json.dumps(command, ensure_ascii=False) + "\r\n\r\n"
        with self._lock:
            try:
                assert self._proc.stdin is not None
                self._proc.stdin.write(payload)
                self._proc.stdin.flush()
            except BrokenPipeError as exc:
                raise RuntimeError("repl_session_dead: broken pipe") from exc
            except Exception as exc:  # noqa: BLE001
                raise RuntimeError(f"repl_session_write_error: {exc}") from exc

            chunks: list[str] = []
            raw: dict[str, Any] | None = None
            deadline = time.time() + self._timeout
            while time.time() < deadline:
                poll = self._proc.poll()
                if poll is not None and poll != 0:
                    stderr = ""
                    if self._proc.stderr is not None:
                        try:
                            stderr = self._proc.stderr.read() or ""
                        except Exception:
                            stderr = ""
                    raise RuntimeError(
                        f"repl_session_dead: exit_code={poll}; stderr={stderr[:300]}"
                    )
                assert self._proc.stdout is not None
                ready, _, _ = select.select([self._proc.stdout], [], [], 0.2)
                if not ready:
                    continue
                line = self._proc.stdout.readline()
                if not line:
                    continue
                chunks.append(line)
                candidate = "".join(chunks).strip()
                if not candidate:
                    continue
                try:
                    raw = json.loads(candidate)
                    break
                except json.JSONDecodeError:
                    continue
            if raw is None:
                raise RuntimeError(f"repl_session_timeout: {self._timeout}s")

        if not isinstance(raw, dict):
            raise RuntimeError("repl_session_protocol_error: non-object response")
        if "message" in raw and not (raw.get("messages") or raw.get("sorries")):
            raise RuntimeError(f"repl_session_protocol_error: {raw.get('message')}")
        return raw

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        try:
            if self._proc.stdin is not None:
                try:
                    self._proc.stdin.close()
                except Exception:
                    pass
            self._proc.terminate()
            self._proc.wait(timeout=2)
        except Exception:
            try:
                self._proc.kill()
            except Exception:
                pass

    def __enter__(self) -> "ReplSession":
        return self

    def __exit__(self, *_args: Any) -> None:
        self.close()

