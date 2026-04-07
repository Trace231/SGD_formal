"""Native Lean REPL adapter with schema-compatible normalization.

Two verification modes are provided:

``verify_with_repl``
    One-shot subprocess (``subprocess.run``).  Each call spawns a fresh REPL
    process, writes the full snippet, waits for the process to exit, then
    parses stdout.  Robust against hangs because the OS reaps the process
    once it finishes; any hang is caught by the ``timeout`` parameter which
    triggers ``subprocess.TimeoutExpired``.

``ReplSession``
    Persistent REPL process (``subprocess.Popen``).  The process is kept
    alive for the duration of the session so the Mathlib import environment
    is only elaborated once (``prime_header``).  Subsequent ``verify`` calls
    reuse the cached env_id.

    **Critical implementation detail — binary IO (text=False, bufsize=0)**:
    The Lean REPL returns multi-line JSON responses.  When ``subprocess.Popen``
    is opened with ``text=True`` and ``bufsize=1`` (line-buffered), Python's
    ``TextIOWrapper.readline()`` reads a full OS-pipe chunk into an internal
    buffer on the first call.  Subsequent ``select.select()`` calls on the
    same file descriptor then see an empty OS pipe (the bytes are in Python's
    buffer), so they never fire — causing an infinite hang.

    Fix: open the process in binary, unbuffered mode (``text=False``,
    ``bufsize=0``) and read directly from the raw file descriptor via
    ``os.read(fd, 8192)``.  This bypasses Python's TextIO layer entirely,
    so ``select.select`` and ``os.read`` always operate on the real OS pipe
    state.
"""

from __future__ import annotations

import json
import os
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
    import re as _re

    block_comment_re = _re.compile(r"/-.*?-/", _re.DOTALL)
    sorry_re = _re.compile(r"\bsorry\b")
    admit_re = _re.compile(r"\badmit\b")
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
    """One-shot REPL verification via ``subprocess.run``.

    Spawns a fresh REPL process for each call.  The process exits once it
    has processed the single command, so there are no hanging persistent
    processes.  ``subprocess.TimeoutExpired`` is caught and re-raised as
    ``RuntimeError("repl_timeout: ...")``.
    """
    command_args, cwd = _build_repl_command(
        repl_workspace=repl_workspace,
        lake_path=lake_path,
        project_root=project_root,
    )

    command: dict[str, Any] = {"cmd": code}
    if last_env is not None:
        command["env"] = int(last_env)
    if extra_args:
        command.update(extra_args)
    payload = json.dumps(command, ensure_ascii=False)

    run_timeout = None if int(timeout) <= 0 else int(timeout)
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
                timeout=run_timeout,
            )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f"repl_timeout: {run_timeout}s") from exc
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
    """Persistent REPL session with env chaining.

    Opens the REPL subprocess in **binary, unbuffered mode** (``text=False``,
    ``bufsize=0``) to avoid Python's TextIOWrapper buffering issue.  All I/O
    with the subprocess is done via raw file descriptors (``os.read`` /
    ``os.write`` patterns) so that ``select.select`` always reflects true OS
    pipe state.
    """

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
                # Use binary mode (text=False) + unbuffered (bufsize=0).
                # text=True with bufsize=1 caused a critical bug: Python's
                # TextIOWrapper.readline() reads the full OS-pipe chunk into an
                # internal buffer, making subsequent select.select() calls
                # report "not ready" even though the remaining response bytes
                # are sitting in Python's buffer.  With binary/unbuffered mode
                # we use os.read() + select.select() on the raw fd, avoiding
                # this mismatch entirely.
                text=False,
                bufsize=0,
                cwd=str(cwd),
                start_new_session=True,  # own process group → kill all lake children together
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
        timeout: int | None = None,
    ) -> dict[str, Any]:
        """Send *code* to the persistent REPL and return normalised output.

        Parameters
        ----------
        code:          Lean snippet to verify.
        env:           Optional env_id to chain from (pass ``header_env_id``
                       from ``prime_header`` for tactic verification).
        target_label:  Optional prefix for formatted error messages.
        timeout:       Override the session-level timeout for this call.
                       Useful for short no-op commands or complex tactics.
        """
        start = time.time()
        command: dict[str, Any] = {"cmd": code}
        if env is not None:
            command["env"] = int(env)
        raw = self._send_cmd(command, timeout=timeout)
        elapsed = time.time() - start
        return _normalize_repl_output(
            raw=raw,
            source_text=code,
            elapsed=elapsed,
            target_label=target_label,
        )

    def _send_cmd(
        self,
        command: dict[str, Any],
        timeout: int | None = None,
    ) -> dict[str, Any]:
        """Send *command* JSON to the REPL and read the response.

        Uses raw file-descriptor I/O (``os.read``) to bypass Python's
        TextIOWrapper buffering — see module docstring for the full
        explanation.
        """
        if self._closed:
            raise RuntimeError("repl_session_dead: session is closed")

        # Payload is bytes because the process is opened in binary mode.
        payload = (json.dumps(command, ensure_ascii=False) + "\r\n\r\n").encode("utf-8")
        effective_timeout = timeout if timeout is not None else self._timeout

        with self._lock:
            try:
                assert self._proc.stdin is not None
                self._proc.stdin.write(payload)
                self._proc.stdin.flush()
            except BrokenPipeError as exc:
                raise RuntimeError("repl_session_dead: broken pipe") from exc
            except Exception as exc:  # noqa: BLE001
                raise RuntimeError(f"repl_session_write_error: {exc}") from exc

            # Use raw file-descriptor reads via os.read() rather than
            # TextIOWrapper.readline().  Python's TextIO buffer reads a chunk
            # from the OS pipe on the first readline() call (all bytes up to
            # its buffer size), so subsequent select.select() calls on the
            # same fd see an empty OS pipe and never fire — even though the
            # remaining response lines are sitting in Python's internal buffer.
            # Using os.read() on the raw fd bypasses that layer entirely.
            assert self._proc.stdout is not None
            stdout_fd = self._proc.stdout.fileno()
            buf = b""
            raw: dict[str, Any] | None = None
            deadline = time.time() + effective_timeout

            while time.time() < deadline:
                poll = self._proc.poll()
                if poll is not None and poll != 0:
                    stderr_text = ""
                    if self._proc.stderr is not None:
                        try:
                            stderr_bytes = b""
                            while True:
                                ready_e, _, _ = select.select(
                                    [self._proc.stderr], [], [], 0
                                )
                                if not ready_e:
                                    break
                                chunk = os.read(self._proc.stderr.fileno(), 4096)
                                if not chunk:
                                    break
                                stderr_bytes += chunk
                            stderr_text = stderr_bytes.decode("utf-8", errors="replace")
                        except Exception:  # noqa: BLE001
                            pass
                    raise RuntimeError(
                        f"repl_session_dead: exit_code={poll}; stderr={stderr_text[:300]}"
                    )

                ready, _, _ = select.select([stdout_fd], [], [], 0.2)
                if not ready:
                    continue
                try:
                    chunk = os.read(stdout_fd, 8192)
                except OSError:
                    continue
                if not chunk:
                    continue
                buf += chunk
                candidate = buf.decode("utf-8", errors="replace").strip()
                if not candidate:
                    continue
                try:
                    raw = json.loads(candidate)
                    break
                except json.JSONDecodeError:
                    continue

            if raw is None:
                raise RuntimeError(f"repl_session_timeout: {effective_timeout}s")

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
