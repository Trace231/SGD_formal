"""Lean 4 LSP client for querying proof goal state.

Uses the built-in ``lake env lean --server`` language server (JSON-RPC over
stdin/stdout) to query the exact proof goal (``⊢ goal``) and local hypotheses
at any position in a Lean file.

This is more informative than ``lake build`` error output because it returns
the tactic state *before* a tactic fires — enabling Agent3 to understand
exactly what type it must produce before attempting a `have` step.

Typical usage (via tools.py)::

    result = get_lean_goal("Algorithms/SVRGOuterLoop.lean", sorry_line=42)
    # result["goal"]        == "⊢ ∫ ω, ‖process ω - wStar‖^2 ∂P ≤ ρ * ..."
    # result["hypotheses"]  == ["hm : 0 < m", "hL : 0 < L", ...]

Performance note:
    First call elaborates the entire file and all imports; this takes roughly
    the same time as ``lake build`` (~30–60 s for Mathlib-heavy files).
    The result is cached by the LSP server's .olean layer, so subsequent calls
    within the same server session are fast (~1–3 s).
"""

from __future__ import annotations

import json
import queue
import subprocess
import threading
import time
from pathlib import Path
from typing import Any


# ---------------------------------------------------------------------------
# Low-level JSON-RPC / LSP framing
# ---------------------------------------------------------------------------

def _file_uri(path: Path) -> str:
    """Convert an absolute Path to a file:// URI."""
    return "file://" + str(path)


def _read_lsp_message(stream) -> dict | None:
    """Read one JSON-RPC message from *stream* (blocking).

    Returns the parsed dict, or None on EOF / framing error.
    LSP framing: ``Content-Length: N\\r\\n\\r\\n<N bytes of JSON>``
    """
    headers: dict[str, str] = {}
    while True:
        line = stream.readline()
        if not line:
            return None
        line = line.decode("utf-8", errors="replace").rstrip("\r\n")
        if not line:
            break  # blank line separates headers from body
        if ":" in line:
            k, _, v = line.partition(":")
            headers[k.strip().lower()] = v.strip()

    length = int(headers.get("content-length", "0"))
    if length <= 0:
        return None
    body = stream.read(length)
    try:
        return json.loads(body.decode("utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None


def _write_lsp_message(stream, msg: dict) -> None:
    """Write one JSON-RPC message to *stream* with Content-Length framing."""
    body = json.dumps(msg, ensure_ascii=False).encode("utf-8")
    header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
    stream.write(header + body)
    stream.flush()


# ---------------------------------------------------------------------------
# LSP client
# ---------------------------------------------------------------------------

class LeanLSPClient:
    """Synchronous Lean 4 LSP client backed by a reader thread.

    The server process is started in *project_root* so that ``lake env``
    can locate all pre-compiled ``.olean`` dependencies.

    Typical lifecycle::

        client = LeanLSPClient(project_root)
        client.start()
        try:
            uri = client.open_file(abs_file_path)
            ok = client.wait_elaboration(uri, timeout=120)
            resp = client.query_goal(uri, line=41, character=2)
        finally:
            client.close()
    """

    def __init__(self, project_root: Path) -> None:
        self._root = project_root
        self._proc: subprocess.Popen | None = None
        self._reader_thread: threading.Thread | None = None
        # Notifications (no id field) are dropped into the inbox queue
        self._inbox: queue.Queue[dict] = queue.Queue()
        # Responses (id + result/error) are stored here and signaled
        self._responses: dict[int, dict] = {}
        self._response_events: dict[int, threading.Event] = {}
        self._next_id = 1
        self._lock = threading.Lock()
        self._running = False

    # ------------------------------------------------------------------
    # Internal plumbing
    # ------------------------------------------------------------------

    def _next_request_id(self) -> int:
        with self._lock:
            rid = self._next_id
            self._next_id += 1
        return rid

    def _reader_loop(self) -> None:
        """Background thread: read messages from the server's stdout."""
        assert self._proc is not None
        while self._running:
            msg = _read_lsp_message(self._proc.stdout)
            if msg is None:
                break
            if "id" in msg and ("result" in msg or "error" in msg):
                # It's a response to one of our requests.
                rid = msg["id"]
                with self._lock:
                    self._responses[rid] = msg
                    ev = self._response_events.get(rid)
                if ev is not None:
                    ev.set()
            else:
                # Notification (e.g. $/lean/fileProgress, publishDiagnostics).
                self._inbox.put(msg)

    def _send_request(self, method: str, params: Any, timeout: float = 30.0) -> dict:
        """Send a JSON-RPC request and block until the response arrives."""
        rid = self._next_request_id()
        ev = threading.Event()
        with self._lock:
            self._response_events[rid] = ev
        _write_lsp_message(
            self._proc.stdin,
            {"jsonrpc": "2.0", "id": rid, "method": method, "params": params},
        )
        ev.wait(timeout=timeout)
        with self._lock:
            resp = self._responses.pop(rid, None)
            self._response_events.pop(rid, None)
        if resp is None:
            raise TimeoutError(
                f"LSP request '{method}' (id={rid}) timed out after {timeout:.0f}s"
            )
        return resp

    def _send_notification(self, method: str, params: Any) -> None:
        """Send a JSON-RPC notification (no response expected)."""
        _write_lsp_message(
            self._proc.stdin,
            {"jsonrpc": "2.0", "method": method, "params": params},
        )

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def start(self) -> None:
        """Launch ``lake env lean --server`` and complete the LSP handshake."""
        self._proc = subprocess.Popen(
            ["lake", "env", "lean", "--server"],
            cwd=self._root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )
        self._running = True
        self._reader_thread = threading.Thread(
            target=self._reader_loop,
            daemon=True,
            name="lean-lsp-reader",
        )
        self._reader_thread.start()

        # LSP initialize / initialized handshake
        self._send_request(
            "initialize",
            {
                "processId": None,
                "rootUri": _file_uri(self._root),
                "capabilities": {},
                "initializationOptions": {},
            },
            timeout=30.0,
        )
        self._send_notification("initialized", {})

    def open_file(self, file_path: Path) -> str:
        """Open *file_path* in the LSP server and return its URI."""
        content = file_path.read_text(encoding="utf-8")
        uri = _file_uri(file_path.resolve())
        self._send_notification(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": uri,
                    "languageId": "lean4",
                    "version": 1,
                    "text": content,
                }
            },
        )
        return uri

    def wait_elaboration(self, uri: str, timeout: float = 120.0) -> bool:
        """Block until the server finishes elaborating *uri*.

        Returns True when elaboration completes within *timeout* seconds.

        The Lean LSP server emits ``$/lean/fileProgress`` notifications while
        checking a file.  When the ``processing`` list becomes empty the file
        is fully elaborated.
        """
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            try:
                msg = self._inbox.get(timeout=min(remaining, 2.0))
            except queue.Empty:
                continue
            if msg.get("method") == "$/lean/fileProgress":
                params = msg.get("params", {})
                if params.get("textDocument", {}).get("uri") == uri:
                    if params.get("processing") is not None and len(params["processing"]) == 0:
                        return True
        return False

    def query_goal(self, uri: str, line: int, character: int = 2) -> dict:
        """Return the raw LSP response for the goal at (*line*, *character*).

        *line* and *character* are both **0-indexed** (LSP convention).
        ``result`` may be None when no tactic goal exists at that position.
        """
        return self._send_request(
            "$/lean/plainGoal",
            {
                "textDocument": {"uri": uri},
                "position": {"line": line, "character": character},
            },
            timeout=15.0,
        )

    def close(self) -> None:
        """Shutdown the server gracefully."""
        if self._proc is None:
            return
        try:
            self._send_request("shutdown", None, timeout=10.0)
            self._send_notification("exit", None)
        except Exception:  # noqa: BLE001
            pass
        finally:
            self._running = False
            try:
                self._proc.stdin.close()
            except OSError:
                pass
            try:
                self._proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self._proc.kill()
            self._proc = None


# ---------------------------------------------------------------------------
# One-shot public entry point
# ---------------------------------------------------------------------------

def query_goal_at_sorry(
    project_root: Path,
    file_path: Path,
    sorry_line: int,
    timeout: int = 120,
) -> dict[str, Any]:
    """One-shot goal query: start server, open file, wait, query, close.

    Args:
        project_root: Lean project root (where ``lakefile.lean`` lives).
        file_path:    **Absolute** path to the ``.lean`` file to inspect.
        sorry_line:   **1-indexed** line number of the ``sorry`` to query.
        timeout:      Maximum seconds to wait for file elaboration.

    Returns a dict with keys::

        {
            "goal":       str | None,   # "⊢ ..." rendered goal
            "hypotheses": list[str],    # local hypotheses, each "name : Type"
            "raw":        str,          # full rendered tactic state from LSP
            "error":      str | None,   # error message if something failed
            "elapsed_s":  float,        # wall-clock seconds
        }
    """
    t0 = time.monotonic()
    client = LeanLSPClient(project_root)
    try:
        client.start()
        uri = client.open_file(file_path)

        elaborated = client.wait_elaboration(uri, timeout=float(timeout))
        if not elaborated:
            return {
                "goal": None,
                "hypotheses": [],
                "raw": "",
                "error": f"Elaboration timed out after {timeout}s. "
                         "The file may have import errors or Mathlib is still loading.",
                "elapsed_s": time.monotonic() - t0,
            }

        # LSP uses 0-indexed lines; sorry_line is 1-indexed.
        # Try character=2 first (typical `sorry` is indented); fall back to 0.
        resp = client.query_goal(uri, line=sorry_line - 1, character=2)
        result = resp.get("result")
        if result is None:
            resp = client.query_goal(uri, line=sorry_line - 1, character=0)
            result = resp.get("result")

        if result is None:
            return {
                "goal": None,
                "hypotheses": [],
                "raw": "",
                "error": (
                    f"No tactic goal found at line {sorry_line}. "
                    "The sorry may be on a different line, or the position is "
                    "not inside a tactic block."
                ),
                "elapsed_s": time.monotonic() - t0,
            }

        rendered: str = result.get("rendered", "")

        # Parse the rendered tactic state.
        # Lean LSP renders the state as:
        #   hyp1 : T1
        #   hyp2 : T2
        #   ⊢ goal_type
        # Lines before "⊢" are hypotheses; the "⊢" line is the goal.
        lines = rendered.splitlines()
        goal_line: str | None = None
        hypotheses: list[str] = []
        for ln in lines:
            stripped = ln.strip()
            if stripped.startswith("⊢"):
                goal_line = stripped
            elif stripped and goal_line is None:
                hypotheses.append(stripped)

        return {
            "goal": goal_line,
            "hypotheses": hypotheses,
            "raw": rendered,
            "error": None,
            "elapsed_s": time.monotonic() - t0,
        }

    except Exception as exc:  # noqa: BLE001
        return {
            "goal": None,
            "hypotheses": [],
            "raw": "",
            "error": str(exc),
            "elapsed_s": time.monotonic() - t0,
        }
    finally:
        client.close()
