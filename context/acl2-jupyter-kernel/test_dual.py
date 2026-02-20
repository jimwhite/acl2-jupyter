#!/usr/bin/env python3
"""Dual-fixture tests: Bridge vs Jupyter kernel.

One set of tests, run two ways.  Every test is parameterized over a
"backend" fixture that is either the Bridge or the Jupyter kernel.

Bridge fixture:
  - Starts saved_acl2 with bridge, connects via Unix socket
  - Every eval is wrapped in (bridge::in-main-thread ...)
  - Sends LISP commands, reads RETURN/STDOUT/ERROR

Kernel fixture:
  - Starts the acl2 Jupyter kernel via KernelManager
  - Sends execute_request, reads execute_result/stream/error

Usage:
    pytest test_dual.py -v --timeout=120
"""

import os
import socket
import subprocess
import time
import pytest
import jupyter_client


# ---------------------------------------------------------------------------
# Bridge client
# ---------------------------------------------------------------------------

class BridgeClient:
    """Minimal Bridge client."""

    def __init__(self, sock_path):
        self.sock_path = sock_path
        self.sock = None
        self.buf = b""

    def connect(self, timeout=120):
        deadline = time.time() + timeout
        while time.time() < deadline:
            if os.path.exists(self.sock_path):
                try:
                    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                    s.connect(self.sock_path)
                    s.settimeout(120)
                    self.sock = s
                    msg_type, _ = self._read_message()
                    assert msg_type == "ACL2_BRIDGE_HELLO", f"Expected HELLO, got {msg_type}"
                    msg_type, _ = self._read_message()
                    assert msg_type == "READY", f"Expected READY, got {msg_type}"
                    return
                except (ConnectionRefusedError, FileNotFoundError):
                    pass
            time.sleep(0.5)
        raise RuntimeError(f"Bridge socket {self.sock_path} not available after {timeout}s")

    def _send(self, cmd_type, sexpr):
        content = sexpr
        header = f"{cmd_type} {len(content)}\n"
        self.sock.sendall((header + content + "\n").encode())

    def _read_message(self):
        while b"\n" not in self.buf:
            data = self.sock.recv(4096)
            if not data:
                return None, None
            self.buf += data

        header_end = self.buf.index(b"\n")
        header = self.buf[:header_end].decode()
        self.buf = self.buf[header_end + 1:]

        parts = header.split(" ", 1)
        if len(parts) != 2:
            return header, ""

        msg_type = parts[0]
        content_len = int(parts[1])

        while len(self.buf) < content_len + 1:
            data = self.sock.recv(4096)
            if not data:
                break
            self.buf += data

        content = self.buf[:content_len].decode()
        self.buf = self.buf[content_len + 1:]
        return msg_type, content

    def eval_lisp(self, sexpr, timeout=60):
        """Send sexpr wrapped in (bridge::in-main-thread (ld '(...) ...)).
        The ld wrapper provides LP context (*ld-level* > 0, catch tags)
        so that include-book, defthm, etc. work correctly.
        Returns (result, stdout, error)."""
        # Wrap in ld for LP context — same approach as acl2_jupyter.
        # Without ld, *ld-level* is 0 and throw-raw-ev-fncall calls
        # interface-er instead of throwing cleanly.
        ld_wrapped = (
            f'(bridge::in-main-thread'
            f' (ld \'({sexpr})'
            f' :ld-pre-eval-print nil'
            f' :ld-post-eval-print :command-conventions'
            f' :ld-verbose nil'
            f' :ld-prompt nil'
            f' :ld-error-action :continue'
            f' :current-package "ACL2"))'
        )
        self._send("LISP", ld_wrapped)
        result = None
        stdout_parts = []
        error = None
        deadline = time.time() + timeout
        while time.time() < deadline:
            msg_type, content = self._read_message()
            if msg_type is None:
                break
            if msg_type == "RETURN":
                result = content
                break
            elif msg_type == "STDOUT":
                stdout_parts.append(content)
            elif msg_type == "ERROR":
                error = content
                break
            elif msg_type == "READY":
                break
        # Always consume until READY to keep protocol in sync
        if msg_type not in (None, "READY"):
            while time.time() < deadline:
                msg_type, _ = self._read_message()
                if msg_type is None or msg_type == "READY":
                    break
        return result, "".join(stdout_parts), error

    def close(self):
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass


# ---------------------------------------------------------------------------
# Kernel eval helper
# ---------------------------------------------------------------------------

def kernel_eval(kc, code, timeout=60):
    """Execute code on Jupyter kernel. Returns (result, stdout, error)."""
    msg_id = kc.execute(code)
    results = []
    stdout_parts = []
    error = None
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            msg = kc.get_iopub_msg(timeout=2)
        except Exception:
            break
        parent_id = msg.get("parent_header", {}).get("msg_id")
        if parent_id != msg_id:
            continue
        mt = msg["msg_type"]
        if mt == "execute_result":
            results.append(msg["content"]["data"].get("text/plain", ""))
        elif mt == "stream":
            stdout_parts.append(msg["content"]["text"])
        elif mt == "error":
            error = msg["content"]
        elif mt == "status" and msg["content"]["execution_state"] == "idle":
            break
    result = results[0] if results else None
    return result, "".join(stdout_parts), error


# ---------------------------------------------------------------------------
# Backend wrapper — unified eval interface
# ---------------------------------------------------------------------------

class Backend:
    """Thin wrapper so tests call backend.eval(sexpr) regardless of type."""

    def __init__(self, name, eval_fn):
        self.name = name
        self._eval = eval_fn

    def eval(self, sexpr, timeout=60):
        return self._eval(sexpr, timeout=timeout)

    def __repr__(self):
        return self.name


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def bridge_backend():
    """Start Bridge server, yield a Backend, shut down after."""
    sock_path = "/tmp/test-dual-bridge.sock"
    if os.path.exists(sock_path):
        os.unlink(sock_path)

    bridge_script = f'''(include-book "centaur/bridge/top" :dir :system)
(bridge::start "{sock_path}")
'''
    proc = subprocess.Popen(
        ["/home/acl2/saved_acl2"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    proc.stdin.write(bridge_script.encode())
    proc.stdin.flush()

    client = BridgeClient(sock_path)
    client.connect(timeout=120)

    yield Backend("bridge", client.eval_lisp)

    try:
        client._send("LISP", "(bridge::stop)")
    except Exception:
        pass
    client.close()
    proc.terminate()
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        proc.kill()
    if os.path.exists(sock_path):
        os.unlink(sock_path)


@pytest.fixture(scope="module")
def kernel_backend():
    """Start the ACL2 Jupyter kernel, yield a Backend."""
    km = jupyter_client.KernelManager(kernel_name="acl2")
    km.start_kernel()
    kc = km.client()
    kc.start_channels()
    kc.wait_for_ready(timeout=120)

    yield Backend("kernel", lambda sexpr, timeout=60: kernel_eval(kc, sexpr, timeout=timeout))

    kc.stop_channels()
    km.shutdown_kernel(now=True)


@pytest.fixture(params=["bridge", "kernel"])
def backend(request, bridge_backend, kernel_backend):
    """Parameterized fixture -- each test runs once per backend."""
    if request.param == "bridge":
        return bridge_backend
    return kernel_backend


# ---------------------------------------------------------------------------
# Tests -- one set, run two ways
# ---------------------------------------------------------------------------

class TestDual:

    def test_arithmetic(self, backend):
        result, stdout, error = backend.eval("(+ 1 2)")
        assert error is None, f"error: {error}"
        output = (result or "") + stdout
        assert "3" in output, f"output: {output!r}"

    def test_defun(self, backend):
        name = f"{backend.name}-double"
        result, stdout, error = backend.eval(f"(defun {name} (x) (* 2 x))")
        assert error is None, f"error: {error}"
        output = (result or "") + stdout
        assert len(output) > 0, "expected some output from defun"

    def test_call_defun(self, backend):
        name = f"{backend.name}-double"
        result, stdout, error = backend.eval(f"({name} 21)")
        assert error is None, f"error: {error}"
        output = (result or "") + stdout
        assert "42" in output, f"output: {output!r}"

    def test_cw(self, backend):
        tag = backend.name
        result, stdout, error = backend.eval(f'(cw "hello {tag}~%")')
        assert error is None, f"error: {error}"
        assert f"hello {tag}" in stdout.lower(), f"stdout: {stdout!r}"

    def test_include_book(self, backend):
        result, stdout, error = backend.eval(
            '(include-book "std/lists/append" :dir :system)', timeout=60
        )
        assert error is None, f"error: {error}"

    def test_after_include_book(self, backend):
        result, stdout, error = backend.eval("(+ 100 200)")
        assert error is None, f"error: {error}"
        output = (result or "") + stdout
        assert "300" in output, f"output: {output!r}"

    def test_include_book_apply(self, backend):
        result, stdout, error = backend.eval(
            '(include-book "projects/apply/top" :dir :system)', timeout=60
        )
        assert error is None, f"error: {error}"

    def test_after_include_book_apply(self, backend):
        result, stdout, error = backend.eval("(+ 1 1)")
        assert error is None, f"error: {error}"
        output = (result or "") + stdout
        assert "2" in output, f"output: {output!r}"

    def test_pbt_initial(self, backend):
        """Before any defun in this session, :pbt :max should show
        at least EXIT-BOOT-STRAP-MODE (the base event from boot-strap)
        plus whatever include-books have already run."""
        result, stdout, error = backend.eval(":pbt :max")
        assert error is None, f"error: {error}"
        output = (result or "") + stdout
        # The last event must be something real, not just
        # EXIT-BOOT-STRAP-MODE (event 0) -- prior tests already
        # did include-book and defun.
        assert "INCLUDE-BOOK" in output.upper() or "DEFUN" in output.upper(), \
            f":pbt :max should show prior events, got: {output!r}"

    def test_pbt_after_defun(self, backend):
        """Define a function, then :pbt :max must show it."""
        tag = backend.name
        defun_name = f"pbt-test-{tag}"
        result, stdout, error = backend.eval(
            f"(defun {defun_name} (x) (+ x 1))")
        assert error is None, f"defun error: {error}"
        result2, stdout2, error2 = backend.eval(":pbt :max")
        assert error2 is None, f":pbt error: {error2}"
        output = (result2 or "") + stdout2
        assert defun_name.upper() in output.upper(), \
            f":pbt :max should show {defun_name}, got: {output!r}"

    def test_undo(self, backend):
        """Define a function, undo it with :U, then verify the kernel
        is still in a valid state (no package lock errors)."""
        tag = backend.name
        undo_name = f"undo-test-{tag}"
        # Define
        result, stdout, error = backend.eval(
            f"(defun {undo_name} (x) (+ x 99))")
        assert error is None, f"defun error: {error}"
        # Undo
        result2, stdout2, error2 = backend.eval(":u")
        assert error2 is None, f":u error: {error2}"
        # Verify state is valid -- arithmetic still works
        result3, stdout3, error3 = backend.eval("(+ 10 20)")
        assert error3 is None, f"post-undo eval error: {error3}"
        output = (result3 or "") + stdout3
        assert "30" in output, f"post-undo output: {output!r}"
