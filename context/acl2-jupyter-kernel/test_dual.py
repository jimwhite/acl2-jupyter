#!/usr/bin/env python3
"""Dual-fixture tests: Bridge vs Jupyter kernel.

Each test runs the same ACL2 eval through both the Bridge and the Jupyter
kernel. This ensures the kernel behaves identically to the Bridge.

Bridge fixture:
  - Starts saved_acl2 with bridge, connects via Unix socket
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
# Bridge fixture
# ---------------------------------------------------------------------------

class BridgeClient:
    """Minimal Bridge client matching test_bridge_include_book.py."""

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
                    # Read HELLO
                    msg_type, _ = self._read_message()
                    assert msg_type == "ACL2_BRIDGE_HELLO", f"Expected HELLO, got {msg_type}"
                    # Read READY
                    msg_type, _ = self._read_message()
                    assert msg_type == "READY", f"Expected READY, got {msg_type}"
                    return
                except (ConnectionRefusedError, FileNotFoundError):
                    pass
            time.sleep(0.5)
        raise RuntimeError(f"Bridge socket {self.sock_path} not available after {timeout}s")

    def send(self, cmd_type, sexpr):
        content = sexpr
        header = f"{cmd_type} {len(content)}\n"
        self.sock.sendall((header + content + "\n").encode())

    def _read_message(self):
        # Read header line
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
        self.buf = self.buf[content_len + 1:]  # skip trailing newline
        return msg_type, content

    def eval_lisp(self, sexpr, timeout=60):
        """Send a LISP command, collect results. Returns (result, stdout, error)."""
        self.send("LISP", sexpr)
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
        # After RETURN, read the next READY
        if result is not None:
            msg_type, _ = self._read_message()
            # should be READY
        return result, "".join(stdout_parts), error

    def close(self):
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass


@pytest.fixture(scope="module")
def bridge():
    """Start Bridge server, yield a BridgeClient, shut down after."""
    sock_path = "/tmp/test-dual-bridge.sock"
    # Clean up stale socket
    if os.path.exists(sock_path):
        os.unlink(sock_path)

    # Start Bridge via saved_acl2
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

    yield client

    # Shutdown
    try:
        client.send("LISP", "(bridge::stop)")
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


# ---------------------------------------------------------------------------
# Kernel fixture
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def kernel():
    """Start the ACL2 Jupyter kernel, yield a client."""
    km = jupyter_client.KernelManager(kernel_name="acl2")
    km.start_kernel()
    kc = km.client()
    kc.start_channels()
    kc.wait_for_ready(timeout=120)
    yield kc
    kc.stop_channels()
    km.shutdown_kernel(now=True)


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
# Tests — Bridge
# ---------------------------------------------------------------------------

class TestBridge:
    """Run evals through Bridge to establish baseline."""

    def test_arithmetic(self, bridge):
        result, _, error = bridge.eval_lisp("(+ 1 2)")
        assert error is None, f"error: {error}"
        assert result is not None
        assert "3" in result

    def test_defun(self, bridge):
        result, stdout, error = bridge.eval_lisp("(defun bridge-double (x) (* 2 x))")
        assert error is None, f"error: {error}"
        assert result is not None or stdout

    def test_call_defun(self, bridge):
        result, _, error = bridge.eval_lisp("(bridge-double 21)")
        assert error is None, f"error: {error}"
        assert "42" in result

    def test_cw(self, bridge):
        result, stdout, error = bridge.eval_lisp('(cw "hello bridge~%")')
        assert error is None, f"error: {error}"
        assert "hello bridge" in stdout.lower(), f"stdout: {stdout!r}"

    def test_include_book(self, bridge):
        result, stdout, error = bridge.eval_lisp(
            '(include-book "std/lists/append" :dir :system)', timeout=120
        )
        assert error is None, f"error: {error}"

    def test_after_include_book(self, bridge):
        result, _, error = bridge.eval_lisp("(+ 100 200)")
        assert error is None, f"error: {error}"
        assert "300" in result


# ---------------------------------------------------------------------------
# Tests — Kernel
# ---------------------------------------------------------------------------

class TestKernel:
    """Run the same evals through the Jupyter kernel."""

    def test_arithmetic(self, kernel):
        result, _, error = kernel_eval(kernel, "(+ 1 2)")
        assert error is None, f"error: {error}"
        assert result is not None
        assert "3" in result

    def test_defun(self, kernel):
        result, stdout, error = kernel_eval(kernel, "(defun kernel-double (x) (* 2 x))")
        assert error is None, f"error: {error}"
        assert result is not None or stdout

    def test_call_defun(self, kernel):
        result, _, error = kernel_eval(kernel, "(kernel-double 21)")
        assert error is None, f"error: {error}"
        assert "42" in result

    def test_cw(self, kernel):
        result, stdout, error = kernel_eval(kernel, '(cw "hello kernel~%")')
        assert error is None, f"error: {error}"
        assert "hello kernel" in stdout.lower(), f"stdout: {stdout!r}"

    def test_include_book(self, kernel):
        result, stdout, error = kernel_eval(
            kernel, '(include-book "std/lists/append" :dir :system)', timeout=120
        )
        assert error is None, f"error: {error}"

    def test_after_include_book(self, kernel):
        result, _, error = kernel_eval(kernel, "(+ 100 200)")
        assert error is None, f"error: {error}"
        assert result is not None
        assert "300" in result
