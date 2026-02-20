#!/usr/bin/env python3
"""Tests for cell metadata (events + package) in execute_reply.

Kernel-only tests — Bridge doesn't have execute_reply metadata.
Each execute_reply carries metadata with:
  - "events": array of S-expression strings (event landmarks from world diff)
  - "package": current ACL2 package name after eval

Usage:
    pytest test_metadata.py -v --timeout=180
"""

import time
import pytest
import jupyter_client


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def eval_with_metadata(kc, code, timeout=60):
    """Execute code and return (result, stdout, error, metadata).

    Collects IOPub messages for result/stdout/error, then reads the
    shell reply for metadata.
    """
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
        parent = msg.get("parent_header", {}).get("msg_id")
        if parent != msg_id:
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
    # Shell reply carries metadata
    metadata = {}
    try:
        reply = kc.get_shell_msg(timeout=10)
        if reply.get("parent_header", {}).get("msg_id") == msg_id:
            metadata = reply.get("metadata", {})
    except Exception:
        pass
    result = results[0] if results else None
    return result, "".join(stdout_parts), error, metadata


# ---------------------------------------------------------------------------
# Fixture
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def kc():
    """Start ACL2 Jupyter kernel, yield KernelClient, shut down after."""
    km = jupyter_client.KernelManager(kernel_name="acl2")
    km.start_kernel()
    client = km.client()
    client.start_channels()
    client.wait_for_ready(timeout=120)
    yield client
    client.stop_channels()
    km.shutdown_kernel(now=True)


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestMetadata:

    def test_arithmetic_no_events(self, kc):
        """Plain arithmetic doesn't create events."""
        result, stdout, error, metadata = eval_with_metadata(kc, "(+ 2 3)")
        assert error is None, f"error: {error}"
        assert result == "5", f"result: {result!r}"
        events = metadata.get("events", [])
        assert len(events) == 0, f"expected no events, got: {events}"

    def test_arithmetic_package(self, kc):
        """Package should be ACL2 by default."""
        _, _, error, metadata = eval_with_metadata(kc, "(+ 1 1)")
        assert error is None, f"error: {error}"
        assert metadata.get("package") == "ACL2", f"metadata: {metadata}"

    def test_defun_event(self, kc):
        """A defun should produce an event landmark."""
        _, _, error, metadata = eval_with_metadata(
            kc, "(defun metadata-test-fn (x) (+ x 42))")
        assert error is None, f"error: {error}"
        events = metadata.get("events", [])
        assert len(events) > 0, f"expected events, got: {metadata}"
        # The event S-expression should mention the function name
        combined = " ".join(events)
        assert "METADATA-TEST-FN" in combined.upper(), \
            f"expected function name in events: {events}"

    def test_defthm_event(self, kc):
        """A defthm should produce an event landmark."""
        _, _, error, metadata = eval_with_metadata(
            kc, "(defthm metadata-test-thm (equal (car (cons x y)) x))")
        assert error is None, f"error: {error}"
        events = metadata.get("events", [])
        assert len(events) > 0, f"expected events, got: {metadata}"
        combined = " ".join(events)
        assert "METADATA-TEST-THM" in combined.upper(), \
            f"expected theorem name in events: {events}"

    def test_include_book_event(self, kc):
        """An include-book should produce an event landmark."""
        _, _, error, metadata = eval_with_metadata(
            kc,
            '(include-book "std/lists/append" :dir :system)',
            timeout=60)
        assert error is None, f"error: {error}"
        events = metadata.get("events", [])
        assert len(events) > 0, f"expected events for include-book, got: {metadata}"

    def test_multiple_forms_events(self, kc):
        """Multiple forms in one cell should produce multiple events."""
        code = """(defun meta-fn-a (x) (+ x 1))
(defun meta-fn-b (x) (+ x 2))"""
        _, _, error, metadata = eval_with_metadata(kc, code)
        assert error is None, f"error: {error}"
        events = metadata.get("events", [])
        assert len(events) >= 2, f"expected >=2 events, got {len(events)}: {events}"

    def test_events_are_strings(self, kc):
        """Events should be S-expression strings (prin1 output)."""
        _, _, error, metadata = eval_with_metadata(
            kc, "(defun meta-string-test (x) x)")
        assert error is None, f"error: {error}"
        events = metadata.get("events", [])
        assert len(events) > 0, f"no events"
        for e in events:
            assert isinstance(e, str), f"event should be string, got: {type(e)}"
            # Should look like a Lisp S-expression (starts with paren or symbol)
            assert len(e) > 0, "empty event string"
