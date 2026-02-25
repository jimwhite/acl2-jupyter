#!/usr/bin/env python3
"""Tests for the 'forms' array in cell metadata.

Requires ACL2_JUPYTER_EVENT_FORMS=1 in the kernel install.
When event-forms is enabled, each cell's display_data includes a 'forms'
array of the original ACL2 event forms (the code as submitted), enabling
the .ipynb to serve as a self-contained book.

Usage:
    pytest test_event_forms.py -v
"""

import time
import pytest
import jupyter_client

MIME_TYPE = "application/vnd.acl2.events+json"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def eval_with_metadata(kc, code, timeout=60):
    """Execute code and return (result, stdout, error, acl2_meta).

    Collects IOPub messages.  acl2_meta is the dict from the
    display_data output with our vendor MIME type, or {} if absent.
    """
    msg_id = kc.execute(code)
    results = []
    stdout_parts = []
    error = None
    acl2_meta = {}
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
        elif mt == "display_data":
            data = msg["content"].get("data", {})
            if MIME_TYPE in data:
                acl2_meta = data[MIME_TYPE]
        elif mt == "stream":
            stdout_parts.append(msg["content"]["text"])
        elif mt == "error":
            error = msg["content"]
        elif mt == "status" and msg["content"]["execution_state"] == "idle":
            break
    # Drain shell reply so it doesn't leak into next test
    try:
        kc.get_shell_msg(timeout=10)
    except Exception:
        pass
    result = results[0] if results else None
    return result, "".join(stdout_parts), error, acl2_meta


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
# Tests — Event Forms  (requires ACL2_JUPYTER_EVENT_FORMS=1)
# ---------------------------------------------------------------------------

class TestEventForms:

    def test_defun_has_form(self, kc):
        """A defun should produce a form matching the source code."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun forms-test-fn (x) (+ x 99))")
        assert error is None, f"error: {error}"
        forms = meta.get("forms", [])
        assert len(forms) > 0, f"expected forms, got: {meta}"
        combined = " ".join(forms).lower()
        assert "forms-test-fn" in combined, \
            f"expected function name in forms: {forms}"
        assert "defun" in combined, \
            f"expected 'defun' in forms: {forms}"

    def test_defthm_has_form(self, kc):
        """A defthm should produce a form matching the theorem."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defthm forms-test-thm (equal (cdr (cons x y)) y))")
        assert error is None, f"error: {error}"
        forms = meta.get("forms", [])
        assert len(forms) > 0, f"expected forms, got: {meta}"
        combined = " ".join(forms).lower()
        assert "forms-test-thm" in combined, \
            f"expected theorem name in forms: {forms}"
        assert "defthm" in combined, \
            f"expected 'defthm' in forms: {forms}"

    def test_forms_are_strings(self, kc):
        """Forms should be S-expression strings."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun forms-str-test (x) x)")
        assert error is None, f"error: {error}"
        forms = meta.get("forms", [])
        assert len(forms) > 0, f"no forms"
        for f in forms:
            assert isinstance(f, str), f"form should be string, got: {type(f)}"
            assert len(f) > 0, "empty form string"

    def test_arithmetic_no_forms(self, kc):
        """Plain arithmetic produces no forms (no events = no forms)."""
        _, _, error, meta = eval_with_metadata(kc, "(+ 3 4)")
        assert error is None, f"error: {error}"
        forms = meta.get("forms", [])
        assert len(forms) == 0, f"expected no forms, got: {forms}"

    def test_forms_count_matches_events(self, kc):
        """Number of forms should equal number of events."""
        code = """(defun forms-count-a (x) (+ x 10))
(defun forms-count-b (x) (+ x 20))"""
        _, _, error, meta = eval_with_metadata(kc, code)
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        forms = meta.get("forms", [])
        assert len(events) == len(forms), \
            f"events ({len(events)}) != forms ({len(forms)})"
        assert len(forms) >= 2, f"expected >=2 forms, got {len(forms)}"
