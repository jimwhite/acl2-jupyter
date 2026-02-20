#!/usr/bin/env python3
"""Tests for cell metadata persisted via display_data.

The ACL2 kernel emits a display_data message with MIME type
application/vnd.acl2.events+json after each successful cell execution.
This gets stored in the notebook's output list (standard Jupyter
persistence mechanism).

The payload is:
  {
    "events": ["(DEFUN ...)", ...],   -- event landmark S-expressions
    "package": "ACL2",                -- current ACL2 package
    "forms": ["(defun ...)", ...]     -- original event forms (optional,
                                         requires ACL2_JUPYTER_EVENT_FORMS=1)
  }

Usage:
    pytest test_metadata.py -v --timeout=180
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
# Tests
# ---------------------------------------------------------------------------

class TestMetadata:

    def test_arithmetic_no_events(self, kc):
        """Plain arithmetic doesn't create events."""
        result, stdout, error, meta = eval_with_metadata(kc, "(+ 2 3)")
        assert error is None, f"error: {error}"
        assert result == "5", f"result: {result!r}"
        events = meta.get("events", [])
        assert len(events) == 0, f"expected no events, got: {events}"

    def test_arithmetic_package(self, kc):
        """Package should be ACL2 by default."""
        _, _, error, meta = eval_with_metadata(kc, "(+ 1 1)")
        assert error is None, f"error: {error}"
        assert meta.get("package") == "ACL2", f"meta: {meta}"

    def test_defun_event(self, kc):
        """A defun should produce an event landmark."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun metadata-test-fn (x) (+ x 42))")
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) > 0, f"expected events, got: {meta}"
        # The event S-expression should mention the function name
        combined = " ".join(events)
        assert "METADATA-TEST-FN" in combined.upper(), \
            f"expected function name in events: {events}"

    def test_defthm_event(self, kc):
        """A defthm should produce an event landmark."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defthm metadata-test-thm (equal (car (cons x y)) x))")
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) > 0, f"expected events, got: {meta}"
        combined = " ".join(events)
        assert "METADATA-TEST-THM" in combined.upper(), \
            f"expected theorem name in events: {events}"

    def test_include_book_event(self, kc):
        """An include-book should produce an event landmark."""
        _, _, error, meta = eval_with_metadata(
            kc,
            '(include-book "std/lists/append" :dir :system)',
            timeout=60)
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) > 0, f"expected events for include-book, got: {meta}"

    def test_multiple_forms_events(self, kc):
        """Multiple forms in one cell should produce multiple events."""
        code = """(defun meta-fn-a (x) (+ x 1))
(defun meta-fn-b (x) (+ x 2))"""
        _, _, error, meta = eval_with_metadata(kc, code)
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) >= 2, f"expected >=2 events, got {len(events)}: {events}"

    def test_events_are_strings(self, kc):
        """Events should be S-expression strings (prin1 output)."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun meta-string-test (x) x)")
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) > 0, f"no events"
        for e in events:
            assert isinstance(e, str), f"event should be string, got: {type(e)}"
            # Should look like a Lisp S-expression (starts with paren or symbol)
            assert len(e) > 0, "empty event string"

    def test_display_data_present(self, kc):
        """display_data with vendor MIME type should be emitted."""
        result, _, error, meta = eval_with_metadata(kc, "(+ 10 20)")
        assert error is None, f"error: {error}"
        # meta comes from display_data; should have at least 'package'
        assert "package" in meta, f"no display_data with {MIME_TYPE}: {meta}"
        assert "events" in meta, f"missing events key: {meta}"


class TestEventForms:
    """Tests for the 'forms' array in display_data metadata.

    These tests require ACL2_JUPYTER_EVENT_FORMS=1 in the kernel's
    environment (set in kernel.json via the installer).
    """

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


class TestShallowEvents:
    """Tests for the default shallow-events mode (ACL2_JUPYTER_DEEP_EVENTS=0).

    In shallow mode:
    - Only top-level events (depth=0) are included
    - Absolute event numbers are stripped from the events output
    - include-book produces exactly 1 event (not all sub-events)
    """

    def test_event_no_leading_number(self, kc):
        """Events should not start with a number (number stripped)."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun shallow-num-test (x) (+ x 7))")
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) > 0, f"no events"
        for e in events:
            # In shallow mode, the event string should start with '('
            # followed by the form or type metadata, NOT an integer.
            stripped = e.strip()
            assert stripped.startswith("("), \
                f"event should start with '(': {e!r}"
            # The first token after '(' should NOT be a digit
            inner = stripped[1:].lstrip()
            assert not inner[0].isdigit(), \
                f"event should not have leading number: {e!r}"

    def test_include_book_one_event(self, kc):
        """include-book should produce exactly 1 event (top-level only)."""
        _, _, error, meta = eval_with_metadata(
            kc,
            '(include-book "std/lists/rev" :dir :system)',
            timeout=60)
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        # Should be exactly 1: the include-book landmark itself.
        # In deep mode this would be many (all sub-events from the book).
        assert len(events) == 1, \
            f"expected exactly 1 event for include-book, got {len(events)}: {events}"

    def test_defun_event_contains_form(self, kc):
        """In shallow mode, a standard :program defun event IS the form."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun shallow-form-test (x) (cons x x))")
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        assert len(events) == 1, f"expected 1 event: {events}"
        # For a standard :program defun with depth=0, the compact tuple
        # is (N . form), so stripping the number gives just the form.
        e = events[0].upper()
        assert "DEFUN" in e, f"expected DEFUN in event: {events[0]}"
        assert "SHALLOW-FORM-TEST" in e, f"expected name in event: {events[0]}"
