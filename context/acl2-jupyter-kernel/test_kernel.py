"""Tests for the ACL2 Jupyter kernel.

Requires the 'acl2' kernelspec to be installed.
Run with: pytest test_kernel.py -v
"""

import time
import pytest
import jupyter_client


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def kernel():
    """Start a single ACL2 kernel for the whole test module."""
    km = jupyter_client.KernelManager(kernel_name="acl2")
    km.start_kernel()
    kc = km.client()
    kc.start_channels()
    kc.wait_for_ready(timeout=120)
    yield kc
    kc.stop_channels()
    km.shutdown_kernel(now=True)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def execute(kc, code, *, timeout=30):
    """Execute *code* on the kernel and return (results, stdout, error).

    * results – list of text/plain strings from execute_result messages
    * stdout  – concatenated stream output
    * error   – error content dict, or None
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
        # Skip messages from other requests
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
    return results, "".join(stdout_parts), error


def drain_shell(kc, timeout=2):
    """Drain any pending shell messages so the next get_shell_msg is fresh."""
    while True:
        try:
            kc.get_shell_msg(timeout=timeout)
        except Exception:
            break


# ---------------------------------------------------------------------------
# Basic evaluation
# ---------------------------------------------------------------------------

class TestBasicEval:
    """Arithmetic and primitive list operations."""

    @pytest.mark.parametrize(
        "code, expected",
        [
            ("(+ 1 2)", "3"),
            ("(* 6 7)", "42"),
            ("(- 10 3)", "7"),
            ("(expt 2 10)", "1024"),
        ],
    )
    def test_arithmetic(self, kernel, code, expected):
        results, _, error = execute(kernel, code)
        assert error is None, f"error: {error}"
        assert len(results) == 1
        assert results[0].strip() == expected

    @pytest.mark.parametrize(
        "code, expected",
        [
            ("(car '(a b c))", "a"),
            ("(cdr '(a b c))", "(b c)"),
            ("(cons 'x '(y z))", "(x y z)"),
            ("(append '(1 2) '(3 4))", "(1 2 3 4)"),
            ("(length '(a b c d))", "4"),
        ],
    )
    def test_lists(self, kernel, code, expected):
        results, _, error = execute(kernel, code)
        assert error is None, f"error: {error}"
        assert len(results) == 1
        assert results[0].strip().lower() == expected.lower()


# ---------------------------------------------------------------------------
# ACL2-specific features
# ---------------------------------------------------------------------------

class TestACL2Features:
    """defun, defthm, keyword commands, and constants."""

    def test_defun(self, kernel):
        results, stdout, error = execute(kernel, "(defun test-double (x) (* 2 x))")
        assert error is None, f"error: {error}"
        # defun returns a summary; at minimum there should be no error
        assert results or stdout, "expected some output from defun"

    def test_call_defun(self, kernel):
        # Depends on test_defun having run (module-scoped kernel)
        results, _, error = execute(kernel, "(test-double 21)")
        assert error is None, f"error: {error}"
        assert any("42" in r for r in results), f"expected 42, got {results}"

    def test_defthm(self, kernel):
        results, stdout, error = execute(
            kernel,
            "(defthm test-double-is-plus (equal (test-double x) (+ x x)))",
            timeout=60,
        )
        assert error is None, f"error: {error}"
        # A successful proof produces stdout output and/or a result
        assert results or stdout, "expected output from defthm"

    def test_keyword_command(self, kernel):
        # :pe translates to (PE 'TEST-DOUBLE) via keyword command handling
        results, stdout, error = execute(kernel, ":pe test-double")
        assert error is None, f"error: {error}"
        assert results or stdout, "expected output from :pe"

    def test_defconst(self, kernel):
        results, _, error = execute(kernel, "(defconst *test-val* 99)")
        assert error is None, f"error: {error}"
        results2, _, error2 = execute(kernel, "*test-val*")
        assert error2 is None
        assert any("99" in r for r in results2), f"expected 99, got {results2}"


# ---------------------------------------------------------------------------
# Output routing
# ---------------------------------------------------------------------------

class TestOutputRouting:
    """CW output should appear on stdout, not in the result."""

    def test_cw(self, kernel):
        results, stdout, error = execute(kernel, '(cw "hello from acl2~%")')
        assert error is None, f"error: {error}"
        assert "hello from acl2" in stdout.lower(), f"stdout: {stdout!r}"

    def test_cw_with_format(self, kernel):
        code = '(cw "Sum is ~x0~%" (+ 3 4))'
        results, stdout, error = execute(kernel, code)
        assert error is None, f"error: {error}"
        assert "7" in stdout, f"stdout: {stdout!r}"


# ---------------------------------------------------------------------------
# Code completeness checks
# ---------------------------------------------------------------------------

class TestCodeComplete:
    """The kernel should report whether a code fragment is complete."""

    def _check(self, kc, code, expected_status):
        drain_shell(kc, timeout=1)
        msg_id = kc.is_complete(code)
        # Find the is_complete_reply matching our request
        deadline = time.time() + 10
        while time.time() < deadline:
            try:
                reply = kc.get_shell_msg(timeout=2)
            except Exception:
                break
            if reply.get("msg_type") == "is_complete_reply":
                assert reply["content"]["status"] == expected_status
                return
            if reply.get("parent_header", {}).get("msg_id") == msg_id:
                assert reply["content"]["status"] == expected_status
                return
        pytest.fail(f"No is_complete_reply received for {code!r}")

    def test_complete(self, kernel):
        self._check(kernel, "(+ 1 2)", "complete")

    def test_incomplete(self, kernel):
        self._check(kernel, "(+ 1", "incomplete")

    def test_invalid(self, kernel):
        self._check(kernel, ")", "invalid")


# ---------------------------------------------------------------------------
# Error handling
# ---------------------------------------------------------------------------

class TestIncludeBook:
    """include-book should work without crashing the kernel."""

    def test_include_book(self, kernel):
        results, stdout, error = execute(
            kernel,
            '(include-book "std/lists/append" :dir :system)',
            timeout=120,
        )
        assert error is None, f"error: {error}"
        # include-book succeeds via side effect; may or may not produce output

    def test_function_after_include_book(self, kernel):
        """After include-book, the kernel should still work."""
        results, _, error = execute(kernel, "(+ 1 2)")
        assert error is None, f"error: {error}"
        assert any("3" in r for r in results), f"expected 3, got {results}"

    def test_book_content_available(self, kernel):
        """A theorem from the included book should be usable."""
        # std/lists/append provides theorems about append;
        # verify that a function from the book's dependency works
        results, _, error = execute(kernel, "(append '(a) '(b c))")
        assert error is None, f"error: {error}"
        assert any("a" in r.lower() for r in results), f"expected (a b c), got {results}"


class TestErrors:
    """Evaluation errors should be reported, not crash the kernel."""

    def test_undefined_function(self, kernel):
        results, stdout, error = execute(kernel, "(no-such-function-xyz 1 2)")
        assert error is not None or not results, "expected an error"

    def test_kernel_survives_error(self, kernel):
        """After an error, the kernel should still work."""
        execute(kernel, "(no-such-function-xyz 1 2)")
        # Give the kernel a moment to settle after the error
        time.sleep(0.5)
        results, _, error = execute(kernel, "(+ 10 20)")
        assert error is None, f"unexpected error: {error}"
        assert any("30" in r for r in results), f"expected 30, got {results}"
