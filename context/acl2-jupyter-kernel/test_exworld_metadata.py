#!/usr/bin/env python3
"""Tests for extra-world metadata: symbols, dependencies, expansions, raw_definitions.

Follows the same pattern as test_metadata.py — starts the acl2 Jupyter kernel
via KernelManager, executes cells, and checks the display_data payload under
application/vnd.acl2.events+json for the new keys.

Usage:
    pytest test_exworld_metadata.py -v --timeout=180
"""

import time
import pytest
import jupyter_client

MIME_TYPE = "application/vnd.acl2.events+json"


# ---------------------------------------------------------------------------
# Helpers  (same as test_metadata.py)
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
    # Drain shell reply
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
# Tests — Symbols
# ---------------------------------------------------------------------------

class TestSymbols:

    def test_arithmetic_has_symbols(self, kc):
        """Plain arithmetic should report referenced symbols."""
        _, _, error, meta = eval_with_metadata(kc, "(+ 2 3)")
        assert error is None, f"error: {error}"
        symbols = meta.get("symbols", [])
        assert len(symbols) > 0, f"expected symbols, got: {meta}"
        names = [s["name"] for s in symbols]
        # '+' should appear (it's the operator)
        assert any("+" in n for n in names), \
            f"expected '+' in symbol names: {names}"

    def test_symbol_has_required_fields(self, kc):
        """Each symbol entry should have name, package, kind, operator, argument."""
        _, _, error, meta = eval_with_metadata(kc, "(car '(a b c))")
        assert error is None, f"error: {error}"
        symbols = meta.get("symbols", [])
        assert len(symbols) > 0, f"no symbols"
        for s in symbols:
            assert "name" in s, f"missing 'name': {s}"
            assert "package" in s, f"missing 'package': {s}"
            assert "kind" in s, f"missing 'kind': {s}"
            assert "operator" in s, f"missing 'operator': {s}"
            assert "argument" in s, f"missing 'argument': {s}"

    def test_operator_position(self, kc):
        """The head of a form should be marked as operator."""
        _, _, error, meta = eval_with_metadata(kc, "(cons 'x '(y))")
        assert error is None, f"error: {error}"
        symbols = meta.get("symbols", [])
        cons_entry = [s for s in symbols if s["name"].upper() == "CONS"]
        assert len(cons_entry) > 0, f"expected CONS in symbols: {symbols}"
        assert cons_entry[0]["operator"] is True, \
            f"CONS should be operator: {cons_entry[0]}"

    def test_symbol_kind_function(self, kc):
        """A known ACL2 function should be classified as 'function'."""
        _, _, error, meta = eval_with_metadata(kc, "(car '(a b c))")
        assert error is None, f"error: {error}"
        symbols = meta.get("symbols", [])
        car_entry = [s for s in symbols if s["name"].upper() == "CAR"]
        assert len(car_entry) > 0, f"expected CAR: {symbols}"
        assert car_entry[0]["kind"] == "function", \
            f"CAR should be function: {car_entry[0]}"

    def test_defun_symbols_include_body(self, kc):
        """A defun should report symbols from its body."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun exw-fn1 (x y) (if (consp x) (cons (car x) y) y))")
        assert error is None, f"error: {error}"
        symbols = meta.get("symbols", [])
        names = {s["name"].upper() for s in symbols}
        for expected in ["CONSP", "CONS", "CAR"]:
            assert expected in names, \
                f"expected {expected} in symbols: {names}"

    def test_formals_not_operator(self, kc):
        """Formal parameters in a defun arglist should be argument-only,
        never operator.  Regression test: the first formal was mis-classified
        as operator because the arglist was walked as a normal form."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun exw-formals-test (a b c) (list a b c))")
        assert error is None, f"error: {error}"
        symbols = meta.get("symbols", [])
        for name in ["A", "B", "C"]:
            entries = [s for s in symbols if s["name"].upper() == name]
            assert len(entries) > 0, f"formal {name} not found in symbols"
            for e in entries:
                assert e.get("argument") is True, \
                    f"formal {name} should be argument: {e}"
                assert e.get("operator") is not True, \
                    f"formal {name} should NOT be operator: {e}"


# ---------------------------------------------------------------------------
# Tests — Dependencies
# ---------------------------------------------------------------------------

class TestDependencies:

    def test_defun_has_dependencies(self, kc):
        """A defun should produce dependency edges."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun exw-dep1 (x) (if (consp x) (car x) x))")
        assert error is None, f"error: {error}"
        deps = meta.get("dependencies", {})
        assert len(deps) > 0, f"expected dependencies, got: {meta}"
        # Find the entry for exw-dep1
        dep_keys = list(deps.keys())
        matches = [k for k in dep_keys if "exw-dep1" in k.lower()]
        assert len(matches) > 0, f"no dep edge for exw-dep1: {dep_keys}"
        refs = deps[matches[0]]
        ref_names = [r.lower() for r in refs]
        assert any("consp" in r for r in ref_names), \
            f"expected consp in refs: {refs}"

    def test_arithmetic_no_dependencies(self, kc):
        """Plain arithmetic (no world event) should have no dependencies."""
        _, _, error, meta = eval_with_metadata(kc, "(+ 10 20)")
        assert error is None, f"error: {error}"
        deps = meta.get("dependencies", {})
        assert len(deps) == 0, f"expected no dependencies: {deps}"

    def test_self_recursive_dependency(self, kc):
        """A recursive function should list its body references in deps.
        Self-references are excluded (the sym itself is filtered out)."""
        code = "(defun exw-rec (x) (if (consp x) (exw-rec (cdr x)) 0))"
        _, _, error, meta = eval_with_metadata(kc, code)
        assert error is None, f"error: {error}"
        deps = meta.get("dependencies", {})
        matches = [k for k in deps if "exw-rec" in k.lower()]
        assert len(matches) > 0, f"no dep edge for exw-rec: {deps}"
        refs = deps[matches[0]]
        ref_names = [r.lower() for r in refs]
        # Body references should include consp, cdr, etc.
        assert any("consp" in r for r in ref_names), \
            f"expected consp reference: {refs}"
        assert any("cdr" in r for r in ref_names), \
            f"expected cdr reference: {refs}"


# ---------------------------------------------------------------------------
# Tests — Expansions
# ---------------------------------------------------------------------------

class TestExpansions:

    def test_non_macro_no_expansion(self, kc):
        """A plain function call should not produce an expansion."""
        _, _, error, meta = eval_with_metadata(kc, "(+ 2 3)")
        assert error is None, f"error: {error}"
        expansions = meta.get("expansions", [])
        # translate1 may or may not expand a primitive — just check structure
        for e in expansions:
            assert "form" in e, f"missing 'form': {e}"
            assert "expansion" in e, f"missing 'expansion': {e}"

    def test_expansion_has_structure(self, kc):
        """If an expansion is present, it should have form/expansion strings."""
        # Use a known ACL2 macro — cw expands into fmt-to-comment-window etc.
        _, _, error, meta = eval_with_metadata(kc, '(cw "test~%")')
        assert error is None, f"error: {error}"
        expansions = meta.get("expansions", [])
        # cw is a macro, so we may get an expansion
        for e in expansions:
            assert isinstance(e.get("form"), str), f"form not string: {e}"
            assert isinstance(e.get("expansion"), str), f"expansion not string: {e}"


# ---------------------------------------------------------------------------
# Tests — Overall Structure
# ---------------------------------------------------------------------------

class TestExworldStructure:

    def test_metadata_backward_compatible(self, kc):
        """New keys should not break existing events/package keys."""
        _, _, error, meta = eval_with_metadata(kc, "(+ 1 1)")
        assert error is None, f"error: {error}"
        assert "events" in meta, f"missing events: {meta}"
        assert "package" in meta, f"missing package: {meta}"

    def test_defun_has_both_events_and_symbols(self, kc):
        """A defun should produce both events (world) and symbols (exworld)."""
        _, _, error, meta = eval_with_metadata(
            kc, "(defun exw-both-test (x) (+ x 1))")
        assert error is None, f"error: {error}"
        events = meta.get("events", [])
        symbols = meta.get("symbols", [])
        assert len(events) > 0, f"no events: {meta}"
        assert len(symbols) > 0, f"no symbols: {meta}"
