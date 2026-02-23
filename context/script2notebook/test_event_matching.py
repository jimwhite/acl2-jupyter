#!/usr/bin/env python3
"""Test the event-to-cell matching algorithm across all boot-strap files.

Usage:
    python test_event_matching.py [/home/acl2]
"""

import json
import sys
from pathlib import Path

import pytest

from event_matching import (
    extract_cell_name,
    extract_event_name,
    match_events_to_cells,
    summarize_matching,
)


@pytest.fixture
def source_root():
    """Provide the ACL2 source root for integration tests."""
    root = Path("/home/acl2")
    if not (root / ".boot-metadata" / "manifest.json").exists():
        pytest.skip("No boot-metadata available")
    return root


def test_extract_event_name():
    """Verify event name extraction on known tuple formats."""
    cases = [
        ("(DEFUN FOO (X) X)", "FOO"),
        ("(DEFMACRO BAR (X) X)", "BAR"),
        ("(DEFCONST *C* 42)", "*C*"),
        ("(MUTUAL-RECURSION (DEFUN A ...) (DEFUN B ...))", "MUTUAL-RECURSION"),
        # Tuple-prefix: short form
        ("((TABLE) FOO-TABLE ...)", "FOO-TABLE"),
        # Tuple-prefix: long form — name is SECOND token after prefix
        ("(((DEFUN . T) TO-DF . :COMMON-LISP-COMPLIANT) DEFUN TO-DF (X) ...)", "TO-DF"),
        ("(((DEFUN . T) WEAK-BDDNOTE-P . :CLC) DEFUN WEAK-BDDNOTE-P (X) ...)", "WEAK-BDDNOTE-P"),
        ("(((DEFUN . T) DFP . :CLC) DEFUN DFP (X) ...)", "DFP"),
        ("((DEFATTACH NIL) FOO BAR)", "FOO"),
        # Encapsulate
        ("(((ENCAPSULATE . T) 0) ENCAPSULATE NIL (LOGIC) ...)", "ENCAPSULATE"),
    ]
    failures = 0
    for event_str, expected in cases:
        got = extract_event_name(event_str)
        if got != expected:
            print(f"  FAIL extract_event_name({event_str!r})")
            print(f"    expected {expected!r}, got {got!r}")
            failures += 1
    print(f"extract_event_name: {len(cases) - failures}/{len(cases)} passed")
    return failures


def test_extract_cell_name():
    """Verify cell name extraction on known source formats."""
    cases = [
        ("(defun foo (x) x)", "FOO"),
        ("(defmacro bar (x) x)", "BAR"),
        ("(defconst *c* 42)", "*C*"),
        ("(mutual-recursion\n (defun a ...) (defun b ...))", "MUTUAL-RECURSION"),
        ("(in-package \"ACL2\")", "\"ACL2\""),
        ("; comment only", None),
        ("#+acl2-loop-only\n(defmacro set-ruler-extenders (x) ...)", "SET-RULER-EXTENDERS"),
        ("#-acl2-loop-only\n(defmacro set-ruler-extenders (x) ...)", "SET-RULER-EXTENDERS"),
        ("*acl2-system-documentation*", "*ACL2-SYSTEM-DOCUMENTATION*"),
        # Package-prefixed source
        ("(acl2::defconst acl2::*common-lisp-syms*)", "*COMMON-LISP-SYMS*"),
        # Encapsulate cell
        ("(encapsulate () (logic))", "ENCAPSULATE"),
    ]
    failures = 0
    for src, expected in cases:
        got = extract_cell_name(src)
        if got != expected:
            print(f"  FAIL extract_cell_name({src[:50]!r}...)")
            print(f"    expected {expected!r}, got {got!r}")
            failures += 1
    print(f"extract_cell_name: {len(cases) - failures}/{len(cases)} passed")
    return failures


def test_forms_passthrough():
    """Verify that match_events_to_cells distributes forms parallel to events."""
    # Events in world order (newest first) — reversed inside the function.
    events = [
        "(DEFUN BAR (X) X)",
        "(DEFUN FOO (X) X)",
    ]
    forms = [
        "(defun bar (x) x)",
        "(defun foo (x) x)",
    ]
    cells = [
        {"source": "(defun foo (x)\n  x)", "cell_type": "code"},
        {"source": "(defun bar (x)\n  x)", "cell_type": "code"},
    ]

    # Without forms — returns just event assignments.
    result = match_events_to_cells(events, cells)
    assert isinstance(result, list), f"expected list, got {type(result)}"
    assert len(result) == 2
    assert result[0] == ["(DEFUN FOO (X) X)"], f"cell 0: {result[0]}"
    assert result[1] == ["(DEFUN BAR (X) X)"], f"cell 1: {result[1]}"

    # With forms — returns (event_assignments, form_assignments).
    evt_a, frm_a = match_events_to_cells(events, cells, forms=forms)
    assert len(evt_a) == 2
    assert len(frm_a) == 2
    assert evt_a[0] == ["(DEFUN FOO (X) X)"], f"cell 0 events: {evt_a[0]}"
    assert frm_a[0] == ["(defun foo (x) x)"], f"cell 0 forms: {frm_a[0]}"
    assert evt_a[1] == ["(DEFUN BAR (X) X)"], f"cell 1 events: {evt_a[1]}"
    assert frm_a[1] == ["(defun bar (x) x)"], f"cell 1 forms: {frm_a[1]}"

    print("forms_passthrough: PASSED")
    return 0


def test_forms_with_macro_expansion():
    """Forms should follow events when sub-events attach to parent cell."""
    # World order (newest first): macro-generated SUB after PARENT, then PREV.
    events = [
        "(DEFUN SUB (X) X)",
        "(DEFUN PARENT (X) X)",
        "(DEFUN PREV (X) X)",
    ]
    forms = [
        "(defun sub (x) x)",
        "(defun parent (x) x)",
        "(defun prev (x) x)",
    ]
    # Only PREV and PARENT have matching cells; SUB is a macro sub-event
    # that should attach to PARENT's cell.
    cells = [
        {"source": "(defun prev (x) x)", "cell_type": "code"},
        {"source": "(defmacro parent (x) x)", "cell_type": "code"},
    ]

    evt_a, frm_a = match_events_to_cells(events, cells, forms=forms)
    # PREV → cell 0
    assert evt_a[0] == ["(DEFUN PREV (X) X)"], f"cell 0 events: {evt_a[0]}"
    assert frm_a[0] == ["(defun prev (x) x)"], f"cell 0 forms: {frm_a[0]}"
    # PARENT + SUB → cell 1
    assert len(evt_a[1]) == 2, f"cell 1 should have 2 events: {evt_a[1]}"
    assert evt_a[1][0] == "(DEFUN PARENT (X) X)"
    assert evt_a[1][1] == "(DEFUN SUB (X) X)"
    assert frm_a[1][0] == "(defun parent (x) x)"
    assert frm_a[1][1] == "(defun sub (x) x)"

    print("forms_with_macro_expansion: PASSED")
    return 0


def test_forms_empty_cells():
    """Cells with no matching events get empty forms lists too."""
    events = ["(DEFUN B (X) X)"]
    forms = ["(defun b (x) x)"]
    cells = [
        {"source": "; comment cell", "cell_type": "code"},
        {"source": "(defun b (x) x)", "cell_type": "code"},
        {"source": "(+ 1 2)", "cell_type": "code"},
    ]

    evt_a, frm_a = match_events_to_cells(events, cells, forms=forms)
    assert evt_a[0] == [], f"cell 0 events: {evt_a[0]}"
    assert frm_a[0] == [], f"cell 0 forms: {frm_a[0]}"
    assert evt_a[1] == ["(DEFUN B (X) X)"]
    assert frm_a[1] == ["(defun b (x) x)"]
    assert evt_a[2] == []
    assert frm_a[2] == []

    print("forms_empty_cells: PASSED")
    return 0


def test_matching_all_files(source_root: Path):
    """Run matching across all boot-strap files and report results."""
    meta_dir = source_root / ".boot-metadata"
    manifest_path = meta_dir / "manifest.json"
    if not manifest_path.exists():
        print(f"No manifest at {manifest_path}")
        return 1

    manifest = json.load(open(manifest_path))
    results = summarize_matching(source_root, manifest)

    total = results["total_events"]
    assigned = results["total_assigned"]
    rate = (assigned / total * 100) if total else 0
    print(f"\nOverall: {assigned}/{total} events assigned ({rate:.1f}%)")

    problems = [f for f in results["files"] if f["unassigned"] > 0]
    if problems:
        print(f"\nFiles with unassigned events ({len(problems)}):")
        for f in problems:
            print(f"  {f['key']}: {f['unassigned']}/{f['events']} unassigned")
    else:
        print("\nAll events assigned!")

    return len(problems)


def _matching_detail(source_root: Path, key: str):
    """Show detailed matching for one file to debug mismatches."""
    meta_dir = source_root / ".boot-metadata"
    meta = json.load(open(meta_dir / f"{key}.json"))
    events = meta.get("events", [])
    stem = meta["stem"]

    nb = json.load(open(source_root / f"{stem}.ipynb"))
    code_cells = [
        c for c in nb["cells"]
        if c["cell_type"] == "code"
        and not c.get("metadata", {}).get("provenance", {}).get("boot_strap")
    ]

    rev_events = list(reversed(events))

    print(f"\n=== {key} ===")
    print(f"Events: {len(events)}, Code cells: {len(code_cells)}")

    assignments = match_events_to_cells(events, code_cells)
    assigned = sum(len(a) for a in assignments)
    print(f"Assigned: {assigned}/{len(events)}")

    # Show first few cells with their assignments
    print(f"\nFirst 15 cells:")
    for ci in range(min(15, len(code_cells))):
        c = code_cells[ci]
        src = "".join(c["source"]) if isinstance(c["source"], list) else c["source"]
        cname = extract_cell_name(src)
        n_assigned = len(assignments[ci])
        first_line = src.strip().split("\n")[0][:70]
        marker = f"[{n_assigned} events]" if n_assigned else "[no events]"
        print(f"  C{ci}: {marker} name={cname!s:25s} {first_line}")
        if n_assigned:
            for ei, ev in enumerate(assignments[ci][:3]):
                ename = extract_event_name(ev)
                print(f"       E{ei}: name={ename!s:25s} {ev[:60]}")
            if n_assigned > 3:
                print(f"       ... and {n_assigned - 3} more")

    # Show unassigned events
    assigned_set = set()
    for a in assignments:
        for ev in a:
            assigned_set.add(id(ev))

    # Find first unassigned event in source order
    unassigned_rev = []
    for ev in rev_events:
        found = False
        for a in assignments:
            if any(e is ev for e in a):
                found = True
                break
        if not found:
            unassigned_rev.append(ev)

    if unassigned_rev:
        print(f"\nFirst 5 unassigned events (source order):")
        for ev in unassigned_rev[:5]:
            ename = extract_event_name(ev)
            print(f"  name={ename!s:25s} {ev[:80]}")


def test_matching_forms_all_files(source_root: Path):
    """Verify that forms are distributed in parallel with events across all files.

    Requires boot-metadata to have been captured WITH forms (the updated
    capture script).  If forms are absent, tests are skipped gracefully.
    """
    meta_dir = source_root / ".boot-metadata"
    manifest_path = meta_dir / "manifest.json"
    if not manifest_path.exists():
        print("No manifest — skipping forms integration test")
        return 0

    manifest = json.load(open(manifest_path))
    checked = 0
    problems = 0

    for entry in manifest.get("files", []):
        key = entry["key"]
        stem = entry["stem"]

        meta_path = meta_dir / f"{key}.json"
        if not meta_path.exists():
            continue
        meta = json.load(open(meta_path))
        events = meta.get("events", [])
        forms = meta.get("forms", [])

        if not forms:
            continue  # Old capture without forms — skip

        if len(forms) != len(events):
            print(f"  FAIL {key}: forms ({len(forms)}) != events ({len(events)})")
            problems += 1
            continue

        nb_path = source_root / f"{stem}.ipynb"
        if not nb_path.exists():
            continue

        nb = json.load(open(nb_path))
        code_cells = [
            c for c in nb["cells"]
            if c["cell_type"] == "code"
            and not c.get("metadata", {}).get("provenance", {}).get("boot_strap")
        ]

        evt_a, frm_a = match_events_to_cells(events, code_cells, forms=forms)
        for ci in range(len(code_cells)):
            if len(evt_a[ci]) != len(frm_a[ci]):
                print(f"  FAIL {key} cell {ci}: "
                      f"events ({len(evt_a[ci])}) != forms ({len(frm_a[ci])})")
                problems += 1
        checked += 1

    if checked:
        print(f"forms parallel distribution: {checked} files checked, "
              f"{problems} problems")
    else:
        print("forms parallel distribution: skipped (no forms in metadata)")
    return problems


def main():
    source_root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("/home/acl2")

    print("=== Unit Tests ===")
    failures = 0
    failures += test_extract_event_name()
    failures += test_extract_cell_name()
    failures += test_forms_passthrough()
    failures += test_forms_with_macro_expansion()
    failures += test_forms_empty_cells()

    print("\n=== Integration: all files ===")
    problems = test_matching_all_files(source_root)
    problems += test_matching_forms_all_files(source_root)

    # Show detail for problem files
    if problems > 0 and len(sys.argv) <= 2:
        meta_dir = source_root / ".boot-metadata"
        manifest = json.load(open(meta_dir / "manifest.json"))
        results = summarize_matching(source_root, manifest)
        problem_keys = [f["key"] for f in results["files"] if f["unassigned"] > 0]
        for key in problem_keys[:3]:
            _matching_detail(source_root, key)

    # Also allow explicit detail for one key
    if len(sys.argv) > 2:
        _matching_detail(source_root, sys.argv[2])

    print(f"\n{'PASS' if failures == 0 and problems == 0 else 'ISSUES FOUND'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
