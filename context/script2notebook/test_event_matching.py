#!/usr/bin/env python3
"""Test the event-to-cell matching algorithm across all boot-strap files.

Usage:
    python test_event_matching.py [/home/acl2]
"""

import json
import sys
from pathlib import Path

from event_matching import (
    extract_cell_name,
    extract_event_name,
    match_events_to_cells,
    summarize_matching,
)


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


def test_matching_detail(source_root: Path, key: str):
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


def main():
    source_root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("/home/acl2")

    print("=== Unit Tests ===")
    failures = 0
    failures += test_extract_event_name()
    failures += test_extract_cell_name()

    print("\n=== Integration: all files ===")
    problems = test_matching_all_files(source_root)

    # Show detail for problem files
    if problems > 0 and len(sys.argv) <= 2:
        meta_dir = source_root / ".boot-metadata"
        manifest = json.load(open(meta_dir / "manifest.json"))
        results = summarize_matching(source_root, manifest)
        problem_keys = [f["key"] for f in results["files"] if f["unassigned"] > 0]
        for key in problem_keys[:3]:
            test_matching_detail(source_root, key)

    # Also allow explicit detail for one key
    if len(sys.argv) > 2:
        test_matching_detail(source_root, sys.argv[2])

    print(f"\n{'PASS' if failures == 0 and problems == 0 else 'ISSUES FOUND'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
