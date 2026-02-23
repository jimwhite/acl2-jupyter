"""Match captured boot-strap events to notebook code cells.

The capture script produces events in world order (newest first, from
``ldiff``).  Each source ``.lisp`` file has one code cell per top-level
form (produced by the tree-sitter converter).  This module matches the
captured event tuples back to their originating cells so that each cell
gets exactly the events it produced — mirroring what the live kernel
does for community books.

Algorithm
---------
1. Reverse the event list so it is in source order (first form first).
2. Extract a "name" from each event tuple and each cell source.
3. Walk events and cells together: when an event name matches the
   current cell name, anchor that event (and any subsequent sub-events
   that don't match the *next* cell) to that cell.
4. Cells that produce no events (comments, ``in-package``, etc.) get
   an empty list.
"""

from __future__ import annotations

import json
import logging
import re
from pathlib import Path

log = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Name extraction
# ---------------------------------------------------------------------------

def extract_event_name(event_str: str) -> str | None:
    """Extract the defining name from a printed event-tuple string.

    Event tuple formats after stripping the event number:
      - ``(DEFUN NAME ...)``
      - ``(DEFMACRO NAME ...)``
      - ``(DEFCONST NAME ...)``
      - ``(MUTUAL-RECURSION ...)``  → returns ``"MUTUAL-RECURSION"``
      - ``((DEFUN . T) NAME ...)``  (tuple-prefix form)
      - ``((TABLE) ...)``
      - ``((ENCAPSULATE ...) ...)``
      - ``((DEFATTACH ...) ...)``
    """
    s = event_str.strip()
    if not s.startswith("("):
        return None
    s = s[1:]  # skip outer paren

    # Tuple-prefix: ((KIND ...) REST ...)
    # Two sub-formats:
    #   Short prefix: ((TABLE) NAME ...)        → name is parts[0]
    #   Long prefix:  ((DEFUN . T) TO-DF . :CLC) DEFUN TO-DF ...  → name is parts[1]
    #   Encapsulate:  ((ENCAPSULATE . T) 0) ENCAPSULATE NIL ...   → "ENCAPSULATE"
    if s.startswith("("):
        depth = 0
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    break
        rest = s[i + 1 :].lstrip()
        parts = rest.split(None, 3)
        if not parts:
            return None
        first = parts[0].rstrip(")")
        # If first token is a known event type keyword, the name is next
        _EVENT_TYPES = {
            "DEFUN", "DEFMACRO", "DEFCONST", "DEFTHM", "DEFSTOBJ",
            "DEFATTACH", "DEFPKG", "DEFLABEL", "DEFAXIOM", "DEFCHOOSE",
            "VERIFY-GUARDS", "IN-THEORY", "TABLE", "MUTUAL-RECURSION",
            "ENCAPSULATE", "PROGN", "INCLUDE-BOOK",
        }
        if first in _EVENT_TYPES and len(parts) >= 2:
            if first in ("MUTUAL-RECURSION", "ENCAPSULATE"):
                return first
            return parts[1].rstrip(")")
        return first

    # Normal: (KIND NAME ...) or (MUTUAL-RECURSION ...)
    parts = s.split(None, 2)
    if len(parts) >= 2:
        kind = parts[0]
        name = parts[1].rstrip(")")
        if kind in ("MUTUAL-RECURSION", "ENCAPSULATE"):
            return kind
        return name
    return parts[0].rstrip(")") if parts else None


def _strip_package(name: str) -> str:
    """Strip any package prefix (e.g. 'ACL2::FOO' → 'FOO')."""
    idx = name.find("::")
    if idx >= 0:
        return name[idx + 2 :]
    return name


def extract_cell_name(src: str) -> str | None:
    """Extract the defining name from a code cell's source text.

    Handles reader conditionals (``#+`` / ``#-``), ``defun-inline``,
    ``mutual-recursion``, etc.  Returns the uppercased name, or None
    for non-event forms (comments, ``in-package``, bare values).
    """
    s = src.strip()

    # Strip reader conditionals: #+feature or #-feature then a form or token
    for _ in range(10):  # bounded loop
        if s.startswith("#+") or s.startswith("#-"):
            s = s[2:]
            if s.startswith("("):
                depth = 0
                for i, ch in enumerate(s):
                    if ch == "(":
                        depth += 1
                    elif ch == ")":
                        depth -= 1
                    if depth == 0:
                        s = s[i + 1 :].lstrip()
                        break
                else:
                    return None  # malformed
            else:
                parts = s.split(None, 1)
                s = parts[1] if len(parts) > 1 else ""
            s = s.lstrip()
        else:
            break

    if not s.startswith("("):
        # Bare symbol like *acl2-system-documentation* — return uppercased
        token = s.split(None, 1)[0] if s else None
        if token and not token.startswith(";"):
            return _strip_package(token.upper().rstrip(")"))
        return None

    inner = s[1:]
    parts = inner.split(None, 2)
    if not parts:
        return None

    kind = _strip_package(parts[0].upper().rstrip(")"))
    if len(parts) >= 2:
        name = _strip_package(parts[1].upper().rstrip(")"))
        if kind in ("MUTUAL-RECURSION", "ENCAPSULATE"):
            return kind
        return name
    return kind


# ---------------------------------------------------------------------------
# Matching
# ---------------------------------------------------------------------------

def match_events_to_cells(
    events: list[str],
    code_cells: list[dict],
    *,
    forms: list[str] | None = None,
) -> list[list[str]] | tuple[list[list[str]], list[list[str]]]:
    """Assign events to code cells by name-anchored sequential matching.

    *events* are in world order (newest first).  We reverse them to
    source order, then walk through cells and events together.

    The algorithm is greedy and resilient to macro-expansion mismatches:

    1. Build a cell-name index and an event-name sequence.
    2. Walk events in source order.  For each event, scan forward in
       cells to find a name match.  If found, anchor the event there
       and assign any intervening unmatched events to the *preceding*
       anchored cell (they are sub-events of a macro expansion).
    3. After all events are processed, any trailing unmatched events
       go to the last anchored cell.

    If *forms* is provided (parallel list, same length as *events*),
    returns ``(event_assignments, form_assignments)`` — two parallel
    lists-of-lists.  Otherwise returns just *event_assignments*.

    Each returned list is parallel to *code_cells* where each element
    is the list of strings assigned to that cell (may be empty).
    """
    rev_events = list(reversed(events))
    rev_forms = list(reversed(forms)) if forms is not None else None
    n_events = len(rev_events)

    # Pre-compute cell names (uppercased, package-stripped).
    cell_names: list[str | None] = []
    for c in code_cells:
        src = "".join(c["source"]) if isinstance(c["source"], list) else c["source"]
        cell_names.append(extract_cell_name(src))

    # Build a map from name → list of cell indices (in order) for fast lookup.
    from collections import defaultdict
    name_to_cells: dict[str, list[int]] = defaultdict(list)
    for ci, cname in enumerate(cell_names):
        if cname is not None:
            name_to_cells[cname].append(ci)

    # For each cell name, track how many we've consumed (pointer into list).
    name_cursor: dict[str, int] = defaultdict(int)

    event_assignments: list[list[str]] = [[] for _ in code_cells]
    form_assignments: list[list[str]] = [[] for _ in code_cells] if rev_forms is not None else []

    # Phase 1: anchor events to cells by name match.
    # For each event, find the earliest unused cell with matching name
    # that comes after the last anchor point.
    anchors: list[tuple[int, int]] = []  # (event_idx, cell_idx)
    last_anchor_ci = -1

    for ei in range(n_events):
        ename = extract_event_name(rev_events[ei])
        if ename is None:
            continue
        candidates = name_to_cells.get(ename, [])
        cursor = name_cursor.get(ename, 0)
        # Find first candidate cell after last_anchor_ci
        matched_ci = None
        for idx in range(cursor, len(candidates)):
            ci = candidates[idx]
            if ci > last_anchor_ci:
                matched_ci = ci
                name_cursor[ename] = idx + 1
                break
        if matched_ci is not None:
            anchors.append((ei, matched_ci))
            last_anchor_ci = matched_ci

    def _assign(ci: int, ei: int):
        event_assignments[ci].append(rev_events[ei])
        if rev_forms is not None:
            form_assignments[ci].append(rev_forms[ei])

    # Phase 2: assign events to cells based on anchors.
    # Events between two anchors go to the first anchor's cell
    # (they are macro-expansion sub-events of that cell's form).
    if not anchors:
        # No anchors at all — put everything in cell 0 if there is one
        if code_cells:
            for ei in range(n_events):
                _assign(0, ei)
        if rev_forms is not None:
            return event_assignments, form_assignments
        return event_assignments

    # Events before first anchor → first anchor's cell
    first_anchor_ei, first_anchor_ci = anchors[0]
    for ei in range(first_anchor_ei):
        _assign(first_anchor_ci, ei)

    # Events at and between anchors
    for ai in range(len(anchors)):
        anchor_ei, anchor_ci = anchors[ai]
        next_ei = anchors[ai + 1][0] if ai + 1 < len(anchors) else n_events
        for ei in range(anchor_ei, next_ei):
            _assign(anchor_ci, ei)

    if rev_forms is not None:
        return event_assignments, form_assignments
    return event_assignments


# ---------------------------------------------------------------------------
# Diagnostics
# ---------------------------------------------------------------------------

def summarize_matching(
    source_root: Path,
    manifest: dict,
) -> dict:
    """Run matching across all files and return a summary dict.

    Returns ``{"total_events", "total_assigned", "files": [...]}``.
    """
    meta_dir = source_root / ".boot-metadata"
    results = {
        "total_events": 0,
        "total_assigned": 0,
        "files": [],
    }

    for entry in manifest.get("files", []):
        key = entry["key"]
        stem = entry["stem"]

        meta_path = meta_dir / f"{key}.json"
        if not meta_path.exists():
            continue
        meta = json.load(open(meta_path))
        events = meta.get("events", [])
        if not events:
            results["files"].append({
                "key": key, "events": 0, "assigned": 0, "unassigned": 0,
            })
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

        assignments = match_events_to_cells(events, code_cells)
        assigned = sum(len(a) for a in assignments)
        unassigned = len(events) - assigned

        results["total_events"] += len(events)
        results["total_assigned"] += assigned
        results["files"].append({
            "key": key,
            "events": len(events),
            "assigned": assigned,
            "unassigned": unassigned,
        })

    return results
