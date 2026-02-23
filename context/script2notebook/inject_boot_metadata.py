#!/usr/bin/env python3
"""Inject boot-strap event metadata into ACL2 source notebooks.

This script is specific to the ACL2 build itself — it reads per-file
event data captured by ``capture-boot-metadata.lisp`` (stored under
``<source>/.boot-metadata/``) and distributes events to individual code
cells in the corresponding ``.ipynb`` notebooks.  The result mirrors
what the live ACL2 Jupyter kernel does for certified community books.

Usage::

    inject-boot-metadata /home/acl2          # in-place
    inject-boot-metadata /home/acl2 --force  # re-inject even if present
    inject-boot-metadata /home/acl2 -v       # verbose logging
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from pathlib import Path

from .event_matching import match_events_to_cells

log = logging.getLogger("inject-boot-metadata")


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

BOOT_METADATA_DIR = ".boot-metadata"
EVENTS_MIME = "application/vnd.acl2.events+json"

# ACL2 build infrastructure files that live alongside the source but
# are NOT part of ``*acl2-files*``.
_ACL2_INFRA_STEMS = frozenset({
    "acl2", "acl2-check", "acl2-fns", "acl2-init", "acl2r",
    "acl2-proclaims", "akcl-acl2-trace", "allegro-acl2-trace",
    "openmcl-acl2-trace",
})


def _is_raw_source(stem: str) -> bool:
    """Files ending in ``-raw`` are pure Common Lisp — no ACL2 events."""
    return stem.endswith("-raw")


# ---------------------------------------------------------------------------
# Manifest / metadata loading
# ---------------------------------------------------------------------------

def _load_manifest(source_root: Path) -> dict | None:
    path = source_root / BOOT_METADATA_DIR / "manifest.json"
    if not path.is_file():
        return None
    try:
        with open(path) as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        log.warning("Cannot load boot manifest %s: %s", path, exc)
        return None


def _load_file_metadata(source_root: Path, key: str) -> dict | None:
    path = source_root / BOOT_METADATA_DIR / f"{key}.json"
    if not path.is_file():
        return None
    try:
        with open(path) as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        log.warning("Cannot load boot metadata %s: %s", path, exc)
        return None


# ---------------------------------------------------------------------------
# Notebook helpers
# ---------------------------------------------------------------------------

def _notebook_path(source: Path, source_root: Path, output_root: Path) -> Path:
    rel = source.relative_to(source_root)
    return (output_root / rel).with_suffix(".ipynb")


def _strip_old_boot_metadata(nb: dict) -> bool:
    """Remove any previously-injected boot-strap metadata from *nb*.

    Removes:
      - notebook-level ``acl2_boot_strap`` metadata key
      - per-cell ``provenance.boot_strap`` metadata
      - ``display_data`` outputs with the events MIME type sourced from
        ``boot-strap-capture``
      - any prepended bulk metadata cells from the earlier approach

    Returns True if anything was removed.
    """
    changed = False

    if nb.get("metadata", {}).pop("acl2_boot_strap", None) is not None:
        changed = True

    cells_to_remove = []
    for i, cell in enumerate(nb.get("cells", [])):
        # Remove old bulk metadata cells (from earlier approach)
        prov = cell.get("metadata", {}).get("provenance", {})
        if prov.get("boot_strap"):
            if cell.get("cell_type") == "code" and prov.get("type") == "boot_metadata":
                cells_to_remove.append(i)
                continue
            # Regular cell with boot_strap provenance — clean it
            prov.pop("boot_strap", None)
            prov.pop("pass", None)
            if not prov:
                cell.get("metadata", {}).pop("provenance", None)
            changed = True

        # Strip boot-strap display_data outputs
        if "outputs" in cell:
            new_outputs = []
            for out in cell["outputs"]:
                if (out.get("output_type") == "display_data"
                        and EVENTS_MIME in out.get("data", {})
                        and out["data"][EVENTS_MIME].get("source") == "boot-strap-capture"):
                    changed = True
                    continue
                new_outputs.append(out)
            cell["outputs"] = new_outputs

    for i in reversed(cells_to_remove):
        del nb["cells"][i]
        changed = True

    return changed


# ---------------------------------------------------------------------------
# Per-cell injection
# ---------------------------------------------------------------------------

def _inject_into_notebook(
    notebook: Path,
    metadata_entries: list[dict],
    source: Path,
    *,
    force: bool = False,
) -> bool:
    """Inject per-cell boot-strap event metadata into *notebook*.

    Uses ``event_matching.match_events_to_cells`` to distribute events
    from each pass to the corresponding code cells, adding
    ``display_data`` outputs with ``application/vnd.acl2.events+json``.

    Returns True if the notebook was modified.
    """
    try:
        with open(notebook) as f:
            nb = json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        log.warning("Cannot read %s: %s", notebook, exc)
        return False

    stem = metadata_entries[0].get("stem", source.stem)
    is_raw = _is_raw_source(stem)

    # Strip previous injection (idempotent).
    _strip_old_boot_metadata(nb)

    # --- Notebook-level metadata ---
    boot_meta: dict = {
        "source_type": "raw_common_lisp" if is_raw else "acl2_source",
        "stem": stem,
    }
    if not is_raw:
        boot_meta["passes"] = []
        for entry in metadata_entries:
            boot_meta["passes"].append({
                "pass": entry.get("pass"),
                "position": entry.get("position"),
                "event_count": entry.get("event_count", 0),
                "baseline_event_number": entry.get("baseline_event_number"),
                "final_event_number": entry.get("final_event_number"),
            })

    nb.setdefault("metadata", {})["acl2_boot_strap"] = boot_meta

    if is_raw:
        # Raw CL: just stamp metadata, no events.
        with open(notebook, "w") as f:
            json.dump(nb, f, indent=1)
            f.write("\n")
        return True

    # --- Per-cell event distribution ---
    cells = nb.get("cells", [])
    code_cell_indices = [
        i for i, c in enumerate(cells)
        if c.get("cell_type") == "code"
    ]
    code_cells = [cells[i] for i in code_cell_indices]

    modified = False

    for entry in metadata_entries:
        events = entry.get("events", [])
        if not events:
            continue
        pass_num = entry.get("pass", 1)
        pkg = entry.get("package", "ACL2")

        # match_events_to_cells expects world-order (newest first) which
        # is what the capture script stores.
        assignments = match_events_to_cells(events, code_cells)

        assigned_count = 0
        cells_with_events = 0
        for idx_in_code, cell_events in enumerate(assignments):
            if not cell_events:
                continue
            assigned_count += len(cell_events)
            cells_with_events += 1
            cell_idx = code_cell_indices[idx_in_code]
            cell = cells[cell_idx]

            display_data_output = {
                "output_type": "display_data",
                "data": {
                    EVENTS_MIME: {
                        "events": cell_events,
                        "package": pkg,
                        "source": "boot-strap-capture",
                        "pass": pass_num,
                        "stem": stem,
                    }
                },
                "metadata": {},
            }

            cell.setdefault("outputs", []).append(display_data_output)
            cell.setdefault("metadata", {}).setdefault("provenance", {})
            cell["metadata"]["provenance"]["boot_strap"] = True
            cell["metadata"]["provenance"]["pass"] = pass_num
            modified = True

        log.info(
            "  pass %d: %d events → %d cells (of %d code cells) for %s",
            pass_num, assigned_count, cells_with_events,
            len(code_cells), stem,
        )

        if assigned_count != len(events):
            log.warning(
                "  pass %d: MISMATCH — %d/%d events assigned for %s",
                pass_num, assigned_count, len(events), stem,
            )

    if modified:
        with open(notebook, "w") as f:
            json.dump(nb, f, indent=1)
            f.write("\n")

    return modified


# ---------------------------------------------------------------------------
# Main driver
# ---------------------------------------------------------------------------

def run(
    source_root: Path,
    output_root: Path | None = None,
    *,
    force: bool = False,
) -> tuple[int, int, int]:
    """Inject boot-strap metadata into all ACL2 source notebooks.

    Returns ``(injected, skipped, errors)``.
    """
    if output_root is None:
        output_root = source_root

    manifest = _load_manifest(source_root)
    if manifest is None:
        log.info("No boot-strap metadata found at %s/%s", source_root, BOOT_METADATA_DIR)
        return 0, 0, 0

    # stem → [manifest entries]
    file_entries = manifest.get("files", [])
    stem_keys: dict[str, list[dict]] = {}
    for entry in file_entries:
        stem_keys.setdefault(entry.get("stem", ""), []).append(entry)

    acl2_files_set = set(manifest.get("acl2_files", []))
    injected = skipped = errors = 0

    for source in sorted(source_root.iterdir()):
        if source.suffix != ".lisp" or not source.is_file():
            continue
        # Only top-level ACL2 source files
        if source.parent.resolve() != source_root.resolve():
            continue

        stem = source.stem
        notebook = _notebook_path(source, source_root, output_root)
        if not notebook.exists():
            continue

        if stem in _ACL2_INFRA_STEMS:
            skipped += 1
            continue

        keys = stem_keys.get(stem, [])
        if not keys and stem not in acl2_files_set and not _is_raw_source(stem):
            skipped += 1
            continue

        # Load full metadata (with events) for each pass
        metadata_entries = []
        for entry in keys:
            key = entry.get("key", f"{stem}-pass{entry.get('pass', 1)}")
            full = _load_file_metadata(source_root, key)
            if full:
                metadata_entries.append(full)

        if _is_raw_source(stem) and not metadata_entries:
            metadata_entries = [{"stem": stem, "pass": 0, "events": []}]

        if not metadata_entries and not _is_raw_source(stem):
            log.debug("No boot metadata for %s", stem)
            skipped += 1
            continue

        # Already injected?
        if not force:
            try:
                with open(notebook) as f:
                    nb = json.load(f)
                if nb.get("metadata", {}).get("acl2_boot_strap"):
                    skipped += 1
                    continue
            except (json.JSONDecodeError, OSError):
                pass

        try:
            if _inject_into_notebook(notebook, metadata_entries, source, force=force):
                log.info("Injected: %s (%d passes)", notebook.name, len(metadata_entries))
                injected += 1
            else:
                skipped += 1
        except Exception as exc:
            log.error("FAILED %s: %s", notebook.name, exc, exc_info=True)
            errors += 1

    return injected, skipped, errors


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="inject-boot-metadata",
        description=(
            "Inject captured boot-strap event metadata into ACL2 source "
            "notebooks.  Distributes events to individual code cells, "
            "matching the per-cell output format used by the live kernel."
        ),
    )
    p.add_argument(
        "source", type=Path,
        help="Root directory of ACL2 sources (must contain .boot-metadata/)",
    )
    p.add_argument(
        "-o", "--output", type=Path, default=None,
        help="Output directory for notebooks (default: in-place)",
    )
    p.add_argument(
        "--force", action="store_true",
        help="Re-inject even if metadata is already present",
    )
    p.add_argument(
        "-v", "--verbose", action="store_true",
        help="Enable debug logging",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(levelname)s: %(message)s",
    )

    source = args.source.resolve()
    output = (args.output or args.source).resolve()

    if not source.is_dir():
        log.error("Source %s is not a directory", source)
        return 1

    t0 = time.monotonic()
    injected, skipped, errors = run(source, output, force=args.force)
    elapsed = time.monotonic() - t0

    log.info("Done in %.1fs: %d injected, %d skipped, %d errors",
             elapsed, injected, skipped, errors)


    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
