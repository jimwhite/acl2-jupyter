#!/usr/bin/env python3
"""Build ACL2 notebooks from source files and execute certified ones.

Two-phase workflow:

  1. **Convert** — Use ``script2notebook`` to convert ``.lisp`` / ``.lsp`` /
     ``.acl2`` source files to ``.ipynb`` notebooks, preserving directory
     structure under an output root.

  2. **Execute** — Run notebooks whose source ``.lisp`` has an accompanying
     ``.cert`` file through the ACL2 kernel via ``jupyter nbconvert --execute``
     to capture execution metadata (display data, outputs).

Both phases are incremental: files are only rebuilt when the source is newer
than the output.  Use ``--force`` to override.

Usage examples::

    # Convert all .lisp files under /home/acl2 into notebooks
    build-notebooks convert /home/acl2 -o /workspace/notebooks/acl2

    # Execute only the certified ones
    build-notebooks execute /home/acl2 -o /workspace/notebooks/acl2

    # Do both in one shot
    build-notebooks all /home/acl2 -o /workspace/notebooks/acl2

    # Parallel execution with 4 workers
    build-notebooks execute /home/acl2 -o /workspace/notebooks/acl2 -j 4

    # Only process a subtree
    build-notebooks all /home/acl2/books/arithmetic-3 -o /workspace/notebooks/acl2/books/arithmetic-3
"""

from __future__ import annotations

import argparse
import logging
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

log = logging.getLogger("build-notebooks")

# Extensions handled by script2notebook (from its EXTENSION_MAP).
SOURCE_EXTENSIONS = {".lisp", ".lsp", ".acl2"}

# Default cell execution timeout (seconds).  ACL2 proofs can be slow.
DEFAULT_CELL_TIMEOUT = 600  # 10 minutes per cell

# Default kernel startup timeout (seconds).  ACL2 kernel loads a big image.
DEFAULT_STARTUP_TIMEOUT = 120


# ── helpers ──────────────────────────────────────────────────────────


def _find_source_files(source_dir: Path) -> list[Path]:
    """Recursively find all convertible source files under *source_dir*."""
    files = []
    for root, _dirs, names in os.walk(source_dir):
        for name in sorted(names):
            p = Path(root) / name
            if p.suffix in SOURCE_EXTENSIONS:
                files.append(p)
    return files


def _notebook_path(source: Path, source_root: Path, output_root: Path) -> Path:
    """Compute the output .ipynb path preserving directory structure."""
    rel = source.relative_to(source_root)
    return (output_root / rel).with_suffix(".ipynb")


def _is_stale(source: Path, target: Path, force: bool = False) -> bool:
    """Return True when *target* needs to be rebuilt from *source*."""
    if force:
        return True
    if not target.exists():
        return True
    return source.stat().st_mtime > target.stat().st_mtime


def _has_cert(source: Path) -> bool:
    """Return True if *source* has an accompanying .cert file."""
    return source.with_suffix(".cert").exists()


# ── Phase 1: Convert ────────────────────────────────────────────────


def convert_one(
    source: Path,
    source_root: Path,
    output_root: Path,
    force: bool = False,
) -> Path | None:
    """Convert a single source file to a notebook.  Returns output path or None if skipped."""
    notebook = _notebook_path(source, source_root, output_root)

    if not _is_stale(source, notebook, force):
        return None

    notebook.parent.mkdir(parents=True, exist_ok=True)

    result = subprocess.run(
        ["script2notebook", str(source), "-o", str(notebook)],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        log.error("convert failed: %s\n%s", source, result.stderr.strip())
        return None

    return notebook


def phase_convert(
    source_root: Path,
    output_root: Path,
    force: bool = False,
) -> tuple[int, int, int]:
    """Convert all source files.  Returns (converted, skipped, errors)."""
    sources = _find_source_files(source_root)
    log.info("Found %d source files under %s", len(sources), source_root)

    converted = skipped = errors = 0
    for source in sources:
        result = convert_one(source, source_root, output_root, force)
        if result is None:
            notebook = _notebook_path(source, source_root, output_root)
            if notebook.exists():
                skipped += 1
            else:
                errors += 1
        else:
            converted += 1

    return converted, skipped, errors


# ── Phase 2: Execute ────────────────────────────────────────────────


def _execute_notebook(
    notebook: Path,
    kernel_name: str,
    cell_timeout: int,
    startup_timeout: int,
    allow_errors: bool,
) -> tuple[Path, bool, str]:
    """Execute a single notebook in-place.  Returns (path, success, message)."""
    cmd = [
        "jupyter", "nbconvert",
        "--to", "notebook",
        "--inplace",
        "--execute",
        f"--ExecutePreprocessor.kernel_name={kernel_name}",
        f"--ExecutePreprocessor.timeout={cell_timeout}",
        f"--ExecutePreprocessor.startup_timeout={startup_timeout}",
    ]
    if allow_errors:
        cmd.append("--ExecutePreprocessor.allow_errors=True")
    cmd.append(str(notebook))

    t0 = time.monotonic()
    result = subprocess.run(cmd, capture_output=True, text=True)
    elapsed = time.monotonic() - t0

    if result.returncode == 0:
        return notebook, True, f"OK ({elapsed:.1f}s)"
    else:
        # Extract last few lines of stderr for diagnosis
        stderr_tail = "\n".join(result.stderr.strip().splitlines()[-5:])
        return notebook, False, f"FAILED ({elapsed:.1f}s): {stderr_tail}"


def _notebook_has_outputs(notebook: Path) -> bool:
    """Return True if *notebook* has any code cell with outputs.

    A freshly converted notebook has code cells with empty outputs lists.
    After execution, cells gain outputs.  This is a cheap heuristic to
    detect whether execution has been run.
    """
    import json
    try:
        with open(notebook) as f:
            nb = json.load(f)
        for cell in nb.get("cells", []):
            if cell.get("cell_type") == "code" and cell.get("outputs"):
                return True
    except (json.JSONDecodeError, OSError):
        pass
    return False


def _find_executable_notebooks(
    source_root: Path,
    output_root: Path,
    force: bool = False,
) -> list[tuple[Path, Path]]:
    """Find notebooks whose source .lisp has a .cert file.

    Returns list of (source, notebook) pairs that need execution.
    The notebook must exist (i.e. convert phase has been run) and its
    source must have an accompanying .cert file.

    A notebook needs execution when:
    - ``force`` is set, or
    - the source ``.lisp`` or ``.cert`` is newer than the notebook, or
    - the notebook has never been executed (no outputs in any code cell).
    """
    sources = _find_source_files(source_root)
    pairs = []
    for source in sources:
        if not _has_cert(source):
            continue
        notebook = _notebook_path(source, source_root, output_root)
        if not notebook.exists():
            log.warning("Notebook missing for certified source %s — run convert first", source)
            continue

        cert = source.with_suffix(".cert")
        if _is_stale(cert, notebook, force) or _is_stale(source, notebook, force):
            pairs.append((source, notebook))
        elif not _notebook_has_outputs(notebook):
            # Notebook was converted but never executed.
            log.debug("Notebook %s has no outputs — needs execution", notebook)
            pairs.append((source, notebook))

    return pairs


def phase_execute(
    source_root: Path,
    output_root: Path,
    jobs: int = 1,
    kernel_name: str = "acl2",
    cell_timeout: int = DEFAULT_CELL_TIMEOUT,
    startup_timeout: int = DEFAULT_STARTUP_TIMEOUT,
    allow_errors: bool = True,
    force: bool = False,
) -> tuple[int, int, int]:
    """Execute certified notebooks.  Returns (executed, skipped, errors)."""
    pairs = _find_executable_notebooks(source_root, output_root, force)
    total_certified = sum(
        1 for s in _find_source_files(source_root) if _has_cert(s)
    )
    log.info(
        "Found %d certified sources, %d notebooks need execution",
        total_certified,
        len(pairs),
    )

    if not pairs:
        return 0, total_certified, 0

    executed = errors = 0

    if jobs <= 1:
        for source, notebook in pairs:
            log.info("Executing %s", notebook)
            path, ok, msg = _execute_notebook(
                notebook, kernel_name, cell_timeout, startup_timeout, allow_errors
            )
            if ok:
                log.info("  %s", msg)
                executed += 1
            else:
                log.error("  %s", msg)
                errors += 1
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            futures = {
                pool.submit(
                    _execute_notebook,
                    notebook,
                    kernel_name,
                    cell_timeout,
                    startup_timeout,
                    allow_errors,
                ): (source, notebook)
                for source, notebook in pairs
            }
            for future in as_completed(futures):
                source, notebook = futures[future]
                try:
                    path, ok, msg = future.result()
                    if ok:
                        log.info("Executed %s: %s", path, msg)
                        executed += 1
                    else:
                        log.error("Execute %s: %s", path, msg)
                        errors += 1
                except Exception as exc:
                    log.error("Execute %s: exception: %s", notebook, exc)
                    errors += 1

    skipped = total_certified - executed - errors
    return executed, skipped, errors


# ── CLI ──────────────────────────────────────────────────────────────


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="build-notebooks",
        description=(
            "Convert ACL2 source files to Jupyter notebooks and execute "
            "certified ones to capture proof output."
        ),
    )
    sub = p.add_subparsers(dest="command", required=True)

    # -- convert --
    conv = sub.add_parser("convert", help="Convert .lisp files to .ipynb")
    conv.add_argument("source", type=Path, help="Root directory of ACL2 sources")
    conv.add_argument(
        "-o", "--output", type=Path, required=True,
        help="Output directory for notebooks (preserves sub-dir structure)",
    )
    conv.add_argument("--force", action="store_true", help="Convert even if up-to-date")
    conv.add_argument("-v", "--verbose", action="store_true")

    # -- execute --
    exe = sub.add_parser("execute", help="Execute certified notebooks through ACL2 kernel")
    exe.add_argument("source", type=Path, help="Root directory of ACL2 sources")
    exe.add_argument(
        "-o", "--output", type=Path, required=True,
        help="Output directory (must match convert output)",
    )
    exe.add_argument(
        "-j", "--jobs", type=int, default=1,
        help="Number of parallel execution workers (default: 1)",
    )
    exe.add_argument(
        "--kernel", default="acl2",
        help="Jupyter kernel name (default: acl2)",
    )
    exe.add_argument(
        "--cell-timeout", type=int, default=DEFAULT_CELL_TIMEOUT,
        help=f"Per-cell execution timeout in seconds (default: {DEFAULT_CELL_TIMEOUT})",
    )
    exe.add_argument(
        "--startup-timeout", type=int, default=DEFAULT_STARTUP_TIMEOUT,
        help=f"Kernel startup timeout in seconds (default: {DEFAULT_STARTUP_TIMEOUT})",
    )
    exe.add_argument(
        "--no-allow-errors", action="store_true",
        help="Stop on first cell error (default: continue past errors)",
    )
    exe.add_argument("--force", action="store_true", help="Re-execute even if up-to-date")
    exe.add_argument("-v", "--verbose", action="store_true")

    # -- all (convert + execute) --
    both = sub.add_parser("all", help="Convert then execute (both phases)")
    both.add_argument("source", type=Path, help="Root directory of ACL2 sources")
    both.add_argument(
        "-o", "--output", type=Path, required=True,
        help="Output directory for notebooks",
    )
    both.add_argument(
        "-j", "--jobs", type=int, default=1,
        help="Number of parallel execution workers (default: 1)",
    )
    both.add_argument(
        "--kernel", default="acl2",
        help="Jupyter kernel name (default: acl2)",
    )
    both.add_argument(
        "--cell-timeout", type=int, default=DEFAULT_CELL_TIMEOUT,
        help=f"Per-cell execution timeout in seconds (default: {DEFAULT_CELL_TIMEOUT})",
    )
    both.add_argument(
        "--startup-timeout", type=int, default=DEFAULT_STARTUP_TIMEOUT,
        help=f"Kernel startup timeout in seconds (default: {DEFAULT_STARTUP_TIMEOUT})",
    )
    both.add_argument(
        "--no-allow-errors", action="store_true",
        help="Stop on first cell error",
    )
    both.add_argument("--force", action="store_true", help="Rebuild everything")
    both.add_argument("-v", "--verbose", action="store_true")

    return p


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(levelname)s: %(message)s",
    )

    source = args.source.resolve()
    output = args.output.resolve()

    if not source.is_dir():
        log.error("Source %s is not a directory", source)
        return 1

    t0 = time.monotonic()
    total_errors = 0

    if args.command in ("convert", "all"):
        log.info("=== Phase 1: Convert ===")
        converted, skipped, errors = phase_convert(source, output, args.force)
        log.info("Convert done: %d converted, %d up-to-date, %d errors", converted, skipped, errors)
        total_errors += errors

    if args.command in ("execute", "all"):
        log.info("=== Phase 2: Execute ===")
        jobs = getattr(args, "jobs", 1)
        kernel = getattr(args, "kernel", "acl2")
        cell_timeout = getattr(args, "cell_timeout", DEFAULT_CELL_TIMEOUT)
        startup_timeout = getattr(args, "startup_timeout", DEFAULT_STARTUP_TIMEOUT)
        allow_errors = not getattr(args, "no_allow_errors", False)

        executed, skipped, errors = phase_execute(
            source, output,
            jobs=jobs,
            kernel_name=kernel,
            cell_timeout=cell_timeout,
            startup_timeout=startup_timeout,
            allow_errors=allow_errors,
            force=args.force,
        )
        log.info("Execute done: %d executed, %d up-to-date, %d errors", executed, skipped, errors)
        total_errors += errors

    elapsed = time.monotonic() - t0
    log.info("Total time: %.1fs", elapsed)

    return 1 if total_errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
