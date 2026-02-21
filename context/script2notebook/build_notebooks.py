#!/usr/bin/env python3
"""Build ACL2 notebooks from source files and execute certified ones.

Two-phase workflow:

  1. **Convert** — Use ``script2notebook`` to convert ``.lisp`` / ``.lsp`` /
     ``.acl2`` source files to ``.ipynb`` notebooks.

  2. **Execute** — Run notebooks whose source ``.lisp`` has an accompanying
     ``.cert`` file through the ACL2 kernel via ``jupyter nbconvert --execute``
     to capture execution metadata (display data, outputs).

By default notebooks are placed alongside the source files (in-place).  Use
``-o`` to redirect output to a separate directory tree.

Both phases are incremental: files are only rebuilt when the source is newer
than the output.  Use ``--force`` to override.

Usage examples::

    # Convert all .lisp files under defsort — notebooks go alongside .lisp
    build-notebooks convert /home/acl2/books/defsort

    # Do both phases in one shot (in-place)
    build-notebooks all /home/acl2/books/defsort

    # Redirect output to a separate tree
    build-notebooks all /home/acl2 -o /workspace/notebooks/acl2

    # Parallel execution with 4 workers
    build-notebooks all /home/acl2/books/defsort -j 4
"""

from __future__ import annotations

import argparse
import itertools
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
# .acl2 files are portcullis companions, not standalone sources.
SOURCE_EXTENSIONS = {".lisp", ".lsp"}

# Default cell execution timeout (seconds).  ACL2 proofs can be slow.
DEFAULT_CELL_TIMEOUT = 600  # 10 minutes per cell

# Default kernel startup timeout (seconds).  ACL2 kernel loads a big image.
DEFAULT_STARTUP_TIMEOUT = 120

# Default number of execution retries on failure (kernel died, etc.).
DEFAULT_EXECUTE_RETRIES = 1

# Default directory for kernel log files (None = don't redirect).
DEFAULT_LOG_DIR: Path | None = None


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


def _acl2_companion_files(source: Path) -> list[tuple[str, str]]:
    """Find ACL2 portcullis companion files for *source*.

    ACL2 uses ``.acl2`` files to specify *portcullis commands* that must
    be evaluated before certifying a book.  Two naming conventions:

    * ``book-name.acl2`` — per-book companion (matched by stem).
    * ``cert.acl2`` — directory-wide default applied to every book in
      the directory that does not have its own ``.acl2`` file.

    Returns a list of ``(label, content)`` pairs, e.g.
    ``[("cert.acl2", "…"), ("foo.acl2", "…")]``.
    The per-book companion, if present, takes precedence in ACL2's
    certification process, but we record all that exist for
    documentation purposes.
    """
    companions = []
    cert_acl2 = source.parent / "cert.acl2"
    book_acl2 = source.with_suffix(".acl2")
    for path in (cert_acl2, book_acl2):
        if path.is_file():
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
                companions.append((path.name, text))
            except OSError:
                pass
    return companions


def _inject_acl2_metadata(notebook: Path, source: Path) -> None:
    """Add ``.acl2`` portcullis companion content to notebook metadata.

    Reads the notebook JSON, adds an ``acl2_portcullis`` key to the
    top-level metadata with a dict mapping companion filenames to their
    text content, then writes it back.  No-op if no companions exist.
    """
    import json

    companions = _acl2_companion_files(source)
    if not companions:
        return

    try:
        with open(notebook) as f:
            nb = json.load(f)
    except (json.JSONDecodeError, OSError) as exc:
        log.warning("Cannot patch metadata for %s: %s", notebook, exc)
        return

    nb.setdefault("metadata", {})["acl2_portcullis"] = {
        name: content for name, content in companions
    }

    with open(notebook, "w") as f:
        json.dump(nb, f, indent=1)
        f.write("\n")


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


# Conversion timeouts (seconds).
CONVERT_WARN_TIMEOUT = 30    # Log a warning after this long.
CONVERT_GIVE_UP_TIMEOUT = 300  # 5 minutes — write placeholder and move on.


def _write_placeholder_notebook(notebook: Path, source: Path, reason: str) -> None:
    """Write a minimal placeholder .ipynb so the file isn't retried."""
    import json
    nb = {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": {
            "kernelspec": {
                "display_name": "ACL2",
                "language": "acl2",
                "name": "acl2",
            },
            "placeholder": True,
            "placeholder_reason": reason,
            "source_file": str(source),
        },
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": [
                    f"**Placeholder** — conversion of `{source.name}` was skipped.\n",
                    f"\n",
                    f"Reason: {reason}\n",
                ],
            }
        ],
    }
    notebook.parent.mkdir(parents=True, exist_ok=True)
    with open(notebook, "w") as f:
        json.dump(nb, f, indent=1)


def _do_convert(source: Path, source_root: Path, output_root: Path,
                convert_timeout: int = CONVERT_GIVE_UP_TIMEOUT) -> Path | None:
    """Run script2notebook on a single file.  Returns output path or None on error.

    Assumes staleness has already been checked and the parent dir exists.
    Warns after 30s, gives up after *convert_timeout* seconds and writes a
    placeholder.  Set *convert_timeout* to 0 to disable the timeout.
    """
    notebook = _notebook_path(source, source_root, output_root)
    notebook.parent.mkdir(parents=True, exist_ok=True)

    proc = subprocess.Popen(
        ["script2notebook", "--fenced", str(source), "-o", str(notebook)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )

    if convert_timeout == 0:
        # No timeout — just wait with periodic warnings.
        warned = False
        try:
            stdout, stderr = proc.communicate(timeout=CONVERT_WARN_TIMEOUT)
        except subprocess.TimeoutExpired:
            warned = True
            log.warning("convert slow (>%ds): %s — no timeout, waiting…",
                        CONVERT_WARN_TIMEOUT, source)
            stdout, stderr = proc.communicate()  # wait forever
    else:
        warned = False
        try:
            stdout, stderr = proc.communicate(timeout=CONVERT_WARN_TIMEOUT)
        except subprocess.TimeoutExpired:
            warned = True
            log.warning("convert slow (>%ds): %s — still waiting…",
                        CONVERT_WARN_TIMEOUT, source)
            remaining = max(1, convert_timeout - CONVERT_WARN_TIMEOUT)
            try:
                stdout, stderr = proc.communicate(timeout=remaining)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
                log.error("convert timeout (>%ds) — writing placeholder: %s",
                           convert_timeout, source)
                _write_placeholder_notebook(
                    notebook, source,
                    f"Conversion timed out after {convert_timeout}s",
                )
                return notebook

    if proc.returncode != 0:
        stderr_text = stderr.decode("utf-8", errors="replace").strip()
        log.error("convert failed: %s\n%s", source, stderr_text)
        _write_placeholder_notebook(
            notebook, source,
            f"Conversion failed: {stderr_text[:200]}",
        )
        return notebook  # placeholder so it won't retry

    if warned:
        log.info("convert finished (slow): %s", source)

    # Patch notebook metadata with .acl2 portcullis companion info.
    _inject_acl2_metadata(notebook, source)

    return notebook


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

    return _do_convert(source, source_root, output_root)


def _bounded_as_completed(pool, fn, items, max_pending):
    """Submit work to *pool* in bounded batches, yielding (future, item) pairs.

    At most *max_pending* futures are in-flight at any time, preventing
    the process pool's call queue from growing unbounded for large inputs.
    """
    it = iter(items)
    pending: dict = {}

    # Prime the pump with the first batch.
    for item in itertools.islice(it, max_pending):
        f = pool.submit(fn, *item) if isinstance(item, tuple) else pool.submit(fn, item)
        pending[f] = item

    while pending:
        # Wait for at least one to finish.
        done_iter = as_completed(pending)
        future = next(done_iter)
        item = pending.pop(future)
        yield future, item

        # Refill: submit one new task for each completed one.
        for new_item in itertools.islice(it, 1):
            f = pool.submit(fn, *new_item) if isinstance(new_item, tuple) else pool.submit(fn, new_item)
            pending[f] = new_item


def phase_convert(
    source_root: Path,
    output_root: Path,
    force: bool = False,
    jobs: int = 1,
    convert_timeout: int = CONVERT_GIVE_UP_TIMEOUT,
) -> tuple[int, int, int]:
    """Convert all source files.  Returns (converted, skipped, errors)."""
    sources = _find_source_files(source_root)
    total = len(sources)
    log.info("Found %d source files under %s", total, source_root)

    # ── Check staleness in the main process (fast stat calls) ──
    stale: list[Path] = []
    skipped = 0
    t_last = time.monotonic()
    for i, source in enumerate(sources):
        notebook = _notebook_path(source, source_root, output_root)
        if _is_stale(source, notebook, force):
            stale.append(source)
        else:
            skipped += 1
        now = time.monotonic()
        if (now - t_last >= 5.0) or (i + 1 == total):
            t_last = now
            log.info("  staleness check: %d/%d (%d need conversion)", i + 1, total, len(stale))

    if not stale:
        return 0, skipped, 0

    # ── Convert only the stale files ──
    converted = errors = 0
    n_stale = len(stale)
    log.info("Converting %d files…", n_stale)

    if jobs <= 1:
        t_last = time.monotonic()
        for i, source in enumerate(stale):
            result = _do_convert(source, source_root, output_root, convert_timeout)
            if result is None:
                errors += 1
            else:
                converted += 1
            now = time.monotonic()
            if (now - t_last >= 5.0) or (i + 1 == n_stale):
                t_last = now
                log.info("  converting: %d/%d (errors %d)", i + 1, n_stale, errors)
    else:
        # Items are (source, source_root, output_root, convert_timeout) tuples.
        items = [(source, source_root, output_root, convert_timeout) for source in stale]
        max_pending = jobs * 2
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            try:
                done = 0
                t_last = time.monotonic()
                for future, item in _bounded_as_completed(pool, _do_convert, items, max_pending):
                    source = item[0]
                    try:
                        result = future.result()
                        if result is None:
                            errors += 1
                        else:
                            converted += 1
                    except Exception as exc:
                        log.error("Convert %s: exception: %s", source, exc)
                        errors += 1
                    done += 1
                    now = time.monotonic()
                    if (now - t_last >= 5.0) or (done == n_stale):
                        t_last = now
                        log.info("  converting: %d/%d (errors %d)", done, n_stale, errors)
            except KeyboardInterrupt:
                log.warning("Interrupted — cancelling remaining conversions…")
                pool.shutdown(wait=False, cancel_futures=True)
                return converted, skipped, errors

    return converted, skipped, errors


# ── Phase 2: Execute ────────────────────────────────────────────────


def _execute_notebook(
    notebook: Path,
    kernel_name: str,
    cell_timeout: int,
    startup_timeout: int,
    allow_errors: bool,
    source_dir: Path | None = None,
    log_dir: Path | None = None,
    source_root: Path | None = None,
) -> tuple[Path, bool, str]:
    """Execute a single notebook in-place.  Returns (path, success, message).

    *source_dir*, when given, sets the kernel working directory so that
    relative ``include-book`` paths resolve against the original source
    tree rather than the output directory.

    *log_dir*, when given, redirects kernel log files out of the source
    tree via ``XDG_RUNTIME_DIR`` and names them after the notebook via
    ``JUPYTER_LOG_NAME``.
    """
    cmd = [
        "jupyter", "nbconvert",
        "--to", "notebook",
        "--inplace",
        "--execute",
        f"--ExecutePreprocessor.kernel_name={kernel_name}",
        f"--ExecutePreprocessor.timeout={cell_timeout}",
        f"--ExecutePreprocessor.startup_timeout={startup_timeout}",
    ]
    if source_dir is not None:
        cmd.append(f"--ExecutePreprocessor.cwd={source_dir}")
    if allow_errors:
        cmd.append("--ExecutePreprocessor.allow_errors=True")
    cmd.append(str(notebook))

    env = None
    if log_dir is not None:
        env = os.environ.copy()
        # Mirror source tree structure under log_dir.
        if source_root and source_dir:
            try:
                rel = source_dir.relative_to(source_root)
                runtime_dir = log_dir / rel
            except ValueError:
                runtime_dir = log_dir
        else:
            runtime_dir = log_dir
        runtime_dir.mkdir(parents=True, exist_ok=True)
        env["XDG_RUNTIME_DIR"] = str(runtime_dir)
        env["JUPYTER_LOG_NAME"] = notebook.stem

    t0 = time.monotonic()
    result = subprocess.run(cmd, capture_output=True, text=True, env=env)
    elapsed = time.monotonic() - t0

    if result.returncode == 0:
        return notebook, True, f"OK ({elapsed:.1f}s)"
    else:
        # Extract last few lines of stderr for diagnosis
        stderr_tail = "\n".join(result.stderr.strip().splitlines()[-5:])
        return notebook, False, f"FAILED ({elapsed:.1f}s): {stderr_tail}"


def _execute_with_retries(
    notebook: Path,
    kernel_name: str,
    cell_timeout: int,
    startup_timeout: int,
    allow_errors: bool,
    source_dir: Path | None,
    retries: int,
    log_dir: Path | None = None,
    source_root: Path | None = None,
) -> tuple[Path, bool, str]:
    """Execute *notebook* with up to *retries* retries on failure."""
    for attempt in range(1 + retries):
        path, ok, msg = _execute_notebook(
            notebook, kernel_name, cell_timeout, startup_timeout,
            allow_errors, source_dir=source_dir,
            log_dir=log_dir, source_root=source_root,
        )
        if ok:
            if attempt > 0:
                msg += f" (after {attempt + 1} attempts)"
            return path, ok, msg
        if attempt < retries:
            log.warning("Execute %s: attempt %d/%d failed, retrying… %s",
                        notebook, attempt + 1, 1 + retries, msg)
    return path, ok, msg


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
    certified = [(s, s.with_suffix(".cert")) for s in sources if _has_cert(s)]
    log.info("Scanning %d certified sources for notebooks needing execution…", len(certified))

    pairs = []
    missing = 0
    checked = 0
    t_last = time.monotonic()
    for source, cert in certified:
        notebook = _notebook_path(source, source_root, output_root)
        if not notebook.exists():
            missing += 1
            checked += 1
            continue

        if _is_stale(cert, notebook, force) or _is_stale(source, notebook, force):
            pairs.append((source, notebook))
        elif not _notebook_has_outputs(notebook):
            pairs.append((source, notebook))

        checked += 1
        now = time.monotonic()
        if now - t_last >= 5.0:
            t_last = now
            log.info("  scan progress: %d/%d checked, %d need execution",
                     checked, len(certified), len(pairs))

    if missing:
        log.warning("%d certified sources have no notebook — run convert first", missing)

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
    retries: int = DEFAULT_EXECUTE_RETRIES,
    log_dir: Path | None = DEFAULT_LOG_DIR,
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

    if log_dir is not None:
        log.info("Kernel logs → %s", log_dir)

    executed = errors = 0

    if jobs <= 1:
        for source, notebook in pairs:
            log.info("Executing %s", notebook)
            path, ok, msg = _execute_with_retries(
                notebook, kernel_name, cell_timeout, startup_timeout,
                allow_errors, source.parent, retries,
                log_dir=log_dir, source_root=source_root,
            )
            if ok:
                log.info("  %s", msg)
                executed += 1
            else:
                log.error("  %s", msg)
                errors += 1
    else:
        # Items are tuples matching _execute_with_retries positional args.
        items = [
            (notebook, kernel_name, cell_timeout, startup_timeout,
             allow_errors, source.parent, retries, log_dir, source_root)
            for source, notebook in pairs
        ]
        max_pending = jobs * 2
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            try:
                for future, item in _bounded_as_completed(pool, _execute_with_retries, items, max_pending):
                    notebook = item[0]
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
            except KeyboardInterrupt:
                log.warning("Interrupted — cancelling remaining executions…")
                pool.shutdown(wait=False, cancel_futures=True)

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
        "-o", "--output", type=Path, default=None,
        help="Output directory (default: same as source — in-place)",
    )
    conv.add_argument(
        "-j", "--jobs", type=int, default=1,
        help="Number of parallel conversion workers (default: 1)",
    )
    conv.add_argument(
        "--convert-timeout", type=int, default=CONVERT_GIVE_UP_TIMEOUT,
        help=f"Per-file conversion timeout in seconds; 0=no limit (default: {CONVERT_GIVE_UP_TIMEOUT})",
    )
    conv.add_argument("--force", action="store_true", help="Convert even if up-to-date")
    conv.add_argument("-v", "--verbose", action="store_true")

    # -- execute --
    exe = sub.add_parser("execute", help="Execute certified notebooks through ACL2 kernel")
    exe.add_argument("source", type=Path, help="Root directory of ACL2 sources")
    exe.add_argument(
        "-o", "--output", type=Path, default=None,
        help="Output directory (default: same as source — in-place)",
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
    exe.add_argument(
        "--retries", type=int, default=DEFAULT_EXECUTE_RETRIES,
        help=f"Number of retries on execution failure (default: {DEFAULT_EXECUTE_RETRIES})",
    )
    exe.add_argument(
        "--log-dir", type=Path, default=DEFAULT_LOG_DIR,
        help="Directory for kernel log files (default: logs in source tree)",
    )
    exe.add_argument("--force", action="store_true", help="Re-execute even if up-to-date")
    exe.add_argument("-v", "--verbose", action="store_true")

    # -- all (convert + execute) --
    both = sub.add_parser("all", help="Convert then execute (both phases)")
    both.add_argument("source", type=Path, help="Root directory of ACL2 sources")
    both.add_argument(
        "-o", "--output", type=Path, default=None,
        help="Output directory (default: same as source — in-place)",
    )
    both.add_argument(
        "-j", "--jobs", type=int, default=1,
        help="Number of parallel execution workers (default: 1)",
    )
    both.add_argument(
        "--convert-timeout", type=int, default=CONVERT_GIVE_UP_TIMEOUT,
        help=f"Per-file conversion timeout in seconds; 0=no limit (default: {CONVERT_GIVE_UP_TIMEOUT})",
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
    both.add_argument(
        "--retries", type=int, default=DEFAULT_EXECUTE_RETRIES,
        help=f"Number of retries on execution failure (default: {DEFAULT_EXECUTE_RETRIES})",
    )
    both.add_argument(
        "--log-dir", type=Path, default=DEFAULT_LOG_DIR,
        help="Directory for kernel log files (default: logs in source tree)",
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
    output = (args.output or args.source).resolve()

    if not source.is_dir():
        log.error("Source %s is not a directory", source)
        return 1

    t0 = time.monotonic()
    total_errors = 0

    if args.command in ("convert", "all"):
        log.info("=== Phase 1: Convert ===")
        jobs = getattr(args, "jobs", 1)
        convert_timeout = getattr(args, "convert_timeout", CONVERT_GIVE_UP_TIMEOUT)
        converted, skipped, errors = phase_convert(
            source, output, args.force, jobs=jobs, convert_timeout=convert_timeout,
        )
        log.info("Convert done: %d converted, %d up-to-date, %d errors", converted, skipped, errors)
        total_errors += errors

    if args.command in ("execute", "all"):
        log.info("=== Phase 2: Execute ===")
        jobs = getattr(args, "jobs", 1)
        kernel = getattr(args, "kernel", "acl2")
        cell_timeout = getattr(args, "cell_timeout", DEFAULT_CELL_TIMEOUT)
        startup_timeout = getattr(args, "startup_timeout", DEFAULT_STARTUP_TIMEOUT)
        allow_errors = not getattr(args, "no_allow_errors", False)

        retries = getattr(args, "retries", DEFAULT_EXECUTE_RETRIES)
        log_dir = getattr(args, "log_dir", DEFAULT_LOG_DIR)

        executed, skipped, errors = phase_execute(
            source, output,
            jobs=jobs,
            kernel_name=kernel,
            cell_timeout=cell_timeout,
            startup_timeout=startup_timeout,
            allow_errors=allow_errors,
            force=args.force,
            retries=retries,
            log_dir=log_dir,
        )
        log.info("Execute done: %d executed, %d up-to-date, %d errors", executed, skipped, errors)
        total_errors += errors

    elapsed = time.monotonic() - t0
    log.info("Total time: %.1fs", elapsed)

    return 1 if total_errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
