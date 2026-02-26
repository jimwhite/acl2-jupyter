#!/usr/bin/env python3
"""Execute ACL2 boot-strap notebooks cell by cell against boot-strap kernels.

Replicates the ACL2 two-pass boot-strap (initialize-acl2) using the Jupyter
kernel in boot-strap mode.  Each .ipynb's code cells are executed one at a
time; the kernel emits per-cell display_data with events, forms and package
(MIME application/vnd.acl2.events+json).  Outputs are written back to the
notebook — no separate JSON files.

Usage:
    python -m script2notebook.build_boot_strap /home/acl2
    python -m script2notebook.build_boot_strap /home/acl2 --pass 1
    python -m script2notebook.build_boot_strap /home/acl2 --stem float-b
"""

import argparse
import json
import logging
import os
import sys
import tempfile
import time
from pathlib import Path

import nbformat
from jupyter_client.manager import KernelManager

log = logging.getLogger(__name__)

# ── File lists ───────────────────────────────────────────────────────────────
# These mirror *acl2-files* and *acl2-pass-2-files* from ACL2.
# We read them from the manifest if available, otherwise hardcode the
# canonical order.

# Canonical boot-strap file order (from ACL2's *acl2-files* / *acl2-pass-2-files*).
# These are the stems of .lisp / .ipynb files, in LD order.

PASS1_STEMS = [
    "axioms", "hons", "basis-a", "memoize", "serialize", "basis-b",
    "parallel", "float-a", "translate", "type-set-a", "linear-a",
    "type-set-b", "linear-b", "non-linear", "tau", "rewrite",
    "simplify", "bdd", "other-processes", "induct", "proof-builder-pkg",
    "doc", "history-management", "prove", "defuns", "proof-builder-a",
    "defthm", "other-events", "float-b", "ld", "proof-builder-b",
    "defpkgs", "apply-prim", "apply-constraints", "apply",
]

PASS2_STEMS = [
    "axioms", "memoize", "hons", "serialize",
    "boot-strap-pass-2-a",
    "float-a", "float-b", "apply-prim", "apply-constraints", "apply",
    "boot-strap-pass-2-b",
]


RAW_STEMS = [
    "apply-raw", "float-raw", "futures-raw", "hons-raw",
    "interface-raw", "memoize-raw", "multi-threading-raw",
    "parallel-raw", "serialize-raw",
]


def get_file_lists() -> tuple[list[str], list[str]]:
    """Return (pass1_stems, pass2_stems)."""
    return list(PASS1_STEMS), list(PASS2_STEMS)


def _is_raw_stem(stem: str) -> bool:
    """Return True for raw Common Lisp source stems (e.g. ``hons-raw``)."""
    return stem.endswith("-raw")


# ── Kernel management ───────────────────────────────────────────────────────

# Sentinel code sent to the kernel to trigger the pass-2 transition.
# Matched literally in kernel.lisp eval-cell.
PASS2_DIRECTIVE = ":bootstrap-enter-pass-2"


def make_kernel_json(acl2_home: Path, pass2_only: bool = False) -> dict:
    """Build a kernel.json spec for boot-strap mode.

    pass2_only=False (default): starts in pass 1 mode, build script drives
        both passes with PASS2_DIRECTIVE between them.
    pass2_only=True: runs pass 1 internally via ACL2's ld-fn during startup,
        kernel starts already in pass 2 state.
    """
    quicklisp = Path.home() / "quicklisp" / "setup.lisp"
    sbcl_home = os.environ.get("SBCL_HOME", "/usr/local/lib/sbcl/")
    start_fn = "start-boot-strap-pass2" if pass2_only else "start-boot-strap"
    display = "ACL2 Boot-strap Pass 2" if pass2_only else "ACL2 Boot-strap"
    
    return {
        "argv": [
            "/usr/local/bin/sbcl",
            "--tls-limit", "16384",
            "--dynamic-space-size", "32000",
            "--control-stack-size", "64",
            "--disable-ldb",
            "--end-runtime-options",
            "--no-userinit",
            "--disable-debugger",
            "--load", str(acl2_home / "init.lisp"),
            "--eval", "(acl2::load-acl2 :load-acl2-proclaims acl2::*do-proclaims*)",
            "--load", str(quicklisp),
            "--eval", "(ql:quickload :acl2-jupyter-kernel :silent t)",
            "--eval", f'(acl2-jupyter-kernel:{start_fn} "{{connection_file}}")',
        ],
        "display_name": display,
        "language": "acl2",
        "interrupt_mode": "message",
        "metadata": {},
        "env": {
            "SBCL_HOME": sbcl_home,
            "ACL2_JUPYTER_EXWORLD": "1",
        },
    }


def install_bootstrap_kernelspec(acl2_home: Path,
                                 pass2_only: bool = False) -> str:
    """Install a temporary kernelspec for boot-strap mode.
    
    Returns the kernel name.
    """
    from jupyter_client.kernelspec import KernelSpecManager
    
    kernel_name = "acl2-bootstrap-pass2" if pass2_only else "acl2-bootstrap"
    spec = make_kernel_json(acl2_home, pass2_only=pass2_only)
    
    with tempfile.TemporaryDirectory() as tmpdir:
        spec_dir = Path(tmpdir) / kernel_name
        spec_dir.mkdir()
        (spec_dir / "kernel.json").write_text(json.dumps(spec, indent=2))
        
        ksm = KernelSpecManager()
        ksm.install_kernel_spec(str(spec_dir), kernel_name, user=True)
    
    log.info("Installed kernelspec: %s", kernel_name)
    return kernel_name


def start_kernel(kernel_name: str, cwd: Path, startup_timeout: int = 600):
    """Start a kernel and return (manager, client).
    
    startup_timeout is generous because boot-strap init takes a while.
    """
    km = KernelManager(kernel_name=kernel_name)
    
    log.info("Starting kernel %s (this may take several minutes) ...", kernel_name)
    km.start_kernel(cwd=str(cwd))
    
    kc = km.client()
    kc.start_channels()
    
    # Wait for kernel to be ready
    log.info("Waiting for kernel ready (timeout=%ds) ...", startup_timeout)
    try:
        kc.wait_for_ready(timeout=startup_timeout)
    except Exception:
        log.error("Kernel failed to start within %ds", startup_timeout)
        km.shutdown_kernel(now=True)
        raise
    
    log.info("Kernel ready.")
    return km, kc


# ── Cell execution ───────────────────────────────────────────────────────────

EVENTS_MIME = "application/vnd.acl2.events+json"


def execute_cell(kc, cell, cell_idx: int, timeout: int = 300) -> list[dict]:
    """Execute a single cell and return its outputs.
    
    Returns a list of nbformat-compatible output dicts.
    """
    source = cell.source if isinstance(cell.source, str) else "".join(cell.source)
    if not source.strip():
        return []
    
    msg_id = kc.execute(source)
    outputs = []
    
    # Collect outputs until execute_reply
    while True:
        try:
            msg = kc.get_iopub_msg(timeout=timeout)
        except Exception:
            log.error("Timeout waiting for cell %d output", cell_idx)
            break
        
        msg_type = msg["header"]["msg_type"]
        parent_id = msg["parent_header"].get("msg_id", "")
        
        if parent_id != msg_id:
            continue
        
        content = msg["content"]
        
        if msg_type == "stream":
            outputs.append(nbformat.v4.new_output(
                output_type="stream",
                name=content.get("name", "stdout"),
                text=content.get("text", ""),
            ))
        elif msg_type == "display_data":
            data = content.get("data", {})
            metadata = content.get("metadata", {})
            outputs.append(nbformat.v4.new_output(
                output_type="display_data",
                data=data,
                metadata=metadata,
            ))
        elif msg_type == "execute_result":
            data = content.get("data", {})
            metadata = content.get("metadata", {})
            outputs.append(nbformat.v4.new_output(
                output_type="execute_result",
                data=data,
                metadata=metadata,
                execution_count=content.get("execution_count"),
            ))
        elif msg_type == "error":
            outputs.append(nbformat.v4.new_output(
                output_type="error",
                ename=content.get("ename", ""),
                evalue=content.get("evalue", ""),
                traceback=content.get("traceback", []),
            ))
        elif msg_type == "status":
            if content.get("execution_state") == "idle":
                break
    
    # Also wait for the execute_reply
    try:
        reply = kc.get_shell_msg(timeout=timeout)
        if reply["content"].get("status") == "error":
            log.warning("Cell %d execute_reply error: %s",
                       cell_idx, reply["content"].get("evalue", "?"))
    except Exception:
        log.warning("Timeout waiting for execute_reply on cell %d", cell_idx)
    
    return outputs


# ── Notebook execution ───────────────────────────────────────────────────────

def execute_notebook(kc, nb_path: Path, dry_run: bool = False,
                     cell_timeout: int = 300) -> nbformat.NotebookNode:
    """Execute all code cells in a notebook, collecting outputs.
    
    Returns the notebook with outputs populated.
    """
    nb = nbformat.read(str(nb_path), as_version=4)
    stem = nb_path.stem
    code_cells = [(i, c) for i, c in enumerate(nb.cells) if c.cell_type == "code"]
    
    log.info("  %s: %d code cells", stem, len(code_cells))
    
    if dry_run:
        return nb
    
    for ci, (nb_idx, cell) in enumerate(code_cells):
        source = cell.source if isinstance(cell.source, str) else "".join(cell.source)
        first_line = source.strip().split("\n")[0][:60] if source.strip() else "(empty)"
        
        log.debug("    cell %d/%d: %s", ci + 1, len(code_cells), first_line)
        
        outputs = execute_cell(kc, cell, ci, timeout=cell_timeout)
        cell.outputs = outputs
        
        # Count events in display_data
        for out in outputs:
            if out.output_type == "display_data":
                data = out.get("data", {})
                if EVENTS_MIME in data:
                    evts = data[EVENTS_MIME]
                    if isinstance(evts, dict):
                        n_events = len(evts.get("events", []))
                        log.debug("      → %d events", n_events)
    
    # Update notebook metadata
    nb.metadata.setdefault("kernelspec", {}).update({
        "display_name": "ACL2",
        "language": "acl2",
        "name": "acl2",
    })
    
    return nb


# ── Pass-2 transition ────────────────────────────────────────────────────────

def send_pass2_transition(kc, timeout: int = 60):
    """Send the pass-2 transition directive to the running kernel.
    
    This switches the kernel from pass 1 (ld-skip-proofsp = initialize-acl2)
    to pass 2 (ld-skip-proofsp = include-book, default-defun-mode = :logic).
    """
    log.info("=== Transitioning to pass 2 ===")
    msg_id = kc.execute(PASS2_DIRECTIVE)
    
    # Drain iopub until idle
    while True:
        try:
            msg = kc.get_iopub_msg(timeout=timeout)
        except Exception:
            raise RuntimeError("Timeout waiting for pass-2 transition")
        parent_id = msg["parent_header"].get("msg_id", "")
        if parent_id != msg_id:
            continue
        mt = msg["header"]["msg_type"]
        if mt == "stream":
            log.debug("  transition: %s", msg["content"].get("text", "").strip())
        if mt == "status" and msg["content"].get("execution_state") == "idle":
            break
    
    # Wait for execute_reply
    reply = kc.get_shell_msg(timeout=timeout)
    if reply["content"].get("status") == "error":
        raise RuntimeError(
            f"Pass-2 transition failed: {reply['content'].get('evalue', '?')}")
    
    log.info("Pass-2 transition complete.")


# ── Build orchestration ──────────────────────────────────────────────────────

def execute_pass(kc, pass_num: int, stems: list[str], acl2_home: Path,
                 dry_run: bool = False, cell_timeout: int = 300,
                 only_stem: str | None = None):
    """Execute all notebooks for one pass (without managing the kernel)."""
    if only_stem:
        if only_stem not in stems:
            log.warning("Stem %r not in pass %d file list — skipping pass",
                       only_stem, pass_num)
            return
        stems = stems[: stems.index(only_stem) + 1]
    
    log.info("=== Pass %d: %d notebooks ===", pass_num, len(stems))
    
    for i, stem in enumerate(stems):
        nb_path = acl2_home / f"{stem}.ipynb"
        if not nb_path.exists():
            log.warning("  SKIP %s: no .ipynb found", stem)
            continue
        
        log.info("[%d/%d] %s", i + 1, len(stems), stem)
        t0 = time.time()
        
        nb = execute_notebook(kc, nb_path, dry_run=dry_run,
                              cell_timeout=cell_timeout)
        
        elapsed = time.time() - t0
        
        if not dry_run:
            nbformat.write(nb, str(nb_path))
            log.info("  %s: done (%.1fs)", stem, elapsed)
        else:
            log.info("  %s: would execute %d code cells",
                    stem,
                    sum(1 for c in nb.cells if c.cell_type == "code"))


# ── Pass-1 metadata injection ────────────────────────────────────────────────

PASS1_EVENTS_DIR = Path("/tmp/pass1-events")


def inject_pass1_metadata(pass1_stems: list[str], acl2_home: Path):
    """Inject pass-1 event metadata into pass-1-only notebooks.
    
    For each stem, reads the per-file JSON written by the kernel's
    write-pass1-file-events, and injects the events as a display_data
    output on the notebook's metadata (notebook-level, not per-cell).
    For stems that are also in pass 2, pass-2 execution already
    captured per-cell metadata so we skip those.
    """
    pass2_set = set(PASS2_STEMS)
    injected = 0
    
    for stem in pass1_stems:
        json_path = PASS1_EVENTS_DIR / f"{stem}.json"
        nb_path = acl2_home / f"{stem}.ipynb"
        
        if not json_path.exists():
            log.debug("  No pass-1 metadata for %s", stem)
            continue
        if not nb_path.exists():
            continue
        
        try:
            with open(json_path) as f:
                meta = json.load(f)
        except Exception as e:
            log.warning("  Failed to read %s: %s", json_path, e)
            continue
        
        n_events = meta.get("event_count", len(meta.get("events", [])))
        if n_events == 0:
            log.debug("  %s: 0 events, skipping", stem)
            continue
        
        nb = nbformat.read(str(nb_path), as_version=4)
        
        # Build the events output matching the pass-2 cell metadata format
        events_data = {
            "events": meta.get("events", []),
            "package": meta.get("package", "ACL2"),
        }
        if meta.get("forms"):
            events_data["forms"] = meta["forms"]
        
        # Check if notebook already has pass-1 metadata injected
        # (from a previous run) — look for a cell with our marker
        marker = "pass-1-metadata"
        existing_idx = None
        for i, cell in enumerate(nb.cells):
            if cell.cell_type == "code" and cell.source.strip() == f"; {marker}":
                existing_idx = i
                break
        
        # Create a synthetic code cell with the metadata as output
        metadata_cell = nbformat.v4.new_code_cell(source=f"; {marker}")
        metadata_cell.outputs = [nbformat.v4.new_output(
            output_type="display_data",
            data={
                EVENTS_MIME: events_data,
                "text/plain": (
                    f"Pass 1 metadata: {n_events} events"
                    f" (package: {meta.get('package', 'ACL2')})"
                ),
            },
            metadata={"pass": 1},
        )]
        
        if existing_idx is not None:
            nb.cells[existing_idx] = metadata_cell
        else:
            nb.cells.append(metadata_cell)
        
        nbformat.write(nb, str(nb_path))
        in_pass2 = " (also in pass 2)" if stem in pass2_set else ""
        log.info("  %s: injected %d pass-1 events%s", stem, n_events, in_pass2)
        injected += 1
    
    log.info("Injected pass-1 metadata into %d notebooks.", injected)


# ── Source-only enrichment (symbols + deps via :analyze-source) ──────────────

def _analyze_cell_source(kc, source: str, cl_mode: bool = False,
                         timeout: int = 60) -> list[dict]:
    """Send source text to the kernel for analysis and return outputs.

    Uses ``:analyze-source`` (ACL2 readtable) or ``:analyze-source-cl``
    (standard CL readtable) directives.  The kernel reads the source,
    extracts symbols/deps against the current world, and emits
    display_data without evaluating any code.
    """
    directive = ":analyze-source-cl " if cl_mode else ":analyze-source "
    return execute_cell(kc, type("C", (), {"source": directive + source})(),
                        cell_idx=0, timeout=timeout)


def _extract_events_mime(outputs: list[dict]) -> dict | None:
    """Find and return the events MIME payload from cell outputs."""
    for out in outputs:
        if out.get("output_type") == "display_data":
            data = out.get("data", {})
            if EVENTS_MIME in data:
                return data[EVENTS_MIME]
    return None


def _merge_events_payload(base: dict, extra: dict) -> dict:
    """Merge *extra* keys into *base*, preferring *extra* for non-empty values."""
    merged = dict(base)
    for key in ("symbols", "dependencies"):
        if key in extra and extra[key]:
            merged[key] = extra[key]
    return merged


def enrich_pass1_notebooks(kc, pass1_stems: list[str], acl2_home: Path,
                           dry_run: bool = False):
    """Enrich pass-1 notebooks with per-cell symbols, deps, and events.

    For each pass-1-only notebook (not in pass 2):
    1. Distribute per-file events to individual cells using event_matching.
    2. Send each cell's source via ``:analyze-source`` to extract symbols/deps.
    3. Merge events + symbols + deps into per-cell display_data outputs.
    4. Remove the old ``; pass-1-metadata`` summary cell if present.

    Must be called while the kernel is still alive (post-pass-2 world).
    """
    from .event_matching import match_events_to_cells

    pass2_set = set(PASS2_STEMS)
    enriched = 0

    for stem in pass1_stems:
        if stem in pass2_set:
            # Pass-2 execution already captured per-cell metadata.
            continue

        nb_path = acl2_home / f"{stem}.ipynb"
        if not nb_path.exists():
            continue

        nb = nbformat.read(str(nb_path), as_version=4)
        code_cells = [(i, c) for i, c in enumerate(nb.cells)
                      if c.cell_type == "code"
                      and c.source.strip() != "; pass-1-metadata"]

        if not code_cells:
            continue

        # --- Event distribution from pass-1 JSON ---
        json_path = PASS1_EVENTS_DIR / f"{stem}.json"
        file_events: list[str] = []
        file_forms: list[str] | None = None
        file_package: str = "ACL2"

        if json_path.exists():
            try:
                with open(json_path) as f:
                    meta = json.load(f)
                file_events = meta.get("events", [])
                file_forms = meta.get("forms") or None
                file_package = meta.get("package", "ACL2")
            except Exception as e:
                log.warning("  %s: failed to read pass-1 JSON: %s", stem, e)

        # Build dicts for match_events_to_cells (needs list[dict] with "source")
        cell_dicts = []
        for _, cell in code_cells:
            src = cell.source if isinstance(cell.source, str) else "".join(cell.source)
            cell_dicts.append({"source": src, "cell_type": "code"})

        per_cell_events: list[list[str]] = [[] for _ in code_cells]
        per_cell_forms: list[list[str]] = [[] for _ in code_cells]

        if file_events:
            result = match_events_to_cells(file_events, cell_dicts,
                                           forms=file_forms)
            if file_forms is not None:
                per_cell_events, per_cell_forms = result
            else:
                per_cell_events = result

        log.info("  %s: enriching %d code cells (%d events to distribute)",
                 stem, len(code_cells), len(file_events))

        if dry_run:
            continue

        # --- Per-cell symbol/dep extraction via :analyze-source ---
        for ci, (nb_idx, cell) in enumerate(code_cells):
            src = cell.source if isinstance(cell.source, str) else "".join(cell.source)
            if not src.strip():
                continue

            # Get symbols/deps from kernel
            analysis_outputs = _analyze_cell_source(kc, src, cl_mode=False)
            analysis_payload = _extract_events_mime(analysis_outputs)

            # Build per-cell metadata
            cell_meta = {
                "events": per_cell_events[ci],
                "package": file_package,
            }
            if per_cell_forms[ci]:
                cell_meta["forms"] = per_cell_forms[ci]

            # Merge in symbols/deps from analysis
            if analysis_payload:
                cell_meta = _merge_events_payload(cell_meta, analysis_payload)

            # Set cell outputs
            n_events = len(per_cell_events[ci])
            n_symbols = len(cell_meta.get("symbols", []))
            cell.outputs = [nbformat.v4.new_output(
                output_type="display_data",
                data={
                    EVENTS_MIME: cell_meta,
                    "text/plain": (
                        f"{n_events} events, {n_symbols} symbols"
                        f" (pass 1, {file_package})"
                    ),
                },
                metadata={"pass": 1},
            )]

        # Remove old pass-1-metadata summary cell if present
        nb.cells = [c for c in nb.cells
                     if not (c.cell_type == "code"
                             and c.source.strip() == "; pass-1-metadata")]

        nbformat.write(nb, str(nb_path))
        enriched += 1

    log.info("Enriched %d pass-1 notebooks with per-cell metadata.", enriched)


def enrich_raw_notebooks(kc, acl2_home: Path, dry_run: bool = False):
    """Enrich raw CL notebooks with per-cell symbols and deps.

    For each ``*-raw.ipynb`` notebook:
    1. Send each cell's source via ``:analyze-source-cl`` (CL readtable).
    2. Write symbols/deps as display_data outputs.
    3. Fix notebook language tag from ``acl2`` to ``common-lisp``.

    Must be called while the kernel is still alive (post-pass-2 world).
    """
    enriched = 0

    for stem in RAW_STEMS:
        nb_path = acl2_home / f"{stem}.ipynb"
        if not nb_path.exists():
            log.debug("  SKIP %s: no .ipynb found", stem)
            continue

        nb = nbformat.read(str(nb_path), as_version=4)
        code_cells = [(i, c) for i, c in enumerate(nb.cells)
                      if c.cell_type == "code"]
        if not code_cells:
            continue

        log.info("  %s: enriching %d code cells (raw CL)", stem, len(code_cells))

        if dry_run:
            continue

        for ci, (nb_idx, cell) in enumerate(code_cells):
            src = cell.source if isinstance(cell.source, str) else "".join(cell.source)
            if not src.strip():
                continue

            # Get symbols/deps from kernel using CL readtable
            analysis_outputs = _analyze_cell_source(kc, src, cl_mode=True)
            analysis_payload = _extract_events_mime(analysis_outputs)

            if analysis_payload:
                n_symbols = len(analysis_payload.get("symbols", []))
                cell.outputs = [nbformat.v4.new_output(
                    output_type="display_data",
                    data={
                        EVENTS_MIME: analysis_payload,
                        "text/plain": (
                            f"{n_symbols} symbols (raw CL)"
                        ),
                    },
                    metadata={"source_type": "raw_common_lisp"},
                )]

        # Fix language tag: raw CL files should be common-lisp, not acl2
        nb.metadata.setdefault("kernelspec", {}).update({
            "display_name": "Common Lisp",
            "language": "common-lisp",
            "name": "common-lisp",
        })
        if "language_info" in nb.metadata:
            nb.metadata["language_info"]["name"] = "common-lisp"

        nbformat.write(nb, str(nb_path))
        enriched += 1

    log.info("Enriched %d raw CL notebooks with per-cell metadata.", enriched)


# ── Build orchestration ──────────────────────────────────────────────────────

def run_build(pass1_stems: list[str], pass2_stems: list[str],
              acl2_home: Path, dry_run: bool = False,
              cell_timeout: int = 300, only_stem: str | None = None,
              pass_num: int | None = None, pass2_only: bool = False,
              startup_timeout: int = 600):
    """Run the bootstrap build with a single kernel.
    
    --pass2-only: pass 1 runs inside the kernel via ld-fn, only pass 2
        notebooks are executed.  Kernel startup is slower but avoids
        *1* function errors.
    --pass 1: pass 1 only (original bootstrap kernel)
    --pass 2: pass 1 + transition + pass 2 (original bootstrap kernel)
    No --pass: same as --pass 2 (full build)
    """
    do_pass2 = (pass_num is None or pass_num == 2 or pass2_only)
    
    # Install kernelspec and start kernel
    kernel_name = install_bootstrap_kernelspec(acl2_home,
                                               pass2_only=pass2_only)
    # Pass-2-only startup is slower (runs pass 1 via ld-fn internally)
    actual_timeout = max(startup_timeout, 1200) if pass2_only else startup_timeout
    km, kc = start_kernel(kernel_name, cwd=acl2_home,
                          startup_timeout=actual_timeout)
    
    try:
        if not pass2_only:
            # Pass 1 via our REPL
            execute_pass(kc, 1, pass1_stems, acl2_home,
                         dry_run=dry_run, cell_timeout=cell_timeout,
                         only_stem=only_stem if not do_pass2 else None)
        
        # Transition + Pass 2
        if do_pass2:
            if not pass2_only and not dry_run:
                send_pass2_transition(kc)
            
            execute_pass(kc, 2, pass2_stems, acl2_home,
                         dry_run=dry_run, cell_timeout=cell_timeout,
                         only_stem=only_stem)
        
        # ── Enrichment phases (kernel must be alive with post-pass-2 world) ──
        if do_pass2 and not dry_run:
            log.info("=== Enrichment: pass-1 notebooks ===")
            enrich_pass1_notebooks(kc, pass1_stems, acl2_home)
            
            log.info("=== Enrichment: raw CL notebooks ===")
            enrich_raw_notebooks(kc, acl2_home)
    
    except KeyboardInterrupt:
        log.warning("Interrupted! Shutting down kernel ...")
    finally:
        log.info("Shutting down kernel ...")
        kc.stop_channels()
        km.shutdown_kernel(now=False)
        try:
            km.cleanup_resources()
        except Exception:
            pass
    
    # Legacy fallback: inject pass-1 summary if enrichment didn't run.
    # Enrichment requires the post-pass-2 world (do_pass2 && !dry_run);
    # when only pass 1 was executed we still have the per-file JSONs.
    if not do_pass2 and not dry_run:
        inject_pass1_metadata(pass1_stems, acl2_home)


def main():
    parser = argparse.ArgumentParser(
        description="Build ACL2 boot-strap notebooks by executing cells "
                    "against a single boot-strap kernel.",
    )
    parser.add_argument(
        "acl2_home", type=Path,
        help="ACL2 source directory containing .ipynb files",
    )
    parser.add_argument(
        "--pass", dest="pass_num", type=int, choices=[1, 2], default=None,
        help="1=pass 1 only, 2=full build (default: full build)",
    )
    parser.add_argument(
        "--stem", type=str, default=None,
        help="Run only up to and including this stem (for debugging)",
    )
    parser.add_argument(
        "--pass2-only", action="store_true",
        help="Pass-2-only mode: pass 1 runs via ld-fn during kernel startup, "
             "only pass-2 notebooks are executed through the REPL. "
             "Avoids *1* function errors from the simplified bootstrap REPL.",
    )
    parser.add_argument(
        "--cell-timeout", type=int, default=300,
        help="Timeout per cell in seconds (default: 300)",
    )
    parser.add_argument(
        "--startup-timeout", type=int, default=600,
        help="Timeout for kernel startup in seconds (default: 600, "
             "pass2-only uses at least 1200)",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="List notebooks and cells without executing",
    )
    parser.add_argument(
        "-v", "--verbose", action="store_true",
        help="Verbose output",
    )
    args = parser.parse_args()
    
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)-5s %(message)s",
        datefmt="%H:%M:%S",
    )
    
    acl2_home = args.acl2_home.resolve()
    if not (acl2_home / "init.lisp").exists():
        log.error("Cannot find init.lisp in %s", acl2_home)
        sys.exit(1)
    
    pass1_stems, pass2_stems = get_file_lists()
    
    run_build(pass1_stems, pass2_stems, acl2_home,
              dry_run=args.dry_run, cell_timeout=args.cell_timeout,
              only_stem=args.stem, pass_num=args.pass_num,
              pass2_only=args.pass2_only,
              startup_timeout=args.startup_timeout)
    
    log.info("Build complete.")


if __name__ == "__main__":
    main()