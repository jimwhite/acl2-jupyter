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


def get_file_lists() -> tuple[list[str], list[str]]:
    """Return (pass1_stems, pass2_stems)."""
    return list(PASS1_STEMS), list(PASS2_STEMS)


# ── Kernel management ───────────────────────────────────────────────────────


def make_kernel_json(pass_num: int, acl2_home: Path) -> dict:
    """Build a kernel.json spec for boot-strap mode."""
    quicklisp = Path.home() / "quicklisp" / "setup.lisp"
    sbcl_home = os.environ.get("SBCL_HOME", "/usr/local/lib/sbcl/")
    
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
            "--eval", f'(acl2-jupyter-kernel:start-boot-strap "{{connection_file}}" :pass {pass_num})',
        ],
        "display_name": f"ACL2 Boot-strap Pass {pass_num}",
        "language": "acl2",
        "interrupt_mode": "message",
        "metadata": {},
        "env": {
            "SBCL_HOME": sbcl_home,
        },
    }


def install_bootstrap_kernelspec(pass_num: int, acl2_home: Path) -> str:
    """Install a temporary kernelspec for boot-strap mode.
    
    Returns the kernel name.
    """
    from jupyter_client.kernelspec import KernelSpecManager
    
    kernel_name = f"acl2-bootstrap-pass{pass_num}"
    spec = make_kernel_json(pass_num, acl2_home)
    
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


# ── Main ─────────────────────────────────────────────────────────────────────

def run_pass(pass_num: int, stems: list[str], acl2_home: Path,
             dry_run: bool = False, cell_timeout: int = 300,
             only_stem: str | None = None):
    """Run one pass of the boot-strap build."""
    if only_stem:
        if only_stem not in stems:
            log.warning("Stem %r not in pass %d file list — skipping pass", only_stem, pass_num)
            return
        # Execute all files up to and including the target
        stems = stems[: stems.index(only_stem) + 1]

    log.info("=== Pass %d: %d notebooks ===", pass_num, len(stems))
    
    # Install kernelspec
    kernel_name = install_bootstrap_kernelspec(pass_num, acl2_home)
    
    # Start kernel
    km, kc = start_kernel(kernel_name, cwd=acl2_home)
    
    try:
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
                # Write notebook with outputs
                nbformat.write(nb, str(nb_path))
                log.info("  %s: done (%.1fs)", stem, elapsed)
            else:
                log.info("  %s: would execute %d code cells",
                        stem,
                        sum(1 for c in nb.cells if c.cell_type == "code"))
    
    except KeyboardInterrupt:
        log.warning("Interrupted! Shutting down kernel ...")
    finally:
        log.info("Shutting down kernel ...")
        kc.stop_channels()
        km.shutdown_kernel(now=False)
        # Give it a moment, then force
        try:
            km.cleanup_resources()
        except Exception:
            pass


def main():
    parser = argparse.ArgumentParser(
        description="Build ACL2 boot-strap notebooks by executing cells "
                    "against boot-strap kernels.",
    )
    parser.add_argument(
        "acl2_home", type=Path,
        help="ACL2 source directory containing .ipynb files",
    )
    parser.add_argument(
        "--pass", dest="pass_num", type=int, choices=[1, 2], default=None,
        help="Run only pass 1 or pass 2 (default: both)",
    )
    parser.add_argument(
        "--stem", type=str, default=None,
        help="Run only up to and including this stem (for debugging)",
    )
    parser.add_argument(
        "--cell-timeout", type=int, default=300,
        help="Timeout per cell in seconds (default: 300)",
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
    
    if args.pass_num is None or args.pass_num == 1:
        run_pass(1, pass1_stems, acl2_home,
                dry_run=args.dry_run, cell_timeout=args.cell_timeout,
                only_stem=args.stem)
    
    if args.pass_num is None or args.pass_num == 2:
        run_pass(2, pass2_stems, acl2_home,
                dry_run=args.dry_run, cell_timeout=args.cell_timeout,
                only_stem=args.stem)
    
    log.info("Build complete.")


if __name__ == "__main__":
    main()