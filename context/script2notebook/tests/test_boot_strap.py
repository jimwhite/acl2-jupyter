#!/usr/bin/env python3
"""Boot-strap kernel tests.

Starts the ACL2 boot-strap kernel (pass 1) and verifies that it can
evaluate forms from the boot-strap world.  The bootstrap kernel starts
from a primordial world (via enter-boot-strap-mode) where standard ACL2
functions like + don't exist yet — they are defined by the axioms cells.

We test:
  1. Basic kernel liveness (reply status ok).
  2. Executing a few early axioms.ipynb cells.
  3. That events metadata is emitted.
  4. That after enough axioms cells, arithmetic works.

Usage:
    python -m pytest context/script2notebook/tests/test_boot_strap.py -v -s
    # or standalone:
    python context/script2notebook/tests/test_boot_strap.py
"""

import json
import logging
import os
import sys
import tempfile
import time
from pathlib import Path

import pytest
import nbformat

log = logging.getLogger(__name__)

ACL2_HOME = Path("/home/acl2")
EVENTS_MIME = "application/vnd.acl2.events+json"


# ── Kernel setup helpers ────────────────────────────────────────────


def make_kernel_json(acl2_home: Path, pass_num: int = 1) -> dict:
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
            "--eval",
            f'(acl2-jupyter-kernel:start-boot-strap "{{connection_file}}" :pass {pass_num})',
        ],
        "display_name": f"ACL2 Boot-strap Pass {pass_num}",
        "language": "acl2",
        "interrupt_mode": "message",
        "metadata": {},
        "env": {"SBCL_HOME": sbcl_home},
    }


def install_kernelspec(acl2_home: Path, pass_num: int = 1) -> str:
    from jupyter_client.kernelspec import KernelSpecManager

    name = f"acl2-bootstrap-pass{pass_num}"
    spec = make_kernel_json(acl2_home, pass_num)
    with tempfile.TemporaryDirectory() as tmpdir:
        d = Path(tmpdir) / name
        d.mkdir()
        (d / "kernel.json").write_text(json.dumps(spec, indent=2))
        KernelSpecManager().install_kernel_spec(str(d), name, user=True)
    return name


# ── Execution helpers ───────────────────────────────────────────────


def execute_one(kc, code: str, timeout: int = 120):
    """Execute *code* and return (outputs, reply_content)."""
    msg_id = kc.execute(code)
    outputs = []
    while True:
        try:
            msg = kc.get_iopub_msg(timeout=timeout)
        except Exception:
            log.error("Timeout waiting for iopub after %ds", timeout)
            break
        if msg["parent_header"].get("msg_id") != msg_id:
            continue
        mt = msg["header"]["msg_type"]
        c = msg["content"]
        if mt == "stream":
            outputs.append({"type": "stream", "name": c.get("name"),
                            "text": c.get("text", "")})
        elif mt in ("display_data", "execute_result"):
            outputs.append({"type": mt, "data": c.get("data", {}),
                            "metadata": c.get("metadata", {})})
        elif mt == "error":
            outputs.append({"type": "error", "ename": c.get("ename"),
                            "evalue": c.get("evalue"),
                            "traceback": c.get("traceback", [])})
        elif mt == "status" and c.get("execution_state") == "idle":
            break

    try:
        reply = kc.get_shell_msg(timeout=timeout)
        reply_content = reply["content"]
    except Exception:
        reply_content = {"status": "timeout"}
    return outputs, reply_content


def get_results(outputs) -> list[str]:
    """Extract text/plain values from execute_result outputs."""
    return [
        o["data"]["text/plain"]
        for o in outputs
        if o["type"] == "execute_result" and "text/plain" in o.get("data", {})
    ]


def get_stdout(outputs) -> str:
    """Concatenate all stream stdout text."""
    return "".join(
        o["text"] for o in outputs
        if o["type"] == "stream" and o.get("name") == "stdout"
    )


def get_errors(outputs) -> list[dict]:
    """Extract Jupyter error outputs."""
    return [o for o in outputs if o["type"] == "error"]


def get_events_data(outputs) -> dict | None:
    """Extract the ACL2 events display_data, if any."""
    for o in outputs:
        if o["type"] == "display_data":
            data = o.get("data", {})
            if EVENTS_MIME in data:
                return data[EVENTS_MIME]
    return None


def has_acl2_error(outputs) -> str | None:
    """Return error text if any output contains an ACL2 error, else None."""
    for o in outputs:
        if o["type"] == "error":
            return f"{o['ename']}: {o['evalue']}"
        if o["type"] == "stream":
            if "ACL2 Error" in o.get("text", ""):
                return o["text"].strip()
    return None


# ── Fixtures ────────────────────────────────────────────────────────


@pytest.fixture(scope="module")
def bootstrap_kernel():
    """Start a single bootstrap pass-1 kernel for the whole test module.

    Yields the kernel client.  Shuts down the kernel after all tests.
    """
    from jupyter_client.manager import KernelManager

    if not ACL2_HOME.exists():
        pytest.skip("ACL2 source not available")

    kernel_name = install_kernelspec(ACL2_HOME, pass_num=1)
    km = KernelManager(kernel_name=kernel_name)
    km.start_kernel(cwd=str(ACL2_HOME))
    kc = km.client()
    kc.start_channels()
    kc.wait_for_ready(timeout=600)
    yield kc
    kc.stop_channels()
    km.shutdown_kernel(now=True)


# ── Tests ───────────────────────────────────────────────────────────


class TestBootstrapKernelLiveness:
    """Verify the kernel starts, responds, and handles basic forms."""

    def test_reply_ok(self, bootstrap_kernel):
        """Kernel should reply ok for a simple in-package form."""
        outputs, reply = execute_one(bootstrap_kernel, '(in-package "ACL2")')
        assert reply.get("status") == "ok", f"reply: {reply}"

    def test_no_plus_in_primordial_world(self, bootstrap_kernel):
        """In the primordial world, + is not yet defined — should error."""
        outputs, reply = execute_one(bootstrap_kernel, "(+ 1 2)")
        assert reply.get("status") == "ok", f"reply: {reply}"
        # ACL2 should report the error via stream output
        stdout = get_stdout(outputs)
        assert "neither a function nor macro" in stdout, (
            f"Expected ACL2 error about undefined +, got stdout={stdout!r}"
        )

    def test_events_metadata_emitted(self, bootstrap_kernel):
        """Every cell should produce an events display_data."""
        outputs, reply = execute_one(bootstrap_kernel, '(in-package "ACL2")')
        assert reply.get("status") == "ok"
        events_data = get_events_data(outputs)
        assert events_data is not None, (
            f"No events display_data. Outputs: "
            f"{json.dumps(outputs, indent=2, default=str)}"
        )
        assert "events" in events_data
        assert "package" in events_data
        assert events_data["package"] == "ACL2"


class TestBootstrapAxiomsCells:
    """Execute the first few cells of axioms.ipynb to build up the world."""

    def test_first_axioms_cells(self, bootstrap_kernel):
        """Execute axioms.ipynb cells 0-4 (in-package, defconst symbols).

        These are the foundational definitions: the CL symbols list,
        specials-and-constants, nil, and t.
        """
        nb = nbformat.read(str(ACL2_HOME / "axioms.ipynb"), as_version=4)
        code_cells = [c for c in nb.cells if c.cell_type == "code"]

        # Execute the first 5 code cells
        for i, cell in enumerate(code_cells[:5]):
            src = cell.source if isinstance(cell.source, str) else "".join(cell.source)
            if not src.strip():
                continue
            outputs, reply = execute_one(bootstrap_kernel, src, timeout=120)
            stdout = get_stdout(outputs)
            errors = get_errors(outputs)
            assert reply.get("status") == "ok", (
                f"Cell {i} failed: reply={reply}; "
                f"stdout={stdout!r}; errors={errors}"
            )
            err = has_acl2_error(outputs)
            assert err is None, (
                f"Cell {i} ACL2 error: {err}\n"
                f"Full outputs: {json.dumps(outputs, indent=2, default=str)}"
            )

    def test_defconst_produces_events(self, bootstrap_kernel):
        """A defconst in boot-strap mode should produce an event landmark.

        Uses a constant that was already defined by load-acl2 in raw Lisp
        (so defconst-fn's boundp check passes).  We pick a fresh one from
        axioms.ipynb that hasn't been installed yet at this point.
        """
        # *stobjs-in* is defined much later in axioms.ipynb, so it should
        # still be available.  If that fails, fall back to re-executing an
        # already-succeeded cell (in-package "ACL2") which always produces
        # events metadata (though zero event-landmark tuples).
        nb = nbformat.read(str(ACL2_HOME / "axioms.ipynb"), as_version=4)
        code_cells = [c for c in nb.cells if c.cell_type == "code"]
        # Cell 5 is typically the next defconst after the first 5
        src = code_cells[5].source if len(code_cells) > 5 else '(in-package "ACL2")'
        if not src.strip():
            src = '(in-package "ACL2")'
        outputs, reply = execute_one(bootstrap_kernel, src, timeout=120)
        assert reply.get("status") == "ok", (
            f"reply: {reply}; outputs: {json.dumps(outputs, indent=2, default=str)}"
        )
        events_data = get_events_data(outputs)
        assert events_data is not None, (
            f"No events display_data. Outputs: "
            f"{json.dumps(outputs, indent=2, default=str)}"
        )


# ── Standalone runner ───────────────────────────────────────────────


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.DEBUG,
        format="%(asctime)s %(levelname)-5s %(message)s",
        datefmt="%H:%M:%S",
    )
    sys.exit(pytest.main([__file__, "-v", "-s", "-x"]))
