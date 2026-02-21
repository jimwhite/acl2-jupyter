"""Tests for build_notebooks portcullis / eval-port-file injection helpers."""

import json
import pytest
from pathlib import Path

from script2notebook.build_notebooks import (
    _inject_port_file_cell,
    _acl2_companion_files,
)


# ── _acl2_companion_files ───────────────────────────────────────────

class TestAcl2CompanionFiles:
    def test_no_companions(self, tmp_path):
        src = tmp_path / "book.lisp"
        src.write_text("")
        assert _acl2_companion_files(src) == []

    def test_both_companions(self, tmp_path):
        src = tmp_path / "book.lisp"
        src.write_text("")
        (tmp_path / "cert.acl2").write_text("; cert\n")
        (tmp_path / "book.acl2").write_text("; book\n")
        companions = _acl2_companion_files(src)
        names = [name for name, _ in companions]
        assert "cert.acl2" in names
        assert "book.acl2" in names

    def test_cert_only(self, tmp_path):
        src = tmp_path / "book.lisp"
        src.write_text("")
        (tmp_path / "cert.acl2").write_text("; cert\n")
        companions = _acl2_companion_files(src)
        assert len(companions) == 1
        assert companions[0][0] == "cert.acl2"



# ── _inject_port_file_cell ───────────────────────────────────────────

def _make_notebook(tmp_path, name="book", cells=None, source_file=None):
    """Create a minimal notebook and matching source file."""
    if cells is None:
        cells = [
            {
                "cell_type": "code",
                "metadata": {},
                "source": ['(in-package "DM")\n'],
                "execution_count": None,
                "outputs": [],
                "id": "cell1",
            }
        ]
    metadata = {"kernelspec": {"name": "acl2"}}
    if source_file:
        metadata["source_file"] = source_file
    nb = {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": metadata,
        "cells": cells,
    }
    nb_path = tmp_path / f"{name}.ipynb"
    nb_path.write_text(json.dumps(nb, indent=1) + "\n")
    src_path = tmp_path / f"{name}.lisp"
    return nb_path, src_path, nb


class TestInjectPortFileCell:
    def test_no_injection_without_port_file(self, tmp_path):
        """No .port file → no injection."""
        nb_path, src_path, _ = _make_notebook(tmp_path)
        src_path.write_text('(in-package "ACL2")\n')
        result = _inject_port_file_cell(nb_path, src_path)
        assert result is False

    def test_inject_when_port_exists(self, tmp_path):
        """When .port file exists, inject eval-port-file cell."""
        nb_path, src_path, _ = _make_notebook(tmp_path)
        src_path.write_text('(in-package "DM")\n')
        # Create a .port file (content doesn't matter for the test).
        port_path = src_path.with_suffix(".port")
        port_path.write_bytes(b"(port file content)")

        result = _inject_port_file_cell(nb_path, src_path)
        assert result is True

        nb = json.loads(nb_path.read_text())
        assert len(nb["cells"]) == 2  # injected + original
        injected = nb["cells"][0]
        assert injected["cell_type"] == "code"
        assert injected["metadata"]["provenance"]["portcullis"] is True
        # The cell should call eval-port-file with the absolute source path.
        source_text = "".join(injected["source"])
        assert "eval-port-file" in source_text
        assert str(src_path.resolve()) in source_text
        # Original cell still last.
        assert nb["cells"][1]["id"] == "cell1"

    def test_no_double_injection(self, tmp_path):
        """Second call should return False and not add more cells."""
        nb_path, src_path, _ = _make_notebook(tmp_path)
        src_path.write_text('(in-package "ACL2")\n')
        src_path.with_suffix(".port").write_bytes(b"(port)")

        _inject_port_file_cell(nb_path, src_path)
        nb_before = json.loads(nb_path.read_text())
        n_cells_before = len(nb_before["cells"])

        result = _inject_port_file_cell(nb_path, src_path)
        assert result is False
        nb_after = json.loads(nb_path.read_text())
        assert len(nb_after["cells"]) == n_cells_before

    def test_invalid_notebook_json(self, tmp_path):
        """Gracefully handle invalid JSON in notebook file."""
        src_path = tmp_path / "book.lisp"
        src_path.write_text("")
        src_path.with_suffix(".port").write_bytes(b"(port)")
        nb_path = tmp_path / "book.ipynb"
        nb_path.write_text("not valid json")
        result = _inject_port_file_cell(nb_path, src_path)
        assert result is False

    def test_cell_uses_absolute_path(self, tmp_path):
        """The eval-port-file call must use an absolute path."""
        nb_path, src_path, _ = _make_notebook(tmp_path)
        src_path.write_text('(in-package "ACL2")\n')
        src_path.with_suffix(".port").write_bytes(b"(port)")

        _inject_port_file_cell(nb_path, src_path)
        nb = json.loads(nb_path.read_text())
        source_text = "".join(nb["cells"][0]["source"])
        # Path in the cell should be absolute.
        assert '/"' not in source_text or source_text.count("/") >= 2
        resolved = str(src_path.resolve())
        assert resolved in source_text
