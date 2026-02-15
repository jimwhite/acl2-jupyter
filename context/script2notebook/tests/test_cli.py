"""Tests for script2notebook.cli."""

import json
import pytest

from script2notebook.cli import main


class TestCLI:
    def test_help(self, capsys):
        with pytest.raises(SystemExit, match="0"):
            main(["--help"])

    def test_missing_file(self, capsys):
        ret = main(["/nonexistent/file.lisp"])
        assert ret == 1

    def test_unsupported_extension(self, tmp_path, capsys):
        p = tmp_path / "test.py"
        p.write_text("print('hello')")
        ret = main([str(p)])
        assert ret == 1

    def test_basic_conversion(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")  # blank → detached
        out = tmp_path / "test.ipynb"
        ret = main([str(p), "-o", str(out)])
        assert ret == 0
        assert out.exists()
        nb = json.loads(out.read_text())
        assert len(nb["cells"]) == 2

    def test_basic_conversion_attached(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n(foo)\n")  # no blank → attached
        out = tmp_path / "test.ipynb"
        ret = main([str(p), "-o", str(out)])
        assert ret == 0
        nb = json.loads(out.read_text())
        assert len(nb["cells"]) == 1
        assert nb["cells"][0]["cell_type"] == "code"

    def test_comment_cell_raw(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")  # blank → detached
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--comment-cell", "raw"])
        assert ret == 0
        nb = json.loads(out.read_text())
        assert nb["cells"][0]["cell_type"] == "raw"

    def test_markdown_bracket_fenced(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")  # blank → detached
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--markdown-bracket", "fenced"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        # nbformat may serialize source as a list of lines
        if isinstance(src, list):
            src = "".join(src)
        assert src.startswith("```\n")

    def test_markdown_bracket_pre(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")  # blank → detached
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--markdown-bracket", "pre"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        if isinstance(src, list):
            src = "".join(src)
        assert src.startswith("<pre>\n")

    def test_default_output_path(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        p = tmp_path / "example.lisp"
        p.write_text("(foo)\n")
        ret = main([str(p)])
        assert ret == 0
        assert (tmp_path / "example.ipynb").exists()
