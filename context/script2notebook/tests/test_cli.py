"""Tests for script2notebook.cli."""

import json
import os
import time
import pytest

from script2notebook.cli import main


# ── Basic invocation ─────────────────────────────────────────────────

class TestCLIBasic:
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
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "test.ipynb"
        ret = main([str(p), "-o", str(out)])
        assert ret == 0
        assert out.exists()
        nb = json.loads(out.read_text())
        assert len(nb["cells"]) == 2

    def test_basic_conversion_attached(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n(foo)\n")
        out = tmp_path / "test.ipynb"
        ret = main([str(p), "-o", str(out)])
        assert ret == 0
        nb = json.loads(out.read_text())
        assert len(nb["cells"]) == 1
        assert nb["cells"][0]["cell_type"] == "code"

    def test_default_output_path(self, tmp_path, monkeypatch):
        monkeypatch.chdir(tmp_path)
        p = tmp_path / "example.lisp"
        p.write_text("(foo)\n")
        ret = main([str(p)])
        assert ret == 0
        assert (tmp_path / "example.ipynb").exists()


# ── Short flags ──────────────────────────────────────────────────────

class TestShortFlags:
    def test_raw_flag(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--raw"])
        assert ret == 0
        nb = json.loads(out.read_text())
        assert nb["cells"][0]["cell_type"] == "raw"

    def test_comment_cell_raw(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--comment-cell", "raw"])
        assert ret == 0
        nb = json.loads(out.read_text())
        assert nb["cells"][0]["cell_type"] == "raw"

    def test_fenced_flag(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--fenced"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        if isinstance(src, list):
            src = "".join(src)
        assert src.startswith("```\n")

    def test_pre_flag(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--pre"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        if isinstance(src, list):
            src = "".join(src)
        assert src.startswith("<pre>\n")

    def test_plain_flag(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--plain"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        if isinstance(src, list):
            src = "".join(src)
        assert "```" not in src
        assert "<pre>" not in src

    def test_markdown_bracket_fenced_long(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--markdown-bracket", "fenced"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        if isinstance(src, list):
            src = "".join(src)
        assert src.startswith("```\n")

    def test_markdown_bracket_pre_long(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = tmp_path / "out.ipynb"
        ret = main([str(p), "-o", str(out), "--markdown-bracket", "pre"])
        assert ret == 0
        nb = json.loads(out.read_text())
        src = nb["cells"][0]["source"]
        if isinstance(src, list):
            src = "".join(src)
        assert src.startswith("<pre>\n")


# ── Multiple files ───────────────────────────────────────────────────

class TestMultipleFiles:
    def test_multiple_files(self, tmp_path):
        a = tmp_path / "a.lisp"
        b = tmp_path / "b.lisp"
        a.write_text("(foo)\n")
        b.write_text("(bar)\n")
        ret = main([str(a), str(b)])
        assert ret == 0
        assert (tmp_path / "a.ipynb").exists()
        assert (tmp_path / "b.ipynb").exists()

    def test_multiple_files_with_output_dir(self, tmp_path):
        a = tmp_path / "a.lisp"
        b = tmp_path / "b.lisp"
        a.write_text("(foo)\n")
        b.write_text("(bar)\n")
        out = tmp_path / "out"
        ret = main([str(a), str(b), "-o", str(out)])
        assert ret == 0
        assert (out / "a.ipynb").exists()
        assert (out / "b.ipynb").exists()


# ── Directory recursion ──────────────────────────────────────────────

class TestDirectoryRecursion:
    def _make_tree(self, tmp_path):
        """Create a small directory tree with mixed files."""
        src = tmp_path / "src"
        sub = src / "sub"
        sub.mkdir(parents=True)
        (src / "top.lisp").write_text("(a)\n")
        (sub / "nested.acl2").write_text("(b)\n")
        (sub / "also.lsp").write_text("(c)\n")
        (sub / "ignore.txt").write_text("not lisp\n")
        return src

    def test_directory_finds_all_matching(self, tmp_path):
        root = self._make_tree(tmp_path)
        ret = main([str(root)])
        assert ret == 0
        assert (root / "top.ipynb").exists()
        assert (root / "sub" / "nested.ipynb").exists()
        assert (root / "sub" / "also.ipynb").exists()
        assert not (root / "sub" / "ignore.ipynb").exists()

    def test_directory_with_output_dir(self, tmp_path):
        """Output dir mirrors sub-directory structure of input dir."""
        root = self._make_tree(tmp_path)
        out = tmp_path / "notebooks"
        ret = main([str(root), "-o", str(out)])
        assert ret == 0
        assert (out / "top.ipynb").exists()
        assert (out / "sub" / "nested.ipynb").exists()
        assert (out / "sub" / "also.ipynb").exists()
        assert not (out / "sub" / "ignore.ipynb").exists()

    def test_no_matching_files_in_dir(self, tmp_path):
        d = tmp_path / "empty"
        d.mkdir()
        (d / "readme.txt").write_text("nothing")
        ret = main([str(d)])
        assert ret == 1  # no matching files


# ── Timestamp checking ───────────────────────────────────────────────

class TestTimestampCheck:
    def test_skip_when_notebook_newer(self, tmp_path, capsys):
        p = tmp_path / "test.lisp"
        p.write_text("(foo)\n")
        out = tmp_path / "test.ipynb"
        # First run creates the notebook
        ret = main([str(p)])
        assert ret == 0
        assert out.exists()
        first_mtime = out.stat().st_mtime

        # Ensure source is older than notebook
        old_time = first_mtime - 10
        os.utime(p, (old_time, old_time))

        # Second run should skip (notebook is newer)
        ret = main([str(p)])
        assert ret == 0
        # mtime should be unchanged
        assert out.stat().st_mtime == first_mtime

    def test_reconvert_when_source_newer(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("(foo)\n")
        out = tmp_path / "test.ipynb"
        ret = main([str(p)])
        assert ret == 0
        first_mtime = out.stat().st_mtime

        # Touch the source to make it newer
        time.sleep(0.05)
        p.write_text("(bar)\n")

        ret = main([str(p)])
        assert ret == 0
        assert out.stat().st_mtime > first_mtime

    def test_force_reconverts(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("(foo)\n")
        out = tmp_path / "test.ipynb"
        ret = main([str(p)])
        assert ret == 0
        first_mtime = out.stat().st_mtime

        # Make source older
        old_time = first_mtime - 10
        os.utime(p, (old_time, old_time))

        # With --force it should reconvert
        time.sleep(0.05)
        ret = main([str(p), "--force"])
        assert ret == 0
        assert out.stat().st_mtime > first_mtime
