"""Tests for script2notebook.converter."""

import pytest

from script2notebook.converter import (
    CommentCellType,
    MarkdownBracket,
    source_to_notebook,
    file_to_notebook,
    convert_file,
)
from script2notebook.languages import ACL2, COMMON_LISP


# ── Helpers ───────────────────────────────────────────────────────────

def cells_summary(nb):
    """Return [(cell_type, source_preview), ...] for quick assertions."""
    return [(c.cell_type, c.source) for c in nb.cells]


def cell_types(nb):
    return [c.cell_type for c in nb.cells]


# ── Test fixtures ─────────────────────────────────────────────────────

# Comment immediately before form (no blank) → attached
SIMPLE_SOURCE = """\
; header comment
(defun foo (x) x)
"""

# Comment separated from form by blank → detached
DETACHED_SOURCE = """\
; header comment

(defun foo (x) x)
"""

MULTI_COMMENT_SOURCE = """\
; line 1
; line 2

; line 3
(foo)
"""

BLOCK_COMMENT_SOURCE = """\
#|
Block comment here.
|#
(bar)
"""

BLOCK_COMMENT_DETACHED_SOURCE = """\
#|
Block comment here.
|#

(bar)
"""

MIXED_SOURCE = """\
;;; File header
;;; Second line

; Attached comment
(include-book "top")

;; Standalone note
;; More note

; Before theorem
(defthm my-thm
  (equal 1 1))

#|
Documentation block
|#

(defun baz (y) y)
"""

CODE_ONLY_SOURCE = """\
(foo)

(bar)

(baz)
"""


# ── Attached / detached behaviour ────────────────────────────────────

class TestAttachedDetached:
    def test_attached_comment_goes_into_code_cell(self):
        """Comment with no blank before form → single code cell."""
        nb = source_to_notebook(SIMPLE_SOURCE, ACL2)
        assert cell_types(nb) == ["code"]
        assert nb.cells[0].source == "; header comment\n(defun foo (x) x)"

    def test_detached_comment_becomes_markdown(self):
        """Comment followed by blank line before form → markdown + code."""
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        assert cell_types(nb) == ["markdown", "code"]
        assert nb.cells[0].source == "; header comment"
        assert nb.cells[1].source == "(defun foo (x) x)"

    def test_split_run_at_blank(self):
        """Earlier comments are markdown; tail after last blank attaches."""
        nb = source_to_notebook(MULTI_COMMENT_SOURCE, ACL2)
        assert cell_types(nb) == ["markdown", "code"]
        md = nb.cells[0].source
        assert "; line 1" in md
        assert "; line 2" in md
        # line 3 is attached to form
        code = nb.cells[1].source
        assert code == "; line 3\n(foo)"

    def test_block_comment_attached(self):
        """Block comment with no blank before form → code cell."""
        nb = source_to_notebook(BLOCK_COMMENT_SOURCE, ACL2)
        assert cell_types(nb) == ["code"]
        src = nb.cells[0].source
        assert "#|" in src
        assert "|#" in src
        assert "(bar)" in src

    def test_block_comment_detached(self):
        """Block comment with blank before form → markdown + code."""
        nb = source_to_notebook(BLOCK_COMMENT_DETACHED_SOURCE, ACL2)
        assert cell_types(nb) == ["markdown", "code"]
        assert "#|" in nb.cells[0].source
        assert nb.cells[1].source == "(bar)"

    def test_multiple_attached_comments(self):
        """Multiple consecutive comments all attach when no internal blank."""
        src = "; first\n; second\n(form)\n"
        nb = source_to_notebook(src, ACL2)
        assert cell_types(nb) == ["code"]
        assert nb.cells[0].source == "; first\n; second\n(form)"

    def test_trailing_comment_at_eof(self):
        """Comments at end of file with no following form → markdown."""
        src = "(foo)\n; trailing\n"
        nb = source_to_notebook(src, ACL2)
        assert cell_types(nb) == ["code", "markdown"]
        assert nb.cells[1].source == "; trailing"

    def test_attached_excludes_preceding_blank(self):
        """Attached comments do not include preceding blank lines."""
        nb = source_to_notebook(MULTI_COMMENT_SOURCE, ACL2)
        code = nb.cells[1].source
        assert not code.startswith("\n")
        assert code.startswith("; line 3")


class TestGroupingBasic:
    def test_code_only(self):
        nb = source_to_notebook(CODE_ONLY_SOURCE, ACL2)
        assert cell_types(nb) == ["code", "code", "code"]

    def test_one_form_per_code_cell(self):
        nb = source_to_notebook(CODE_ONLY_SOURCE, ACL2)
        assert nb.cells[0].source == "(foo)"
        assert nb.cells[1].source == "(bar)"
        assert nb.cells[2].source == "(baz)"


class TestMixedSource:
    def test_cell_types(self):
        nb = source_to_notebook(MIXED_SOURCE, ACL2)
        expected = [
            "markdown",  # File header + Second line (detached from form by blank)
            "code",      # ; Attached comment + include-book
            "markdown",  # Standalone note + More note (detached from form by blank)
            "code",      # ; Before theorem + defthm
            "markdown",  # Documentation block (detached from form by blank)
            "code",      # defun baz
        ]
        assert cell_types(nb) == expected

    def test_attached_comment_in_mixed(self):
        nb = source_to_notebook(MIXED_SOURCE, ACL2)
        # "; Attached comment" goes into the code cell with include-book
        code1 = nb.cells[1].source
        assert code1.startswith("; Attached comment")
        assert '(include-book "top")' in code1

    def test_detached_header_in_mixed(self):
        nb = source_to_notebook(MIXED_SOURCE, ACL2)
        md = nb.cells[0].source
        assert ";;; File header" in md
        assert ";;; Second line" in md

    def test_no_text_modification(self):
        """Every cell source should be a verbatim substring of the original."""
        nb = source_to_notebook(MIXED_SOURCE, ACL2)
        source_bytes = MIXED_SOURCE.encode("utf-8")
        for cell in nb.cells:
            src = cell.source
            assert src in MIXED_SOURCE or src.rstrip("\n") in MIXED_SOURCE


# ── Provenance metadata ──────────────────────────────────────────────

class TestProvenance:
    def test_provenance_present(self):
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        for cell in nb.cells:
            assert "provenance" in cell.metadata
            prov = cell.metadata["provenance"]
            assert "start" in prov
            assert "end" in prov

    def test_source_uri_at_notebook_level(self):
        nb = source_to_notebook(DETACHED_SOURCE, ACL2, source_uri="file:///test.lisp")
        assert nb.metadata["source_file"] == "file:///test.lisp"
        # Not duplicated in cells.
        for cell in nb.cells:
            assert "source" not in cell.metadata["provenance"]

    def test_no_source_uri_key_when_absent(self):
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        assert "source_file" not in nb.metadata

    def test_byte_offsets_cover_source(self):
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        source_bytes = DETACHED_SOURCE.encode("utf-8")
        for cell in nb.cells:
            prov = cell.metadata["provenance"]
            span = source_bytes[prov["start"]:prov["end"]].decode("utf-8")
            assert cell.source in span or span.rstrip("\n") == cell.source

    def test_attached_provenance_spans_comment_and_form(self):
        """Provenance for attached cell covers from comment start to form end."""
        nb = source_to_notebook(SIMPLE_SOURCE, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        span = SIMPLE_SOURCE.encode("utf-8")[prov["start"]:prov["end"]]
        text = span.decode("utf-8")
        assert "; header comment" in text
        assert "(defun foo (x) x)" in text


# ── Comment span metadata ────────────────────────────────────────────

class TestCommentSpan:
    def test_markdown_cell_no_bracket(self):
        """Markdown cell with no bracket: comment = [0, len(source)]."""
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        assert prov["comment"] == [0, len(nb.cells[0].source)]

    def test_markdown_cell_fenced(self):
        """Fenced bracket shifts comment span past the opening ```\\n."""
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        src = nb.cells[0].source
        prov = nb.cells[0].metadata["provenance"]
        start, end = prov["comment"]
        assert start == 4  # len("```\n")
        comment_text = src[start:end]
        assert comment_text == "; header comment"

    def test_markdown_cell_pre(self):
        """Pre bracket shifts comment span past the opening <pre>\\n."""
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            markdown_bracket=MarkdownBracket.PRE,
        )
        src = nb.cells[0].source
        prov = nb.cells[0].metadata["provenance"]
        start, end = prov["comment"]
        assert start == 6  # len("<pre>\n")
        comment_text = src[start:end]
        assert comment_text == "; header comment"

    def test_raw_cell_comment_span(self):
        """Raw cell: comment is the full source."""
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            comment_cell_type=CommentCellType.RAW,
        )
        prov = nb.cells[0].metadata["provenance"]
        assert prov["comment"] == [0, len(nb.cells[0].source)]

    def test_code_cell_no_comment(self):
        """Pure code cell has no comment key."""
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        prov = nb.cells[1].metadata["provenance"]
        assert "comment" not in prov

    def test_code_cell_with_attached_comment(self):
        """Attached comment: comment span covers the comment portion."""
        nb = source_to_notebook(SIMPLE_SOURCE, ACL2)
        src = nb.cells[0].source
        prov = nb.cells[0].metadata["provenance"]
        start, end = prov["comment"]
        comment_text = src[start:end]
        assert "; header comment" in comment_text
        # The rest is the form
        form_text = src[end:]
        assert "(defun foo (x) x)" in form_text

    def test_multiple_attached_comments_span(self):
        """Multiple attached comments: span covers all of them."""
        src_text = "; first\n; second\n(form)\n"
        nb = source_to_notebook(src_text, ACL2)
        src = nb.cells[0].source
        prov = nb.cells[0].metadata["provenance"]
        start, end = prov["comment"]
        assert start == 0
        comment_text = src[start:end]
        assert "; first" in comment_text
        assert "; second" in comment_text
        form_text = src[end:]
        assert "(form)" in form_text

    def test_fenced_multiline_comment_span(self):
        """Fenced multi-line: span skips bracket and covers actual comments."""
        src_text = "; line A\n; line B\n\n(form)\n"
        nb = source_to_notebook(
            src_text, ACL2,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        md = nb.cells[0]
        prov = md.metadata["provenance"]
        start, end = prov["comment"]
        comment_text = md.source[start:end]
        assert "; line A" in comment_text
        assert "; line B" in comment_text
        assert "```" not in comment_text


# ── Inline comment spans ─────────────────────────────────────────────

class TestInlineCommentSpans:
    """Tests for ``provenance.comments`` — inline comments within code forms."""

    def test_no_inline_comments(self):
        """Pure code cell without inline comments has no 'comments' key."""
        nb = source_to_notebook("(defun foo (x) x)\n", ACL2)
        prov = nb.cells[0].metadata["provenance"]
        assert "comments" not in prov

    def test_inline_line_comment(self):
        """A ; comment inside a defun body appears in provenance.comments."""
        src = "(defun foo (x)\n  ; body comment\n  x)\n"
        nb = source_to_notebook(src, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        assert "comments" in prov
        spans = prov["comments"]
        assert len(spans) == 1
        text = nb.cells[0].source[spans[0][0]:spans[0][1]]
        assert text == "; body comment"

    def test_multiple_inline_line_comments(self):
        """Multiple ; comments inside a form produce multiple spans."""
        src = "(defun foo (x)\n  ; first\n  ; second\n  x)\n"
        nb = source_to_notebook(src, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        assert "comments" in prov
        spans = prov["comments"]
        assert len(spans) == 2
        text0 = nb.cells[0].source[spans[0][0]:spans[0][1]]
        text1 = nb.cells[0].source[spans[1][0]:spans[1][1]]
        assert text0 == "; first"
        assert text1 == "; second"

    def test_inline_block_comment(self):
        """A #|...|# comment inside a form appears in provenance.comments."""
        src = "(defun foo (x)\n  #| doc |#\n  x)\n"
        nb = source_to_notebook(src, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        assert "comments" in prov
        spans = prov["comments"]
        assert len(spans) == 1
        text = nb.cells[0].source[spans[0][0]:spans[0][1]]
        assert text == "#| doc |#"

    def test_attached_comment_plus_inline(self):
        """Cell with attached comment AND inline comment has both keys."""
        src = "; header\n(defun foo (x)\n  ; body\n  x)\n"
        nb = source_to_notebook(src, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        # Attached comment
        assert "comment" in prov
        comment_text = nb.cells[0].source[prov["comment"][0]:prov["comment"][1]]
        assert "; header" in comment_text
        # Inline comment
        assert "comments" in prov
        spans = prov["comments"]
        assert len(spans) == 1
        inline_text = nb.cells[0].source[spans[0][0]:spans[0][1]]
        assert inline_text == "; body"

    def test_detached_comment_no_inline(self):
        """Detached comment cell has no 'comments' key (only markdown cells)."""
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        for cell in nb.cells:
            prov = cell.metadata["provenance"]
            assert "comments" not in prov

    def test_inline_spans_are_char_offsets_in_cell(self):
        """Inline comment spans are character offsets into cell.source."""
        src = "(defun f (x) ; note\n  x)\n"
        nb = source_to_notebook(src, ACL2)
        prov = nb.cells[0].metadata["provenance"]
        spans = prov["comments"]
        s, e = spans[0]
        assert nb.cells[0].source[s:e] == "; note"
        # Verify offset is correct relative to cell source
        assert nb.cells[0].source.index("; note") == s


# ── Notebook metadata ────────────────────────────────────────────────

class TestNotebookMetadata:
    def test_acl2_kernel(self):
        nb = source_to_notebook("(foo)\n", ACL2)
        assert nb.metadata["kernelspec"]["name"] == "acl2"
        assert nb.metadata["kernelspec"]["language"] == "acl2"
        assert nb.metadata["language_info"]["file_extension"] == ".lisp"

    def test_common_lisp_kernel(self):
        nb = source_to_notebook("(foo)\n", COMMON_LISP)
        assert nb.metadata["kernelspec"]["name"] == "common-lisp"
        assert nb.metadata["language_info"]["file_extension"] == ".lsp"


# ── Comment cell type option ─────────────────────────────────────────

class TestCommentCellType:
    def test_default_is_markdown(self):
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        assert nb.cells[0].cell_type == "markdown"

    def test_raw_option(self):
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            comment_cell_type=CommentCellType.RAW,
        )
        assert nb.cells[0].cell_type == "raw"
        # Source text still verbatim.
        assert nb.cells[0].source == "; header comment"

    def test_raw_preserves_code_cells(self):
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            comment_cell_type=CommentCellType.RAW,
        )
        assert nb.cells[1].cell_type == "code"


# ── Markdown bracket option ──────────────────────────────────────────

class TestMarkdownBracket:
    def test_none_is_default(self):
        nb = source_to_notebook(DETACHED_SOURCE, ACL2)
        assert nb.cells[0].source == "; header comment"

    def test_fenced(self):
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        src = nb.cells[0].source
        assert src.startswith("```\n")
        assert src.endswith("\n```")
        assert "; header comment" in src

    def test_pre(self):
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            markdown_bracket=MarkdownBracket.PRE,
        )
        src = nb.cells[0].source
        assert src.startswith("<pre>\n")
        assert src.endswith("\n</pre>")
        assert "; header comment" in src

    def test_bracket_ignored_for_raw(self):
        """When comment_cell_type=raw, bracket has no effect."""
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            comment_cell_type=CommentCellType.RAW,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        src = nb.cells[0].source
        assert "```" not in src
        assert src == "; header comment"

    def test_fenced_multiline(self):
        src_text = "; line A\n; line B\n\n(form)\n"
        nb = source_to_notebook(
            src_text, ACL2,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        # line A and line B detached from form by blank
        src = nb.cells[0].source
        lines = src.split("\n")
        assert lines[0] == "```"
        assert lines[-1] == "```"

    def test_pre_multiline(self):
        src_text = "; line A\n; line B\n\n(form)\n"
        nb = source_to_notebook(
            src_text, ACL2,
            markdown_bracket=MarkdownBracket.PRE,
        )
        src = nb.cells[0].source
        assert src.startswith("<pre>\n")
        assert src.endswith("\n</pre>")

    def test_code_cells_unaffected_by_bracket(self):
        nb = source_to_notebook(
            DETACHED_SOURCE, ACL2,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        assert nb.cells[1].source == "(defun foo (x) x)"
        assert "```" not in nb.cells[1].source

    def test_bracket_not_applied_to_attached_comments(self):
        """Attached comments in code cells are not bracketed."""
        nb = source_to_notebook(
            SIMPLE_SOURCE, ACL2,
            markdown_bracket=MarkdownBracket.FENCED,
        )
        # SIMPLE_SOURCE has attached comment → code cell
        assert nb.cells[0].cell_type == "code"
        assert "```" not in nb.cells[0].source


# ── File-based conversion ────────────────────────────────────────────

class TestFileConversion:
    def test_file_to_notebook(self, tmp_path):
        src = "; example\n\n(+ 1 2)\n"  # blank line → detached
        p = tmp_path / "test.lisp"
        p.write_text(src)
        nb = file_to_notebook(p)
        assert cell_types(nb) == ["markdown", "code"]
        assert nb.metadata["kernelspec"]["name"] == "acl2"
        # Source file URI in notebook-level metadata.
        assert nb.metadata["source_file"].startswith("file://")
        assert "test.lisp" in nb.metadata["source_file"]

    def test_file_to_notebook_attached(self, tmp_path):
        src = "; example\n(+ 1 2)\n"  # no blank → attached
        p = tmp_path / "test.lisp"
        p.write_text(src)
        nb = file_to_notebook(p)
        assert cell_types(nb) == ["code"]
        assert "; example" in nb.cells[0].source
        assert "(+ 1 2)" in nb.cells[0].source

    def test_file_to_notebook_lsp(self, tmp_path):
        p = tmp_path / "test.lsp"
        p.write_text("(foo)\n")
        nb = file_to_notebook(p)
        assert nb.metadata["kernelspec"]["name"] == "common-lisp"

    def test_file_to_notebook_acl2_ext(self, tmp_path):
        p = tmp_path / "test.acl2"
        p.write_text("(foo)\n")
        nb = file_to_notebook(p)
        assert nb.metadata["kernelspec"]["name"] == "acl2"

    def test_convert_file_default_output(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")
        out = convert_file(p)
        assert out == tmp_path / "test.ipynb"
        assert out.exists()

    def test_convert_file_custom_output(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("(foo)\n")
        out_path = tmp_path / "custom.ipynb"
        out = convert_file(p, out_path)
        assert out == out_path
        assert out_path.exists()

    def test_convert_file_with_options(self, tmp_path):
        p = tmp_path / "test.lisp"
        p.write_text("; comment\n\n(foo)\n")  # blank → detached
        out = convert_file(
            p,
            comment_cell_type=CommentCellType.RAW,
        )
        import json
        nb = json.loads(out.read_text())
        assert nb["cells"][0]["cell_type"] == "raw"
