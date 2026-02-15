"""Tests for script2notebook.parser."""

import pytest

from script2notebook.parser import Node, NodeKind, parse


# ── Helpers ───────────────────────────────────────────────────────────

def kinds(nodes):
    """Return a list of NodeKind values from a node list."""
    return [n.kind for n in nodes]


def texts(nodes):
    """Return a list of node texts."""
    return [n.text for n in nodes]


# ── Basic parsing ─────────────────────────────────────────────────────

class TestParseBasic:
    def test_single_form(self):
        nodes = parse("(defun foo (x) x)\n")
        forms = [n for n in nodes if n.kind == NodeKind.FORM]
        assert len(forms) == 1
        assert forms[0].text == "(defun foo (x) x)"

    def test_single_line_comment(self):
        nodes = parse("; hello\n")
        comments = [n for n in nodes if n.kind == NodeKind.LINE_COMMENT]
        assert len(comments) == 1
        assert comments[0].text == "; hello"

    def test_block_comment(self):
        src = "#| block |#\n"
        nodes = parse(src)
        blocks = [n for n in nodes if n.kind == NodeKind.BLOCK_COMMENT]
        assert len(blocks) == 1
        assert blocks[0].text == "#| block |#"

    def test_empty_source(self):
        assert parse("") == []
        assert parse("\n") == []


class TestParseMultipleNodes:
    def test_comment_then_form(self):
        src = "; comment\n(+ 1 2)\n"
        nodes = parse(src)
        real = [n for n in nodes if n.kind != NodeKind.BLANK]
        assert kinds(real) == [NodeKind.LINE_COMMENT, NodeKind.FORM]

    def test_two_forms_with_blank(self):
        src = "(foo)\n\n(bar)\n"
        nodes = parse(src)
        assert NodeKind.BLANK in kinds(nodes)
        forms = [n for n in nodes if n.kind == NodeKind.FORM]
        assert len(forms) == 2

    def test_consecutive_comments(self):
        src = "; a\n; b\n; c\n"
        nodes = parse(src)
        comments = [n for n in nodes if n.kind == NodeKind.LINE_COMMENT]
        assert len(comments) == 3

    def test_comments_with_blank_line_between(self):
        src = "; first\n\n; second\n"
        nodes = parse(src)
        assert NodeKind.BLANK in kinds(nodes)
        comments = [n for n in nodes if n.kind == NodeKind.LINE_COMMENT]
        assert len(comments) == 2


# ── Byte offsets ──────────────────────────────────────────────────────

class TestByteOffsets:
    def test_first_node_starts_at_zero(self):
        nodes = parse("; hello\n")
        assert nodes[0].start_byte == 0

    def test_form_byte_range(self):
        src = "(foo)\n"
        nodes = parse(src)
        form = [n for n in nodes if n.kind == NodeKind.FORM][0]
        assert src.encode("utf-8")[form.start_byte:form.end_byte] == b"(foo)"

    def test_second_form_offset(self):
        src = "(foo)\n\n(bar)\n"
        nodes = parse(src)
        forms = [n for n in nodes if n.kind == NodeKind.FORM]
        assert forms[1].text == "(bar)"
        assert src.encode("utf-8")[forms[1].start_byte:forms[1].end_byte] == b"(bar)"

    def test_blank_node_byte_range(self):
        src = "(foo)\n\n(bar)\n"
        nodes = parse(src)
        blanks = [n for n in nodes if n.kind == NodeKind.BLANK]
        assert len(blanks) == 1
        assert src.encode("utf-8")[blanks[0].start_byte:blanks[0].end_byte] == b"\n"


# ── Multi-line forms ─────────────────────────────────────────────────

class TestMultiLineForms:
    def test_defun_spans_lines(self):
        src = "(defun foo (x)\n  (+ x 1))\n"
        nodes = parse(src)
        form = [n for n in nodes if n.kind == NodeKind.FORM][0]
        assert form.text == "(defun foo (x)\n  (+ x 1))"
        assert form.start_line == 0
        assert form.end_line == 1

    def test_block_comment_spans_lines(self):
        src = "#|\nline 1\nline 2\n|#\n"
        nodes = parse(src)
        bc = [n for n in nodes if n.kind == NodeKind.BLOCK_COMMENT][0]
        assert bc.start_line == 0
        assert bc.end_line == 3


# ── Realistic ACL2 ───────────────────────────────────────────────────

REALISTIC_SOURCE = """\
; ACL2 header
; Copyright notice

(in-package "ACL2")

; A function
(defun double (x)
  (+ x x))

#|
Documentation block.
|#

(defthm double-3
  (equal (double 3) 6))
"""


class TestRealisticSource:
    def test_node_count(self):
        nodes = parse(REALISTIC_SOURCE)
        comments = [n for n in nodes if n.kind in (NodeKind.LINE_COMMENT, NodeKind.BLOCK_COMMENT)]
        forms = [n for n in nodes if n.kind == NodeKind.FORM]
        assert len(forms) == 3  # in-package, defun, defthm
        assert len(comments) == 4  # 2 header + 1 line + 1 block
