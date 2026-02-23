"""Tests for tree-sitter parsing of ACL2 source files.

ACL2 uses several Common Lisp constructs that stress the tree-sitter
grammar.  This file collects known problem cases so we can verify
fixes in tree-sitter-commonlisp and/or work around them in the
converter's parser layer.
"""

import pytest
import tree_sitter
import tree_sitter_commonlisp as tscl
from pathlib import Path

LANG = tree_sitter.Language(tscl.language())
PARSER = tree_sitter.Parser(LANG)


# ── helpers ──────────────────────────────────────────────────────────

def parse(src: str | bytes) -> tree_sitter.Tree:
    if isinstance(src, str):
        src = src.encode()
    return PARSER.parse(src)


def count_errors(node) -> int:
    """Recursively count ERROR nodes in a parse tree."""
    n = 1 if node.type == "ERROR" else 0
    for c in node.children:
        n += count_errors(c)
    return n


def find_errors(node, src: bytes) -> list[str]:
    """Recursively collect ERROR node text."""
    results = []
    if node.type == "ERROR":
        results.append(src[node.start_byte : node.end_byte].decode(errors="replace"))
    for c in node.children:
        results.extend(find_errors(c, src))
    return results


def top_level_children(tree: tree_sitter.Tree) -> list:
    return tree.root_node.children


# ── tilde-slash in format strings ────────────────────────────────────
# ACL2 format directives like ~/ inside strings must not confuse the
# parser.  tree-sitter-commonlisp treats ~/ as a pathname indicator
# and produces ERROR nodes for the text after the /.

class TestTildeSlashInStrings:
    """~/  inside string literals should not produce parse errors."""

    def test_bare_tilde_slash(self):
        tree = parse(b'"~/"')
        assert count_errors(tree.root_node) == 0, (
            f"'~/'' in string produced errors: {find_errors(tree.root_node, b'\"~/\"')}"
        )

    def test_format_directive_tilde_slash_comma(self):
        src = b'"~[~/,~]"'
        tree = parse(src)
        assert count_errors(tree.root_node) == 0, (
            f"format ~[~/,~] produced errors: {find_errors(tree.root_node, src)}"
        )

    def test_fmt1_call(self):
        src = b'(fmt1 " ~s0~#1~[~/,~]" x y z)'
        tree = parse(src)
        assert count_errors(tree.root_node) == 0, (
            f"fmt1 call produced errors: {find_errors(tree.root_node, src)}"
        )

    def test_format_forced_subgoals(self):
        """The defun that first exposed this issue in history-management.lisp."""
        src = b"""\
(defun format-forced-subgoals (clause-ids col max-col channel state)
  (cond
   ((null clause-ids)
    (princ$ ")" channel state))
   (t (let ((goal-name (string-for-tilde-@-clause-id-phrase (car clause-ids))))
        (if (or (null max-col)
                (if (null (cdr clause-ids))
                    (<= (+ 2 col (length goal-name)) max-col)
                  (<= (+ 7 col (length goal-name)) max-col)))
            (mv-let (col state)
                    (fmt1 " ~s0~#1~[~/,~]"
                          (list (cons #\\0 goal-name)
                                (cons #\\1 clause-ids))
                          col channel state nil)
                    (format-forced-subgoals
                     (cdr clause-ids) col max-col channel state))
          (princ$ " ...)" channel state))))))
"""
        tree = parse(src)
        children = top_level_children(tree)
        assert len(children) == 1, (
            f"Expected 1 top-level form, got {len(children)}"
        )
        assert count_errors(tree.root_node) == 0, (
            f"Parse errors: {find_errors(tree.root_node, src)}"
        )


# ── character literals ───────────────────────────────────────────────
# ACL2 uses #\0, #\1, etc. for digit character literals.

class TestCharacterLiterals:
    @pytest.mark.parametrize("char", [b"#\\0", b"#\\1", b"#\\a", b"#\\Space", b"#\\Newline"])
    def test_character_literal(self, char):
        src = b"(cons " + char + b" x)"
        tree = parse(src)
        assert count_errors(tree.root_node) == 0

    def test_char_in_list(self):
        src = b"(list (cons #\\0 goal-name) (cons #\\1 clause-ids))"
        tree = parse(src)
        assert count_errors(tree.root_node) == 0


# ── full file parse quality ──────────────────────────────────────────
# These tests parse entire ACL2 source files and check that tree-sitter
# produces a reasonable number of top-level forms with few errors.

ACL2_HOME = Path("/home/acl2")

# Expected approximate top-level form counts (from wc + manual inspection).
# These are (min, max) bounds — loose enough to survive minor edits.
FILE_EXPECTATIONS = {
    "history-management.lisp": (400, 600),
    "float-b.lisp": (40, 80),
    "axioms.lisp": (800, 1200),
    "basis-a.lisp": (200, 500),
}


@pytest.mark.skipif(not ACL2_HOME.exists(), reason="ACL2 source not available")
class TestFullFileParsing:
    @pytest.mark.parametrize("stem,bounds", list(FILE_EXPECTATIONS.items()))
    def test_top_level_form_count(self, stem, bounds):
        """Top-level form count should be in expected range.

        Far too many children indicates parse errors causing the parser
        to split forms (e.g., 2769 instead of ~500 for history-management).
        """
        src_path = ACL2_HOME / stem
        if not src_path.exists():
            pytest.skip(f"{src_path} not found")

        src = src_path.read_bytes()
        tree = parse(src)
        children = top_level_children(tree)
        # Filter out whitespace-only / comment-only nodes if any
        meaningful = [c for c in children if c.type not in ("comment",)]
        lo, hi = bounds
        assert lo <= len(meaningful) <= hi, (
            f"{stem}: expected {lo}-{hi} top-level forms, got {len(meaningful)}"
        )

    @pytest.mark.parametrize("stem", list(FILE_EXPECTATIONS.keys()))
    def test_error_rate(self, stem):
        """Error nodes should be a small fraction of total nodes."""
        src_path = ACL2_HOME / stem
        if not src_path.exists():
            pytest.skip(f"{src_path} not found")

        src = src_path.read_bytes()
        tree = parse(src)
        children = top_level_children(tree)
        errors = [c for c in children if c.has_error or c.type == "ERROR"]
        error_rate = len(errors) / max(len(children), 1)
        # Allow up to 5% error rate (ideally 0%)
        assert error_rate < 0.05, (
            f"{stem}: {len(errors)}/{len(children)} top-level nodes have errors "
            f"({error_rate:.1%})"
        )
