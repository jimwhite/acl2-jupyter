"""Tests for tree-sitter parsing of ACL2 source files.

ACL2 uses several Common Lisp constructs that stress the tree-sitter
grammar.  This file collects known problem cases so we can verify
fixes in tree-sitter-commonlisp and/or work around them in the
converter's parser layer.

Uses the ``tree_sitter_commonlisp_noformat`` grammar which treats
string literals as opaque ``"..."`` tokens (no format-specifier
sub-parsing).  This avoids error-recovery issues from structural
characters inside format strings and is all we need for correct
top-level form extraction.
"""

import pytest
import tree_sitter
import tree_sitter_commonlisp_noformat as tscl
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


def count_parens_outside_strings(src: str | bytes) -> tuple[int, int]:
    """Count open and close parens *outside* string literals and char literals.

    Returns (open_count, close_count).  This is a simple state-machine
    that skips content inside double-quoted strings (handling backslash
    escapes) and #\\ character literals.
    """
    if isinstance(src, bytes):
        src = src.decode()
    opens = closes = 0
    i = 0
    n = len(src)
    while i < n:
        ch = src[i]
        if ch == '"':
            # skip to closing quote, honoring backslash escapes
            i += 1
            while i < n:
                if src[i] == '\\':
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if ch == '#' and i + 1 < n and src[i + 1] == '\\':
            # character literal: #\x or #\Space etc.
            i += 2
            # consume the character name (letters/digits)
            while i < n and src[i].isalnum():
                i += 1
            continue
        if ch == ';':
            # skip line comment
            while i < n and src[i] != '\n':
                i += 1
            continue
        if ch == '(':
            opens += 1
        elif ch == ')':
            closes += 1
        i += 1
    return opens, closes


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

    def test_tilde_at_directive(self):
        """~@ is a standalone directive in ACL2 (tilde-at phrase).
        The grammar must not consume @ as format_modifiers and then
        fail looking for a format_directive_type."""
        src = b'"~s0 ~@1"'
        tree = parse(src)
        assert count_errors(tree.root_node) == 0, (
            f"~@1 produced errors: {find_errors(tree.root_node, src)}"
        )

    def test_tilde_colon_at_modifier(self):
        """~:@ and ~@: modifiers should still work with directives."""
        src = b'"~@0A key ~#1~[ while proving ~@2 (descended from ~@3)~/~]:"'
        tree = parse(src)
        assert count_errors(tree.root_node) == 0, (
            f"gag-start-msg format string produced errors: {find_errors(tree.root_node, src)}"
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


# ── parenthesis balance ───────────────────────────────────────────────
# When tree-sitter parses a form, the extracted text must have balanced
# parentheses (ignoring parens inside strings, char literals, comments).
# If format-specifier parsing consumes structural parens (e.g., ~( ~) ~[ ~])
# or ERROR nodes cause form splitting, the balance will be off.

class TestParenBalance:
    """Each top-level form's text must have balanced parentheses."""

    def test_format_forced_subgoals_balanced(self):
        """format-forced-subgoals contains ~[~/,~] which has ]  and ) inside strings."""
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
        assert len(children) == 1, f"Expected 1 form, got {len(children)}"
        form_text = src[children[0].start_byte : children[0].end_byte]
        opens, closes = count_parens_outside_strings(form_text)
        assert opens == closes, (
            f"Unbalanced parens: {opens} opens, {closes} closes "
            f"(balance={opens - closes})"
        )

    def test_format_processor_balanced(self):
        """format-processor has format strings with ( ) and ~x0 directives."""
        src = b"""\
(defun format-processor (col goal-tree channel state)
  (let ((proc (access goal-tree goal-tree :processor)))
    (cond
     ((consp proc)
      (cond
       ((eq (car proc) 'push-clause)
        (mv-let
         (col state)
         (fmt1 "~s0 ~@1"
               (list (cons #\\0 "PUSH")
                     (cons #\\1
                           (cond
                            ((eq (caddr proc) :REVERT)
                             "(reverting)")
                            ((eq (caddr proc) :ABORT)
                             "*ABORTING*")
                            (t
                             (tilde-@-pool-name-phrase
                              (access clause-id
                                      (cadr proc)
                                      :forcing-round)
                              (access clause-id
                                      (cadr proc)
                                      :pool-lst))))))
               col channel state nil)
         (declare (ignore col))
         state))
       ((eq (cadr proc) :forced)
        (mv-let (col state)
                (fmt1 "~s0 (FORCED"
                      (list (cons #\\0 (cdr (assoc-eq (car proc)
                                                     *format-proc-alist*))))
                      col channel state nil)
                (format-forced-subgoals
                 (cddr proc) col
                 (f-get-global 'proof-tree-buffer-width state)
                 channel state)))
       (t (let ((err (er hard 'format-processor
                         "Unexpected shape for goal-tree processor, ~x0"
                         proc)))
            (declare (ignore err))
            state))))
     (t (princ$ (or (cdr (assoc-eq proc *format-proc-alist*))
                    proc)
                channel state)))))
"""
        tree = parse(src)
        children = top_level_children(tree)
        assert len(children) == 1, f"Expected 1 form, got {len(children)}"
        form_text = src[children[0].start_byte : children[0].end_byte]
        opens, closes = count_parens_outside_strings(form_text)
        assert opens == closes, (
            f"Unbalanced parens: {opens} opens, {closes} closes "
            f"(balance={opens - closes})"
        )

    def test_format_goal_tree_lst_balanced(self):
        """format-goal-tree-lst has ~[~/,~] and ~#1~[~/more ~] etc."""
        src = b"""\
(fmt1 "<~x0 ~#1~[~/more ~]subgoal~#2~[~/s~]>~%"
      (list (cons #\\0 goal-tree-lst)
            (cons #\\1 (if (= fanout goal-tree-lst) 0 1))
            (cons #\\2 (if (eql goal-tree-lst 1)
                          0
                        1)))
      col channel state nil)
"""
        tree = parse(src)
        children = top_level_children(tree)
        assert len(children) == 1, f"Expected 1 form, got {len(children)}"
        form_text = src[children[0].start_byte : children[0].end_byte]
        opens, closes = count_parens_outside_strings(form_text)
        assert opens == closes, (
            f"Unbalanced parens: {opens} opens, {closes} closes "
            f"(balance={opens - closes})"
        )

    def test_simple_format_string_parens(self):
        """Parens inside format strings must not affect balance."""
        src = b'(fmt1 "~s0 (FORCED" x channel state nil)'
        tree = parse(src)
        children = top_level_children(tree)
        form_text = src[children[0].start_byte : children[0].end_byte]
        opens, closes = count_parens_outside_strings(form_text)
        assert opens == closes, (
            f"Unbalanced: {opens} opens, {closes} closes"
        )

    def test_string_with_close_paren(self):
        """A string containing ) must not leak into structural paren count."""
        src = b'(princ$ ")" channel state)'
        tree = parse(src)
        children = top_level_children(tree)
        form_text = src[children[0].start_byte : children[0].end_byte]
        opens, closes = count_parens_outside_strings(form_text)
        assert opens == closes

    def test_string_with_open_and_close(self):
        """A string with both ( and ) inside."""
        src = b'(princ$ "(reverting)" channel state)'
        tree = parse(src)
        children = top_level_children(tree)
        form_text = src[children[0].start_byte : children[0].end_byte]
        opens, closes = count_parens_outside_strings(form_text)
        assert opens == closes


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
# These tests parse entire ACL2 source files with the noformat grammar
# and check that tree-sitter produces a reasonable number of top-level
# forms with few errors.  The noformat grammar treats strings as opaque
# "..." tokens, avoiding error-recovery issues from structural chars
# inside format strings.

ACL2_HOME = Path("/home/acl2")

# Expected approximate top-level form counts (from wc + manual inspection).
# These are (min, max) bounds — loose enough to survive minor edits.
# Counts measured with the noformat grammar.
FILE_EXPECTATIONS = {
    "history-management.lisp": (500, 700),
    "float-b.lisp": (40, 80),
    "axioms.lisp": (1600, 2200),
    "basis-a.lisp": (300, 500),
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

    @pytest.mark.parametrize("stem", list(FILE_EXPECTATIONS.keys()))
    def test_paren_balance(self, stem):
        """Every non-comment top-level form must have balanced parens.

        Tree-sitter format specifier parsing can consume structural
        parens (e.g., ~( ~) ~[ ~]) or ERROR recovery can split forms
        at paren boundaries.  Either defect manifests as an imbalance.
        """
        src_path = ACL2_HOME / stem
        if not src_path.exists():
            pytest.skip(f"{src_path} not found")

        src = src_path.read_bytes()
        tree = parse(src)
        children = top_level_children(tree)

        imbalanced = []
        for child in children:
            if child.type == "comment":
                continue
            form_text = src[child.start_byte : child.end_byte]
            opens, closes = count_parens_outside_strings(form_text)
            if opens != closes:
                # Grab the first 60 chars of the form for context
                preview = form_text[:60].decode(errors="replace")
                imbalanced.append(
                    f"  line {child.start_point[0]+1}: "
                    f"{opens}( {closes}) balance={opens-closes} "
                    f"  {preview!r}..."
                )

        assert not imbalanced, (
            f"{stem}: {len(imbalanced)} forms with imbalanced parens:\n"
            + "\n".join(imbalanced[:20])
        )
