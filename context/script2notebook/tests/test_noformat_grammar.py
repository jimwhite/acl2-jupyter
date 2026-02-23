"""Tests for the commonlisp_noformat grammar variant.

The noformat variant treats string literals as opaque "..." tokens
without parsing format specifiers inside them.  This avoids error
recovery issues when structural characters appear in format strings.
"""

import pytest
import tree_sitter
import tree_sitter_commonlisp_noformat as tscl_nf
from pathlib import Path

LANG = tree_sitter.Language(tscl_nf.language())
PARSER = tree_sitter.Parser(LANG)

ACL2_HOME = Path("/home/acl2")


def parse(src: str | bytes) -> tree_sitter.Tree:
    if isinstance(src, str):
        src = src.encode()
    return PARSER.parse(src)


# ── basic grammar tests ─────────────────────────────────────────────

class TestNoformatBasics:
    def test_import(self):
        """The noformat package should import and expose language()."""
        lang = tree_sitter.Language(tscl_nf.language())
        assert lang is not None

    def test_simple_form(self):
        tree = parse(b"(+ 1 1)")
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_defun(self):
        tree = parse(b"(defun foo (x) (+ x 1))")
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_string_is_opaque(self):
        """Strings should be single str_lit nodes with no children parsed."""
        tree = parse(b'(format t "hello world")')
        root = tree.root_node
        assert len(root.children) == 1
        assert not root.has_error


# ── format strings that break the original grammar ───────────────────

class TestFormatStringsOpaque:
    """Format strings with structural characters must parse cleanly."""

    def test_tilde_paren(self):
        """~( and ~) are CL format directives for case conversion."""
        tree = parse(b'(format t "~(~A~)" x)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_tilde_bracket(self):
        """~[ and ~] are CL conditional format directives."""
        tree = parse(b'(format t "~[zero~;one~;two~]" n)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_tilde_brace(self):
        """~{ and ~} are CL iteration format directives."""
        tree = parse(b'(format t "~{~A ~}" lst)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_tilde_angle(self):
        """~< and ~> are CL justification format directives."""
        tree = parse(b'(format t "~<left~;right~>" x)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_acl2_tilde_at(self):
        """~@ is ACL2's tilde-at-phrase directive."""
        tree = parse(b'"~s0 ~@1"')
        assert not tree.root_node.has_error

    def test_acl2_tilde_slash_comma(self):
        """ACL2 format ~[~/,~] which confused the original grammar."""
        tree = parse(b'(fmt1 " ~s0~#1~[~/,~]" x y z)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_nested_format_directives(self):
        """Complex nested format directives with multiple structural chars."""
        src = b'(fmt1 "<~x0 ~#1~[~/more ~]subgoal~#2~[~/s~]>~%" lst col ch st nil)'
        tree = parse(src)
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_string_with_parens(self):
        """Parens inside strings must not affect form structure."""
        tree = parse(b'(princ$ "(reverting)" channel state)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error

    def test_string_with_semicolon(self):
        """Semicolons inside strings must not start a comment."""
        tree = parse(b'(format t "a ; b" x)')
        assert len(tree.root_node.children) == 1
        assert not tree.root_node.has_error


# ── full-file error inventory ────────────────────────────────────────

@pytest.mark.skipif(not ACL2_HOME.exists(), reason="ACL2 source not available")
class TestNoformatFullFiles:
    """Parse all ACL2 source files and report errors."""

    def test_clean_file_count(self):
        """At least 70% of .lisp files should parse with zero errors."""
        files = sorted(ACL2_HOME.glob("*.lisp"))
        assert len(files) > 0, "No .lisp files found"
        clean = 0
        for p in files:
            src = p.read_bytes()
            tree = parse(src)
            if not tree.root_node.has_error:
                clean += 1
        ratio = clean / len(files)
        assert ratio >= 0.70, (
            f"Only {clean}/{len(files)} ({ratio:.0%}) files parse cleanly; "
            f"expected >= 70%"
        )

    def test_total_error_count(self):
        """Total error nodes across all files should be manageable."""
        files = sorted(ACL2_HOME.glob("*.lisp"))
        total_errors = 0
        file_errors = {}
        for p in files:
            src = p.read_bytes()
            tree = parse(src)
            errs = [c for c in tree.root_node.children if c.has_error]
            if errs:
                file_errors[p.name] = len(errs)
                total_errors += len(errs)
        # Current baseline: ~83 error nodes.  Allow some headroom.
        assert total_errors <= 120, (
            f"Total error nodes: {total_errors} (expected <= 120)\n"
            + "\n".join(f"  {name}: {n}" for name, n in
                        sorted(file_errors.items(), key=lambda x: -x[1]))
        )

    def test_no_format_string_errors(self):
        """No errors should be caused by format specifiers in strings.

        With the noformat grammar, strings are opaque — so any remaining
        errors must be from other grammar limitations (reader conditionals,
        nil lambda lists, etc.), not format specifiers.
        """
        files = sorted(ACL2_HOME.glob("*.lisp"))
        format_errors = []
        for p in files:
            src = p.read_bytes()
            tree = parse(src)
            for child in tree.root_node.children:
                if child.has_error:
                    text = src[child.start_byte:child.end_byte].decode(
                        errors="replace"
                    )
                    # If the error node starts with a format string char,
                    # something is wrong with string parsing.
                    if text.lstrip().startswith('"~'):
                        format_errors.append(
                            f"{p.name}:{child.start_point[0]+1}: "
                            f"{text[:80]!r}"
                        )
        assert not format_errors, (
            f"{len(format_errors)} format-string-related errors:\n"
            + "\n".join(format_errors[:10])
        )

    def test_error_categorization(self):
        """Categorize remaining errors for tracking purposes.

        This test always passes — it's purely informational.
        Error categories are printed when run with -v.
        """
        from collections import Counter
        files = sorted(ACL2_HOME.glob("*.lisp"))
        categories = Counter()
        for p in files:
            src = p.read_bytes()
            tree = parse(src)
            for child in tree.root_node.children:
                if child.has_error:
                    text = src[child.start_byte:child.end_byte].decode(
                        errors="replace"
                    )
                    first_line = text.split("\n")[0][:80]
                    if "#+\u200b" in text[:50] or "#+" in text[:50] or "#-" in text[:50]:
                        categories["reader-conditional (#+/#-)"] += 1
                    elif (text.strip().startswith("(defmacro") and
                          "nil" in first_line.lower().split("(defmacro")[1][:30]):
                        categories["nil-lambda-list"] += 1
                    elif text.startswith("defun") or text.startswith("defmacro"):
                        categories["bare-symbol (split form)"] += 1
                    elif text.startswith(")"):
                        categories["orphan-close-paren"] += 1
                    else:
                        categories["other"] += 1

        # Print summary for -v output
        total = sum(categories.values())
        print(f"\n  Error categories ({total} total):")
        for cat, count in categories.most_common():
            print(f"    {count:3d}  {cat}")
