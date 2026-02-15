"""Tree-sitter based parser for Common Lisp / ACL2 source files.

Parses source text into a flat sequence of ``Node`` objects, each
representing a top-level syntactic element (comment, block comment,
or form/expression).  Downstream code (:mod:`converter`) groups these
into notebook cells.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass
from pathlib import Path

import tree_sitter
import tree_sitter_commonlisp as tscl


# Build the tree-sitter Language once at module level.
_LANGUAGE = tree_sitter.Language(tscl.language())


class NodeKind(enum.Enum):
    """Classification of a top-level tree-sitter node."""

    LINE_COMMENT = "comment"
    BLOCK_COMMENT = "block_comment"
    FORM = "form"          # any s-expression / atom
    BLANK = "blank"        # blank line(s) between nodes


@dataclass
class Node:
    """A single top-level element extracted from the source file."""

    kind: NodeKind
    text: str
    start_line: int        # 0-based line index in the source
    end_line: int          # 0-based, inclusive


def parse(source: str | bytes) -> list[Node]:
    """Parse *source* into a list of top-level ``Node`` objects.

    The returned list preserves source order and includes ``BLANK``
    nodes for runs of empty lines between real content, which the
    converter uses as cell boundary hints.
    """
    if isinstance(source, str):
        source_bytes = source.encode("utf-8")
        source_str = source
    else:
        source_bytes = source
        source_str = source.decode("utf-8")

    parser = tree_sitter.Parser(_LANGUAGE)
    tree = parser.parse(source_bytes)

    source_lines = source_str.splitlines(keepends=True)
    nodes: list[Node] = []

    # Track the last *content* line covered so we can emit BLANK nodes for
    # gaps.  tree-sitter comment nodes often include the trailing newline,
    # so end_point may be (next_line, 0).  We normalise to the last line
    # that actually contains content.
    last_content_line = -1

    for child in tree.root_node.children:
        child_start = child.start_point[0]
        # Normalise end_line: if the node ends at column 0 of the next
        # line (i.e. only the trailing newline is there), back up one line.
        if child.end_point[1] == 0 and child.end_point[0] > child.start_point[0]:
            child_content_end = child.end_point[0] - 1
        else:
            child_content_end = child.end_point[0]

        child_text = source_bytes[child.start_byte:child.end_byte].decode("utf-8")
        # Strip trailing newline that tree-sitter includes in comment nodes.
        child_text = child_text.rstrip("\n")

        # Emit BLANK node for any gap of empty lines.
        if child_start > last_content_line + 1:
            gap_start = last_content_line + 1
            gap_end = child_start - 1
            gap_text = "".join(source_lines[gap_start:gap_end + 1])
            if gap_text.strip() == "":
                nodes.append(Node(NodeKind.BLANK, gap_text, gap_start, gap_end))

        # Classify the tree-sitter node.
        if child.type == "comment":
            kind = NodeKind.LINE_COMMENT
        elif child.type == "block_comment":
            kind = NodeKind.BLOCK_COMMENT
        else:
            kind = NodeKind.FORM

        nodes.append(Node(kind, child_text, child_start, child_content_end))
        last_content_line = child_content_end

    return nodes


def parse_file(path: str | Path) -> list[Node]:
    """Convenience wrapper: read *path* and parse it."""
    text = Path(path).read_text(encoding="utf-8")
    return parse(text)
