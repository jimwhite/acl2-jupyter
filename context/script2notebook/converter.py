"""Convert a parsed Common Lisp / ACL2 source file into a Jupyter notebook.

The conversion strategy groups top-level ``Node`` objects into cells:

1. **Comment header** — A run of consecutive line comments at the very top
   of the file (before any code) becomes a single *markdown* cell.
   The leading semicolons and space are stripped.

2. **Standalone comments** — A group of consecutive line comments (or a
   block comment) separated from surrounding code by blank lines becomes
   a *markdown* cell.

3. **Code with attached comments** — Line comments immediately above a
   form (no intervening blank line) are included in the same *code* cell
   as the form they document.

4. **Code** — Top-level forms become *code* cells (one per form, unless
   they are in an uninterrupted run without blank-line separators, in
   which case they are joined into a single cell).
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Sequence

import nbformat
from nbformat.v4 import new_code_cell, new_markdown_cell, new_notebook

from .languages import LanguageConfig, language_for_extension
from .parser import Node, NodeKind, parse, parse_file


def _strip_line_comment_prefix(text: str) -> str:
    """Remove leading semicolons (and one optional space) from each line.

    ``"; foo"`` → ``"foo"``
    ``";;; bar"`` → ``"bar"``
    """
    lines = text.splitlines()
    stripped: list[str] = []
    for line in lines:
        # Remove all leading semicolons then optional single space.
        cleaned = re.sub(r"^;+\s?", "", line)
        stripped.append(cleaned)
    return "\n".join(stripped)


def _strip_block_comment(text: str) -> str:
    """Remove ``#|`` / ``|#`` delimiters from a block comment."""
    inner = text
    if inner.startswith("#|"):
        inner = inner[2:]
    if inner.endswith("|#"):
        inner = inner[:-2]
    # Remove leading/trailing blank lines that were just padding.
    return inner.strip("\n")


# ---------------------------------------------------------------------------
# Grouping nodes → cells
# ---------------------------------------------------------------------------

def _group_nodes_into_cells(
    nodes: list[Node],
) -> list[tuple[str, str]]:
    """Group ``Node`` objects into ``(cell_type, source)`` pairs.

    ``cell_type`` is ``"markdown"`` or ``"code"``.

    Algorithm
    ---------
    Walk the flat node list, keeping a small state machine:

    * Accumulate consecutive line-comments into a *pending_comments* buffer.
    * When a FORM is encountered:
      - If *pending_comments* is non-empty **and was not separated by a blank
        line** from the form, attach them as leading comments in the code cell.
      - If *pending_comments* **was** separated by a blank line, flush them
        as a standalone markdown cell first.
    * A blank line (``BLANK`` node) sets a *separated* flag so we know the
      comment block is detached from whatever follows it.
    * Block comments always become their own markdown cell.
    """
    cells: list[tuple[str, str]] = []
    pending_comments: list[Node] = []
    separated = False  # True if a blank line appeared after the last comment

    def flush_pending_as_markdown() -> None:
        nonlocal pending_comments, separated
        if not pending_comments:
            return
        md_text = _strip_line_comment_prefix(
            "\n".join(n.text for n in pending_comments)
        )
        cells.append(("markdown", md_text))
        pending_comments = []
        separated = False

    def flush_pending_as_code_prefix() -> str:
        """Return comment text to prepend to a code cell."""
        nonlocal pending_comments, separated
        if not pending_comments:
            return ""
        text = "\n".join(n.text for n in pending_comments) + "\n"
        pending_comments = []
        separated = False
        return text

    for node in nodes:
        if node.kind == NodeKind.BLANK:
            # A blank line after accumulated comments means they stand alone.
            if pending_comments:
                separated = True
            # A blank line can also be a separator between code cells, but
            # we don't need to track that explicitly — each FORM already
            # produces its own cell.
            continue

        if node.kind == NodeKind.LINE_COMMENT:
            # If we had pending comments that were separated by a blank line,
            # flush them as a standalone markdown cell before starting a new
            # comment accumulation.
            if separated and pending_comments:
                flush_pending_as_markdown()
            pending_comments.append(node)
            continue

        if node.kind == NodeKind.BLOCK_COMMENT:
            # Flush any pending line comments first.
            flush_pending_as_markdown()
            md_text = _strip_block_comment(node.text)
            cells.append(("markdown", md_text))
            separated = False
            continue

        # --- FORM ---
        if pending_comments:
            if separated:
                # Comment block is detached → markdown cell.
                flush_pending_as_markdown()
                code_text = node.text
            else:
                # Comments are attached to this form → include in code cell.
                code_text = flush_pending_as_code_prefix() + node.text
        else:
            code_text = node.text

        cells.append(("code", code_text))
        separated = False

    # If trailing comments remain, emit as markdown.
    flush_pending_as_markdown()

    return cells


# ---------------------------------------------------------------------------
# Notebook construction
# ---------------------------------------------------------------------------

def _build_notebook(
    cells: list[tuple[str, str]],
    lang: LanguageConfig,
) -> nbformat.NotebookNode:
    """Build an ``nbformat`` v4 notebook from ``(cell_type, source)`` pairs."""
    nb = new_notebook()

    nb.metadata["kernelspec"] = {
        "display_name": lang.display_name,
        "language": lang.name,
        "name": lang.effective_kernel_name,
    }
    nb.metadata["language_info"] = {
        "name": lang.name,
        "mimetype": lang.mime_type,
        "file_extension": lang.file_extensions[0],
        "codemirror_mode": lang.codemirror_mode,
        "pygments_lexer": lang.pygments_lexer,
    }

    for cell_type, source in cells:
        if cell_type == "markdown":
            nb.cells.append(new_markdown_cell(source=source))
        else:
            nb.cells.append(new_code_cell(source=source))

    return nb


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def source_to_notebook(
    source: str | bytes,
    lang: LanguageConfig,
) -> nbformat.NotebookNode:
    """Convert *source* text to a Jupyter notebook.

    Parameters
    ----------
    source : str | bytes
        Common Lisp or ACL2 source code.
    lang : LanguageConfig
        Language configuration to embed in notebook metadata.

    Returns
    -------
    nbformat.NotebookNode
    """
    nodes = parse(source)
    cells = _group_nodes_into_cells(nodes)
    return _build_notebook(cells, lang)


def file_to_notebook(path: str | Path) -> nbformat.NotebookNode:
    """Convert a ``.lsp`` / ``.lisp`` / ``.acl2`` file to a notebook.

    The language is inferred from the file extension.
    """
    path = Path(path)
    lang = language_for_extension(path.suffix)
    source = path.read_text(encoding="utf-8")
    return source_to_notebook(source, lang)


def convert_file(
    input_path: str | Path,
    output_path: str | Path | None = None,
) -> Path:
    """Convert *input_path* to a ``.ipynb`` notebook.

    If *output_path* is ``None``, the output is written next to the input
    with the ``.ipynb`` extension.

    Returns the resolved output path.
    """
    input_path = Path(input_path)
    if output_path is None:
        output_path = input_path.with_suffix(".ipynb")
    else:
        output_path = Path(output_path)

    nb = file_to_notebook(input_path)
    nbformat.write(nb, str(output_path))
    return output_path
