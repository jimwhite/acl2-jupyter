"""Convert a parsed Common Lisp / ACL2 source file into a Jupyter notebook.

The conversion strategy groups top-level ``Node`` objects into cells:

1. **Comments** — Consecutive comment nodes (line comments, block comments,
   and blank lines between them) are merged into a single *markdown* cell.
   The source text is preserved exactly as-is, with no modifications
   (semicolons, ``#|``/``|#`` delimiters, etc. are kept verbatim).

2. **Code** — Each top-level form becomes its own *code* cell, with
   source text preserved exactly.

Every cell carries provenance metadata recording the source file URI and
the character span (byte offsets) in the original file.
"""

from __future__ import annotations

from pathlib import Path
from urllib.parse import urljoin
from urllib.request import pathname2url

import nbformat
from nbformat.v4 import new_code_cell, new_markdown_cell, new_notebook

from .languages import LanguageConfig, language_for_extension
from .parser import Node, NodeKind, parse, parse_file


# ---------------------------------------------------------------------------
# Grouping nodes → cells
# ---------------------------------------------------------------------------

# A cell record: (cell_type, source_text, start_byte, end_byte)
CellTuple = tuple[str, str, int, int]


def _is_comment_node(node: Node) -> bool:
    """Return True for line comments and block comments."""
    return node.kind in (NodeKind.LINE_COMMENT, NodeKind.BLOCK_COMMENT)


def _group_nodes_into_cells(
    nodes: list[Node],
    source: str,
) -> list[CellTuple]:
    """Group ``Node`` objects into ``(cell_type, source, start, end)`` tuples.

    Rules
    -----
    * Consecutive comments (line or block) — possibly separated by blank
      lines — are merged into a **single markdown cell**.  The original
      text from the first comment's start byte to the last comment's end
      byte is used verbatim, preserving internal blank lines.
    * Each top-level form becomes its own **code cell**.
    * Blank lines that are not between comments are discarded (they serve
      only as separators).
    """
    source_bytes = source.encode("utf-8")
    cells: list[CellTuple] = []

    # Accumulator for a run of comment nodes.
    comment_run: list[Node] = []  # only comment nodes (not blanks)
    run_start_byte: int | None = None
    run_end_byte: int | None = None
    # We also track whether we're in a "comment run" that may include
    # intervening blanks.
    in_comment_run = False

    def flush_comment_run() -> None:
        nonlocal comment_run, run_start_byte, run_end_byte, in_comment_run
        if not comment_run:
            return
        assert run_start_byte is not None and run_end_byte is not None
        # Extract the span from the original source bytes, preserving
        # everything (blank lines, comment chars, etc.) verbatim.
        text = source_bytes[run_start_byte:run_end_byte].decode("utf-8")
        # Strip a single trailing newline (standard notebook convention).
        text = text.rstrip("\n")
        cells.append(("markdown", text, run_start_byte, run_end_byte))
        comment_run = []
        run_start_byte = None
        run_end_byte = None
        in_comment_run = False

    for node in nodes:
        if _is_comment_node(node):
            if not in_comment_run:
                # Start a new comment run.
                in_comment_run = True
                run_start_byte = node.start_byte
            comment_run.append(node)
            run_end_byte = node.end_byte
            continue

        if node.kind == NodeKind.BLANK:
            if in_comment_run:
                # Blank line between comments — extend the span but don't
                # break the run.
                run_end_byte = node.end_byte
            # Blanks outside a comment run are simply ignored.
            continue

        # --- FORM ---
        # Flush any accumulated comment run first.
        flush_comment_run()
        text = node.text  # already stripped of trailing \n by the parser
        cells.append(("code", text, node.start_byte, node.end_byte))

    # Trailing comments at EOF.
    flush_comment_run()

    return cells


# ---------------------------------------------------------------------------
# Notebook construction
# ---------------------------------------------------------------------------

def _path_to_file_uri(path: Path) -> str:
    """Convert an absolute path to a ``file://`` URI."""
    return urljoin("file:", pathname2url(str(path.resolve())))


def _build_notebook(
    cells: list[CellTuple],
    lang: LanguageConfig,
    source_uri: str | None = None,
) -> nbformat.NotebookNode:
    """Build an ``nbformat`` v4 notebook from cell tuples.

    Each cell gets a ``provenance`` entry in its metadata recording
    the source URI and byte span.
    """
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

    for cell_type, source, start_byte, end_byte in cells:
        provenance = {"start": start_byte, "end": end_byte}
        if source_uri is not None:
            provenance["source"] = source_uri

        if cell_type == "markdown":
            cell = new_markdown_cell(source=source)
        else:
            cell = new_code_cell(source=source)
        cell.metadata["provenance"] = provenance
        nb.cells.append(cell)

    return nb


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def source_to_notebook(
    source: str | bytes,
    lang: LanguageConfig,
    source_uri: str | None = None,
) -> nbformat.NotebookNode:
    """Convert *source* text to a Jupyter notebook.

    Parameters
    ----------
    source : str | bytes
        Common Lisp or ACL2 source code.
    lang : LanguageConfig
        Language configuration to embed in notebook metadata.
    source_uri : str | None
        Optional ``file://`` URI recorded in each cell's provenance metadata.

    Returns
    -------
    nbformat.NotebookNode
    """
    if isinstance(source, bytes):
        source = source.decode("utf-8")
    nodes = parse(source)
    cells = _group_nodes_into_cells(nodes, source)
    return _build_notebook(cells, lang, source_uri=source_uri)


def file_to_notebook(path: str | Path) -> nbformat.NotebookNode:
    """Convert a ``.lsp`` / ``.lisp`` / ``.acl2`` file to a notebook.

    The language is inferred from the file extension.
    """
    path = Path(path)
    lang = language_for_extension(path.suffix)
    source = path.read_text(encoding="utf-8")
    uri = _path_to_file_uri(path)
    return source_to_notebook(source, lang, source_uri=uri)


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
