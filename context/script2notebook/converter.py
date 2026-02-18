"""Convert a parsed Common Lisp / ACL2 source file into a Jupyter notebook.

The conversion strategy groups top-level ``Node`` objects into cells:

1. **Detached comments** — A run of comment nodes (line comments, block
   comments, and blank lines between them) that is followed by a blank
   line before the next form is merged into a single *markdown* cell.

2. **Attached comments** — When one or more comment nodes immediately
   precede a top-level form with **no** blank line in between, they
   are included in the same *code* cell as the form.  If the run also
   contained earlier comments separated by a blank line, those earlier
   comments become a separate markdown cell.  Preceding blank lines are
   never included in the attached portion.

3. **Code** — Each top-level form becomes its own *code* cell, with
   source text preserved exactly.  If comments are attached (see above),
   they are part of the code cell's source.

Source text is preserved exactly as-is throughout—no modifications to
semicolons, ``#|``/``|#`` delimiters, whitespace, etc.

Metadata
~~~~~~~~

* **Notebook level** — ``source_file`` URI (when available).
* **Cell level** — ``provenance.start`` / ``provenance.end`` give byte
  offsets into the source file.  ``provenance.comment`` (when present)
  gives ``[start, end]`` *character* offsets of the comment text within
  the cell's ``source`` string (accounting for any bracket markup).
  ``provenance.comments`` (when present) is a list of ``[start, end]``
  character-offset pairs for inline comments within a code cell's form
  body (e.g. ``;`` comments inside a ``defun``).
"""

from __future__ import annotations

import enum
from pathlib import Path
from urllib.parse import urljoin
from urllib.request import pathname2url

import nbformat
from nbformat.v4 import new_code_cell, new_markdown_cell, new_raw_cell, new_notebook

import tree_sitter

from .languages import LanguageConfig, language_for_extension
from .parser import Node, NodeKind, parse, parse_file


class CommentCellType(enum.Enum):
    """What notebook cell type to use for comment blocks."""

    MARKDOWN = "markdown"
    RAW = "raw"


class MarkdownBracket(enum.Enum):
    """How to bracket comment text inside a markdown cell.

    Only applies when ``CommentCellType.MARKDOWN`` is selected.
    """

    NONE = "none"        # bare text
    FENCED = "fenced"    # wrapped in ``` fenced code block
    PRE = "pre"          # wrapped in <pre>…</pre>


# ---------------------------------------------------------------------------
# Grouping nodes → cells
# ---------------------------------------------------------------------------

# A cell record: (cell_type, source_text, start_byte, end_byte, comment_chars)
# *comment_chars* is the number of characters of comment text at the start of
# source_text (0 for pure-code cells, len(source_text) for markdown cells).
CellTuple = tuple[str, str, int, int, int]


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
    * **Detached comments** — A run of consecutive comment nodes (possibly
      separated by blank lines) that is followed by a blank line before
      the next form is emitted as a single **markdown** cell.  The original
      text from the first comment's start byte to the last comment's end
      byte is used verbatim, preserving internal blank lines.
    * **Attached comments** — When the run ends with a comment node that
      immediately precedes a form (no blank line between them), the tail
      of the run after the last internal blank line is attached to the
      form's **code** cell, and any earlier comments in the run become a
      markdown cell.  Preceding blank lines are excluded from the attached
      portion.
    * Each top-level form becomes its own **code** cell.
    * Blank lines that are not between comments are discarded (they serve
      only as separators).
    """
    source_bytes = source.encode("utf-8")
    cells: list[CellTuple] = []

    # Accumulator: ordered list of nodes (comments *and* blanks) in the
    # current comment run.  A run always starts with a comment node.
    run_nodes: list[Node] = []
    in_comment_run = False

    def _emit_markdown(node_list: list[Node]) -> None:
        """Emit the comment nodes in *node_list* as a markdown cell.

        The byte span runs from the first comment's start to the last
        comment's end, including any blank lines between comments but
        excluding trailing blanks.
        """
        comments = [n for n in node_list if _is_comment_node(n)]
        if not comments:
            return
        start = comments[0].start_byte
        end = comments[-1].end_byte
        text = source_bytes[start:end].decode("utf-8").rstrip("\n")
        cells.append(("markdown", text, start, end, len(text)))

    def _flush_run_and_form(form_node: Node) -> None:
        """Process the accumulated *run_nodes* when a form is encountered."""
        nonlocal run_nodes, in_comment_run

        if not run_nodes:
            # No comment run — emit the form alone.
            cells.append(("code", form_node.text,
                          form_node.start_byte, form_node.end_byte, 0))
            run_nodes = []
            in_comment_run = False
            return

        last = run_nodes[-1]

        if last.kind == NodeKind.BLANK:
            # Comment run ends with a blank → detached from the form.
            _emit_markdown(run_nodes)
            cells.append(("code", form_node.text,
                          form_node.start_byte, form_node.end_byte, 0))
        else:
            # Comment immediately precedes the form → attached.
            # Find the last blank in the run to split detached / attached.
            last_blank_idx: int | None = None
            for i in range(len(run_nodes) - 1, -1, -1):
                if run_nodes[i].kind == NodeKind.BLANK:
                    last_blank_idx = i
                    break

            if last_blank_idx is not None:
                markdown_part = run_nodes[:last_blank_idx]   # before the blank
                attached_part = run_nodes[last_blank_idx + 1:]  # after the blank
                _emit_markdown(markdown_part)
            else:
                # No blank in the run — entire run is attached.
                attached_part = run_nodes

            # Build code cell: attached comments + form.
            attached_start = attached_part[0].start_byte
            code_end = form_node.end_byte
            text = source_bytes[attached_start:code_end].decode("utf-8")
            text = text.rstrip("\n")
            # Compute the character length of the comment portion.
            # It runs from the start of the cell up to (but not including)
            # the form text.
            comment_chars = len(text) - len(form_node.text)
            cells.append(("code", text, attached_start, code_end, comment_chars))

        run_nodes = []
        in_comment_run = False

    for node in nodes:
        if _is_comment_node(node):
            if not in_comment_run:
                in_comment_run = True
            run_nodes.append(node)
            continue

        if node.kind == NodeKind.BLANK:
            if in_comment_run:
                # Blank line between comments — keep it in the run but
                # don't break the run.
                run_nodes.append(node)
            # Blanks outside a comment run are simply ignored.
            continue

        # --- FORM ---
        _flush_run_and_form(node)

    # Trailing comments at EOF.
    if run_nodes:
        _emit_markdown(run_nodes)

    return cells


# ---------------------------------------------------------------------------
# Notebook construction
# ---------------------------------------------------------------------------

def _path_to_file_uri(path: Path) -> str:
    """Convert an absolute path to a ``file://`` URI."""
    return urljoin("file:", pathname2url(str(path.resolve())))


def _format_comment_source(
    text: str,
    bracket: MarkdownBracket,
) -> str:
    """Wrap *text* according to the bracket style (markdown cells only)."""
    if bracket is MarkdownBracket.FENCED:
        return f"```\n{text}\n```"
    if bracket is MarkdownBracket.PRE:
        return f"<pre>\n{text}\n</pre>"
    return text


def _bracket_prefix_len(bracket: MarkdownBracket) -> int:
    """Return the number of characters the bracket prefix adds."""
    if bracket is MarkdownBracket.FENCED:
        return len("```\n")       # 4
    if bracket is MarkdownBracket.PRE:
        return len("<pre>\n")     # 6
    return 0


def _find_inline_comments(
    ts_tree: tree_sitter.Tree,
    cell_start_byte: int,
    cell_end_byte: int,
    form_start_byte: int,
    source_bytes: bytes,
) -> list[list[int, int]]:
    """Walk *ts_tree* to find comment nodes inside a form's byte range.

    Returns a list of ``[char_start, char_end]`` pairs giving character
    offsets within the cell's source string.  Only comments that fall
    inside the form body (i.e. starting at or after *form_start_byte*)
    are included—attached leading comments handled separately via
    ``provenance.comment``.
    """
    spans: list[list[int, int]] = []

    def _walk(node: tree_sitter.Node) -> None:
        # Skip nodes entirely outside the form's byte range.
        if node.end_byte <= form_start_byte or node.start_byte >= cell_end_byte:
            return
        if node.type in ("comment", "block_comment"):
            if node.start_byte >= form_start_byte:
                # Compute character offsets within the cell source.
                before = source_bytes[cell_start_byte:node.start_byte]
                char_start = len(before.decode("utf-8"))
                text = source_bytes[node.start_byte:node.end_byte]
                text_str = text.decode("utf-8").rstrip("\n")
                char_end = char_start + len(text_str)
                spans.append([char_start, char_end])
            return  # Don't recurse into comment children.
        for child in node.children:
            _walk(child)

    _walk(ts_tree.root_node)
    return spans


def _build_notebook(
    cells: list[CellTuple],
    lang: LanguageConfig,
    source_bytes: bytes,
    ts_tree: tree_sitter.Tree,
    source_uri: str | None = None,
    comment_cell_type: CommentCellType = CommentCellType.MARKDOWN,
    markdown_bracket: MarkdownBracket = MarkdownBracket.NONE,
) -> nbformat.NotebookNode:
    """Build an ``nbformat`` v4 notebook from cell tuples.

    * ``source_file`` is stored once in notebook-level metadata.
    * Each cell gets ``provenance`` metadata with ``start`` / ``end``
      byte offsets in the source file and, when the cell contains
      comment text, a ``comment`` key giving ``[start, end]`` character
      offsets of the comment within the cell's ``source`` string
      (accounting for any bracket markup).
    * Code cells may additionally have a ``comments`` key: a list of
      ``[start, end]`` character-offset pairs for inline comments
      within the form body (e.g. ``;`` comments inside a ``defun``).
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
    if source_uri is not None:
        nb.metadata["source_file"] = source_uri

    for cell_type, source, start_byte, end_byte, comment_chars in cells:
        provenance: dict = {"start": start_byte, "end": end_byte}

        if cell_type == "markdown":
            if comment_cell_type is CommentCellType.RAW:
                cell = new_raw_cell(source=source)
                # Raw cell: comment is the full source (no bracket).
                provenance["comment"] = [0, len(source)]
            else:
                formatted = _format_comment_source(source, markdown_bracket)
                cell = new_markdown_cell(source=formatted)
                prefix = _bracket_prefix_len(markdown_bracket)
                provenance["comment"] = [prefix, prefix + comment_chars]
        else:
            cell = new_code_cell(source=source)
            if comment_chars > 0:
                provenance["comment"] = [0, comment_chars]
            # Find inline comments within the form body.
            # The form starts at start_byte + the byte length of the
            # attached comment portion (comment_chars in chars, but we
            # need to find form_start_byte from cell_start_byte).
            form_start_byte = start_byte
            if comment_chars > 0:
                # Attached comment occupies comment_chars characters at
                # the start.  Compute the byte offset of the form.
                attached_bytes = source[:comment_chars].encode("utf-8")
                form_start_byte = start_byte + len(attached_bytes)
            inline = _find_inline_comments(
                ts_tree, start_byte, end_byte, form_start_byte, source_bytes,
            )
            if inline:
                provenance["comments"] = inline

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
    comment_cell_type: CommentCellType = CommentCellType.MARKDOWN,
    markdown_bracket: MarkdownBracket = MarkdownBracket.NONE,
) -> nbformat.NotebookNode:
    """Convert *source* text to a Jupyter notebook.

    Parameters
    ----------
    source : str | bytes
        Common Lisp or ACL2 source code.
    lang : LanguageConfig
        Language configuration to embed in notebook metadata.
    source_uri : str | None
        Optional ``file://`` URI stored in notebook-level metadata
        (``nb.metadata["source_file"]``).
    comment_cell_type : CommentCellType
        Cell type for comment blocks (``markdown`` or ``raw``).
    markdown_bracket : MarkdownBracket
        How to bracket comment text in markdown cells (``none``, ``fenced``,
        or ``pre``).  Ignored when *comment_cell_type* is ``raw``.

    Returns
    -------
    nbformat.NotebookNode
    """
    if isinstance(source, bytes):
        source = source.decode("utf-8")
    nodes, ts_tree = parse(source)
    cells = _group_nodes_into_cells(nodes, source)
    return _build_notebook(
        cells, lang,
        source_bytes=source.encode("utf-8"),
        ts_tree=ts_tree,
        source_uri=source_uri,
        comment_cell_type=comment_cell_type,
        markdown_bracket=markdown_bracket,
    )


def file_to_notebook(
    path: str | Path,
    comment_cell_type: CommentCellType = CommentCellType.MARKDOWN,
    markdown_bracket: MarkdownBracket = MarkdownBracket.NONE,
) -> nbformat.NotebookNode:
    """Convert a ``.lsp`` / ``.lisp`` / ``.acl2`` file to a notebook.

    The language is inferred from the file extension.
    """
    path = Path(path)
    lang = language_for_extension(path.suffix)
    source = path.read_text(encoding="utf-8")
    uri = _path_to_file_uri(path)
    return source_to_notebook(
        source, lang,
        source_uri=uri,
        comment_cell_type=comment_cell_type,
        markdown_bracket=markdown_bracket,
    )


def convert_file(
    input_path: str | Path,
    output_path: str | Path | None = None,
    comment_cell_type: CommentCellType = CommentCellType.MARKDOWN,
    markdown_bracket: MarkdownBracket = MarkdownBracket.NONE,
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

    nb = file_to_notebook(
        input_path,
        comment_cell_type=comment_cell_type,
        markdown_bracket=markdown_bracket,
    )
    nbformat.write(nb, str(output_path))
    return output_path
