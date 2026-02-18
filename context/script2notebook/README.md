# script2notebook

Convert Common Lisp and ACL2 source files to Jupyter notebooks using
[tree-sitter](https://tree-sitter.github.io/).

Each top-level form becomes a **code cell**. Comments are grouped into
**markdown cells** (or raw cells), preserving the original source text
verbatim—no semicolons are stripped, no delimiters are altered.

## Installation

```bash
pip install -e .
```

Dependencies (pulled in automatically):

| Package                  | Purpose                           |
|--------------------------|-----------------------------------|
| `nbformat >=5.10`       | Jupyter notebook read/write       |
| `tree-sitter >=0.25`    | Incremental parsing framework     |
| `tree-sitter-commonlisp` | Common Lisp / ACL2 grammar       |

For development add `pytest`:

```bash
pip install -e ".[dev]"
```

## Quick start

```bash
# Single file
script2notebook input.lisp

# Multiple files
script2notebook a.lisp b.acl2 c.lsp

# Entire directory tree (recursive)
script2notebook src/

# Specify output location
script2notebook input.lisp -o output.ipynb

# Directory → directory (preserves structure)
script2notebook src/ -o notebooks/
```

## Supported file extensions

| Extension | Language    |
|-----------|------------|
| `.lisp`   | ACL2       |
| `.acl2`   | ACL2       |
| `.lsp`    | Common Lisp|

## Command-line options

```
script2notebook [options] input [input ...]
```

### Comment cell type

| Flag                        | Effect                                      |
|-----------------------------|---------------------------------------------|
| `--comment-cell=markdown`   | Comment blocks → markdown cells (default)   |
| `--comment-cell=raw`        | Comment blocks → raw cells                  |
| `--raw`                     | Shorthand for `--comment-cell=raw`          |

### Markdown bracket style

Controls how comment text is wrapped inside markdown cells. Ignored when
`--comment-cell=raw`.

| Flag                          | Result                           |
|-------------------------------|----------------------------------|
| `--markdown-bracket=none`     | Bare text (default)              |
| `--markdown-bracket=fenced`   | Wrapped in `` ``` `` fenced block|
| `--markdown-bracket=pre`      | Wrapped in `<pre>…</pre>`       |
| `--fenced`                    | Shorthand for fenced             |
| `--pre`                       | Shorthand for pre                |
| `--plain`                     | Shorthand for none               |

### Other flags

| Flag      | Effect                                               |
|-----------|------------------------------------------------------|
| `--force` | Regenerate even when the notebook is newer than the source |

## How cells are created

### Comment grouping

The converter distinguishes **detached** and **attached** comments:

- **Detached** — a run of comment lines (`;` or `#|…|#`) followed by a
  blank line before the next form.  These become a markdown (or raw) cell.

- **Attached** — comment lines immediately preceding a form with *no*
  blank line in between.  These are included in the same code cell as the
  form.

```lisp
; This is a detached comment.
; It becomes its own markdown cell.

; This is attached to the defun below.
(defun foo (x) x)
```

Produces three cells: markdown → code (with attached comment + defun).

When a run of comments contains an internal blank line, the portion
before the last blank becomes a separate markdown cell; the portion
after it is attached to the form.

### Code cells

Each top-level s-expression becomes a single code cell. The source text
is preserved exactly—spacing, indentation, semicolons, block-comment
delimiters, and all.

## Cell metadata

Every cell carries a `provenance` key in its metadata recording its
origin in the source file.

### All cells

```json
{
  "provenance": {
    "start": 0,
    "end": 42
  }
}
```

`start` and `end` are **byte offsets** into the original source file.

### Comment span (`provenance.comment`)

Present on markdown/raw cells and code cells with attached leading
comments. The value is `[start, end]`—**character offsets** into the
cell's `source` string pointing at the comment text (accounting for any
bracket wrapping like `` ``` `` or `<pre>`).

```json
{
  "provenance": {
    "start": 0,
    "end": 120,
    "comment": [4, 50]
  }
}
```

### Inline comment/docstring spans (`provenance.comments`)

Present on code cells that contain comments or docstrings *inside* the
form body. The value is a list of `[start, end]` character-offset pairs
into the cell's `source` string, sorted by position.

Two kinds of spans are detected:

1. **Inline comments** — `;` line comments and `#|…|#` block comments
   nested inside a form (e.g. comments inside a `defun` body).

2. **Docstrings** — String literals at position 4 of a definition form
   whose first term contains `def` (e.g. `defun`, `defmacro`, `define`,
   `defun-sk`). A string is only treated as a docstring when it is *not*
   the last term of the form. Consecutive strings are all included.

```json
{
  "provenance": {
    "start": 0,
    "end": 200,
    "comment": [0, 15],
    "comments": [[30, 58], [62, 78]]
  }
}
```

## Python API

### `source_to_notebook`

```python
from script2notebook.converter import source_to_notebook, MarkdownBracket
from script2notebook.languages import ACL2

nb = source_to_notebook(
    source,                                    # str or bytes
    ACL2,                                      # LanguageConfig
    source_uri="file:///path/to/input.lisp",   # optional
    markdown_bracket=MarkdownBracket.FENCED,   # optional
)
```

### `file_to_notebook`

```python
from script2notebook.converter import file_to_notebook

nb = file_to_notebook("input.lisp")
```

Language is inferred from the file extension. Returns an
`nbformat.NotebookNode`.

### `convert_file`

```python
from script2notebook.converter import convert_file

output_path = convert_file("input.lisp", "output.ipynb")
```

Writes the notebook to disk and returns the resolved output `Path`.

### `parse` / `parse_file`

Low-level access to the tree-sitter parse:

```python
from script2notebook.parser import parse, parse_file

nodes, tree = parse(source_text)
nodes, tree = parse_file("input.lisp")
```

Returns a `(list[Node], tree_sitter.Tree)` tuple. Each `Node` has:

| Field        | Type       | Description                        |
|--------------|------------|------------------------------------|
| `kind`       | `NodeKind` | `LINE_COMMENT`, `BLOCK_COMMENT`, `FORM`, or `BLANK` |
| `text`       | `str`      | Verbatim source text (trailing newlines stripped) |
| `start_line` | `int`      | 0-based line number                |
| `end_line`   | `int`      | 0-based, inclusive                 |
| `start_byte` | `int`      | Byte offset in source              |
| `end_byte`   | `int`      | Byte offset (exclusive)            |

## Architecture

```
cli.py          Command-line entry point (argparse)
parser.py       tree-sitter → flat list of Nodes
converter.py    Nodes → grouped cells → nbformat notebook
languages.py    LanguageConfig for ACL2 and Common Lisp
```

The pipeline is:

1. **Parse** — `parser.parse()` feeds the source through tree-sitter and
   produces a flat, ordered list of `Node` objects plus the raw
   `tree_sitter.Tree`.

2. **Group** — `converter._group_nodes_into_cells()` walks the node list
   and applies the attached/detached comment rules to produce
   `CellTuple` records.

3. **Build** — `converter._build_notebook()` turns cell tuples into
   `nbformat` cells, computes provenance metadata, walks the tree-sitter
   tree for inline comments, and detects docstrings.

4. **Write** — `nbformat.write()` serialises the notebook to `.ipynb`.

## Running tests

```bash
python -m pytest tests/ -v
```

## License

BSD-3-Clause (see `LICENSE` in the repository root).
