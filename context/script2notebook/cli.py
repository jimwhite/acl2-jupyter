"""Command-line interface for script2notebook.

Usage::

    script2notebook input.lisp [input2.lisp ...] [-o output.ipynb]
    script2notebook src/        # recursively convert all matching files
    script2notebook --raw --fenced input.lisp
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

from .converter import CommentCellType, MarkdownBracket, convert_file
from .languages import EXTENSION_MAP


def _build_parser() -> argparse.ArgumentParser:
    supported = ", ".join(sorted(EXTENSION_MAP))
    p = argparse.ArgumentParser(
        prog="script2notebook",
        description=(
            "Convert Common Lisp / ACL2 scripts to Jupyter notebooks "
            "using tree-sitter."
        ),
    )
    p.add_argument(
        "inputs",
        nargs="+",
        type=Path,
        metavar="input",
        help=(
            f"Source file(s) or director(ies) to convert "
            f"(supported extensions: {supported})"
        ),
    )
    p.add_argument(
        "-o",
        "--output",
        type=Path,
        default=None,
        help=(
            "Output path.  For a single file input this is the notebook "
            "file path.  When multiple files or directories are involved "
            "this must be a directory; sub-directory structure relative "
            "to each input root is preserved."
        ),
    )

    # ── comment cell type ────────────────────────────────────────────
    ctype = p.add_mutually_exclusive_group()
    ctype.add_argument(
        "--comment-cell",
        choices=["markdown", "raw"],
        default=None,
        help="Cell type for comment blocks (default: markdown)",
    )
    ctype.add_argument(
        "--raw",
        action="store_true",
        default=False,
        help="Shorthand for --comment-cell=raw",
    )

    # ── markdown bracket ─────────────────────────────────────────────
    bracket = p.add_mutually_exclusive_group()
    bracket.add_argument(
        "--markdown-bracket",
        choices=["none", "fenced", "pre"],
        default=None,
        help=(
            "How to bracket comment text in markdown cells: "
            "none (default), fenced (```), or pre (<pre>). "
            "Ignored when --comment-cell=raw / --raw."
        ),
    )
    bracket.add_argument(
        "--fenced",
        action="store_true",
        default=False,
        help="Shorthand for --markdown-bracket=fenced",
    )
    bracket.add_argument(
        "--pre",
        action="store_true",
        default=False,
        help="Shorthand for --markdown-bracket=pre",
    )
    bracket.add_argument(
        "--plain",
        action="store_true",
        default=False,
        help="Shorthand for --markdown-bracket=none (the default)",
    )

    # ── force rebuild ────────────────────────────────────────────────
    p.add_argument(
        "--force",
        action="store_true",
        default=False,
        help="Convert even when the notebook is newer than the source",
    )
    return p


# ── helpers ──────────────────────────────────────────────────────────

def _resolve_comment_cell_type(args: argparse.Namespace) -> CommentCellType:
    if args.raw:
        return CommentCellType.RAW
    if args.comment_cell == "raw":
        return CommentCellType.RAW
    return CommentCellType.MARKDOWN


def _resolve_markdown_bracket(args: argparse.Namespace) -> MarkdownBracket:
    if args.fenced:
        return MarkdownBracket.FENCED
    if args.pre:
        return MarkdownBracket.PRE
    if args.markdown_bracket == "fenced":
        return MarkdownBracket.FENCED
    if args.markdown_bracket == "pre":
        return MarkdownBracket.PRE
    return MarkdownBracket.NONE


# (source_path, input_root_or_None)
_FileEntry = tuple[Path, Path | None]


def _collect_files(inputs: list[Path]) -> list[_FileEntry]:
    """Expand directories into matching source files (recursive).

    Returns a list of ``(source_path, root_dir)`` tuples.  *root_dir* is
    the directory input that was expanded (used for computing relative
    output paths), or ``None`` when the input was a plain file.
    """
    extensions = set(EXTENSION_MAP)
    files: list[_FileEntry] = []
    for p in inputs:
        if p.is_dir():
            for root, _dirs, names in os.walk(p):
                for name in sorted(names):
                    fp = Path(root) / name
                    if fp.suffix in extensions:
                        files.append((fp, p))
        else:
            files.append((p, None))
    return files


def _needs_conversion(source: Path, notebook: Path, force: bool) -> bool:
    """Return True when the notebook should be (re)generated."""
    if force:
        return True
    if not notebook.exists():
        return True
    return source.stat().st_mtime > notebook.stat().st_mtime


# ── entry point ──────────────────────────────────────────────────────

def _resolve_output(
    source: Path,
    root: Path | None,
    output_arg: Path | None,
    is_output_dir: bool,
) -> Path:
    """Compute the notebook output path for *source*."""
    if output_arg is None:
        return source.with_suffix(".ipynb")

    if is_output_dir:
        if root is not None:
            # Preserve sub-directory structure relative to the input root.
            rel = source.relative_to(root)
        else:
            # Plain file input — just the filename.
            rel = Path(source.name)
        return (output_arg / rel).with_suffix(".ipynb")

    # output_arg is a single file path.
    return output_arg


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    entries = _collect_files(args.inputs)

    if not entries:
        print("error: no matching source files found", file=sys.stderr)
        return 1

    # Decide whether -o is a directory target.
    multiple = len(entries) > 1
    is_output_dir = False
    if args.output is not None:
        if multiple or any(root is not None for _, root in entries):
            # Multiple files or directory input → -o must be a directory.
            is_output_dir = True
        elif args.output.is_dir() or str(args.output).endswith(os.sep):
            is_output_dir = True

    comment_cell_type = _resolve_comment_cell_type(args)
    markdown_bracket = _resolve_markdown_bracket(args)
    errors = 0

    for source, root in entries:
        if not source.exists():
            print(f"error: {source} does not exist", file=sys.stderr)
            errors += 1
            continue

        if source.suffix not in EXTENSION_MAP:
            supported = ", ".join(sorted(EXTENSION_MAP))
            print(
                f"error: unsupported extension {source.suffix!r} "
                f"(supported: {supported})",
                file=sys.stderr,
            )
            errors += 1
            continue

        output = _resolve_output(source, root, args.output, is_output_dir)

        if not _needs_conversion(source, output, args.force):
            continue

        # Ensure the output directory exists.
        output.parent.mkdir(parents=True, exist_ok=True)

        try:
            out = convert_file(
                source,
                output,
                comment_cell_type=comment_cell_type,
                markdown_bracket=markdown_bracket,
            )
            print(f"Wrote {out}")
        except Exception as exc:  # noqa: BLE001
            print(f"error: {source}: {exc}", file=sys.stderr)
            errors += 1

    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
