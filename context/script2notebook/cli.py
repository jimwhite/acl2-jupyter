"""Command-line interface for script2notebook.

Usage::

    python -m script2notebook input.lisp [-o output.ipynb]
    script2notebook input.lisp [-o output.ipynb]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .converter import convert_file
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
        "input",
        type=Path,
        help=f"Source file to convert (supported extensions: {supported})",
    )
    p.add_argument(
        "-o",
        "--output",
        type=Path,
        default=None,
        help="Output notebook path (default: <input>.ipynb)",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)

    input_path: Path = args.input
    if not input_path.exists():
        print(f"error: {input_path} does not exist", file=sys.stderr)
        return 1

    if input_path.suffix not in EXTENSION_MAP:
        supported = ", ".join(sorted(EXTENSION_MAP))
        print(
            f"error: unsupported extension {input_path.suffix!r} "
            f"(supported: {supported})",
            file=sys.stderr,
        )
        return 1

    out = convert_file(input_path, args.output)
    print(f"Wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
