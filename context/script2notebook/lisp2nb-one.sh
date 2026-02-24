#!/bin/sh
# Convert a single .lisp/.lsp file to .ipynb using lisp2nb.
# Usage: lisp2nb-one.sh LISP2NB_PATH [--force] SOURCE_FILE
# Exit 0 on success or skip, 1 on failure.
set -e

LISP2NB="$1"; shift

force=false
if [ "$1" = "--force" ]; then force=true; shift; fi

src="$1"
nb="${src%.*}.ipynb"

# Staleness check (skip if --force).
if [ "$force" = false ] && [ -f "$nb" ] && [ ! "$src" -nt "$nb" ]; then
  exit 0
fi

exec sbcl --noinform --non-interactive --disable-debugger \
  --load "$LISP2NB" \
  --eval "(lisp2nb:convert-file \"$src\" :markdown-bracket :fenced)" \
  --eval '(uiop:quit 0)' >/dev/null 2>&1
