#!/bin/sh

# Start the ACL2 Jupyter Kernel.
#
# Quicklisp loading uses the same pattern as the Dockerfile:
#   sbcl --core saved_acl2.core --load quicklisp/setup.lisp --eval '(ql:quickload ...)'
#
# Then sbcl-restart enters LP, and the heredoc feeds LP commands
# (like demo.lsp feeds saved_acl2 for the Bridge):
#   (set-raw-mode-on!)           — needed for LP to call our raw CL function
#   (acl2-jupyter-kernel:start ...) — the start function IMMEDIATELY turns
#                                     raw mode OFF, so all evaluation runs
#                                     with raw-mode-p nil and *ld-level* > 0.
#
# Bridge's bridge::start is an ACL2 macro (defmacro-last) that LP can call
# without raw mode.  Our start is a raw CL function loaded via ASDF, so LP
# needs raw mode to resolve the package.  But raw mode must be off during
# evaluation, because throw-raw-ev-fncall calls interface-er (hard crash)
# when raw-mode-p is true — vs the catchable (throw 'raw-ev-fncall val)
# when raw-mode-p is nil and *ld-level* > 0.

set -e

CONNECTION_FILE="$1"
if [ -z "${CONNECTION_FILE}" ]; then
    echo "Usage: $0 <connection-file>" >&2
    exit 1
fi

ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"

export SBCL_HOME="${SBCL_HOME:-/usr/local/lib/sbcl/}"

exec /usr/local/bin/sbcl \
    --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 --disable-ldb \
    --core "${ACL2_HOME}/saved_acl2.core" \
    --end-runtime-options \
    --no-userinit \
    --load "${QUICKLISP_SETUP}" \
    --eval '(ql:quickload :acl2-jupyter-kernel :silent t)' \
    --eval '(sb-ext:disable-debugger)' \
    --eval '(acl2::sbcl-restart)' \
    <<ENDOFLISP
(set-raw-mode-on!)
(acl2-jupyter-kernel:start "${CONNECTION_FILE}")
ENDOFLISP
