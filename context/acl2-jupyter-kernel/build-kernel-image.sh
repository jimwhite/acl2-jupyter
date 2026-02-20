#!/bin/sh

# Build a saved ACL2 Jupyter Kernel binary using ACL2's save-exec.
#
# This produces BOTH a shell script (saved_acl2_jupyter) and a
# .core file (saved_acl2_jupyter.core), exactly like how saved_acl2
# itself is built.  The generated shell script includes all the
# necessary SBCL runtime flags:
#
#   --control-stack-size 64   (64 MB for ALL threads — fixes stack overflow)
#   --dynamic-space-size ...  (inherited from the ACL2 build)
#   --tls-limit 16384
#
# kernel.json argv is simply:
#   ["path/to/saved_acl2_jupyter", "{connection_file}"]
#
# The startup flow:
#   saved_acl2_jupyter {connection_file}
#   -> sbcl --control-stack-size 64 ... --eval '(acl2::sbcl-restart)'
#   -> sbcl-restart -> acl2-default-restart -> LP
#   -> LP runs :init-forms inside LD:
#        (set-raw-mode-on!)           ;; enable raw Lisp (no trust tag needed)
#        (acl2-jupyter-kernel:start)  ;; blocks, running Jupyter kernel
#        (value :q)                   ;; when/if kernel exits, exit LP
#   -> kernel has full ACL2 state (like the Bridge)
#
# Usage: ./build-kernel-image.sh [output-dir]

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OUTPUT_DIR="${1:-$SCRIPT_DIR}"
ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"
SAVED_ACL2="${SAVED_ACL2:-${ACL2_HOME}/saved_acl2}"

BINARY_NAME="saved_acl2_jupyter"

echo "=== Building ACL2 Jupyter Kernel (via save-exec) ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo "  Output:     ${OUTPUT_DIR}/${BINARY_NAME}"
echo "              ${OUTPUT_DIR}/${BINARY_NAME}.core"
echo ""

# Ensure output directory exists
mkdir -p "${OUTPUT_DIR}"

# Pipe commands to saved_acl2:
#   1. :q to exit LP (get to raw Lisp)
#   2. Disable debugger so errors exit instead of hanging
#   3. Load Quicklisp + kernel system
#   4. save-exec with :init-forms to start kernel INSIDE LP
#
# Using :init-forms (not :return-from-lp) so the kernel runs inside
# ACL2's LD like the Bridge does.  This ensures full ACL2 state
# (CBD, world, include-book machinery) is available to kernel threads.
#
# After :q we're at raw Lisp with *package* = ACL2,
# so save-exec (an ACL2 macro) is directly accessible.
"${SAVED_ACL2}" <<EOF
(value :q)
(sb-ext:disable-debugger)
(load "${QUICKLISP_SETUP}")
(ql:quickload :acl2-jupyter-kernel :silent t)
(save-exec "${OUTPUT_DIR}/${BINARY_NAME}" nil
           :init-forms '((set-raw-mode-on!)
                         (acl2-jupyter-kernel:start)
                         (value :q)))
EOF

echo ""
echo "=== Build complete ==="
echo "  Binary: ${OUTPUT_DIR}/${BINARY_NAME}"
echo "  Core:   ${OUTPUT_DIR}/${BINARY_NAME}.core"
echo ""
echo "To install the kernelspec, run:"
echo "  ./install-kernelspec.sh"
