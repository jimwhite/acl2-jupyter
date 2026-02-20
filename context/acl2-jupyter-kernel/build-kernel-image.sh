#!/bin/sh

# Build a saved ACL2 Jupyter Kernel core file.
#
# Uses save-lisp-and-die to create a .core file with the kernel system
# pre-loaded.  No shell script wrapper is generated — the kernelspec
# points the sbcl binary at this core directly.
#
# On startup (via kernel.json argv):
#   sbcl --core THIS.core --eval '(acl2::sbcl-restart)'
#        --eval '(acl2-jupyter-kernel:start)'
#
# The flow is:
#   sbcl-restart -> acl2-default-restart -> LP
#   -> *return-from-lp* causes LP to exit immediately
#   -> sbcl-restart returns -> (acl2-jupyter-kernel:start) runs
#   -> reads JUPYTER_CONNECTION_FILE env var -> starts kernel
#
# Usage: ./build-kernel-image.sh [output-dir]
#
# The output directory defaults to the directory containing this script.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
OUTPUT_DIR="${1:-$SCRIPT_DIR}"
ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"
SAVED_ACL2="${SAVED_ACL2:-${ACL2_HOME}/saved_acl2}"

CORE_NAME="acl2-jupyter-kernel.core"

echo "=== Building ACL2 Jupyter Kernel Core ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo "  Output:     ${OUTPUT_DIR}/${CORE_NAME}"
echo ""

# Ensure output directory exists
mkdir -p "${OUTPUT_DIR}"

# Pipe commands to saved_acl2:
#   1. :q to exit LP (get to raw Lisp)
#   2. Disable debugger so errors exit instead of hanging
#   3. Load Quicklisp + kernel system
#   4. Set *return-from-lp* so LP exits cleanly on restart
#   5. Reset *acl2-default-restart-complete* so restart re-initializes
#   6. save-lisp-and-die to create just the .core file
"${SAVED_ACL2}" <<EOF
(value :q)
(sb-ext:disable-debugger)
(load "${QUICKLISP_SETUP}")
(ql:quickload :acl2-jupyter-kernel :silent t)
(setq acl2::*return-from-lp* '(value :q))
(setq acl2::*acl2-default-restart-complete* nil)
(sb-ext:save-lisp-and-die "${OUTPUT_DIR}/${CORE_NAME}" :purify t)
EOF

echo ""
echo "=== Build complete ==="
echo "  Core: ${OUTPUT_DIR}/${CORE_NAME}"
echo ""
echo "To install the kernelspec, start the kernel system and run:"
echo "  (acl2-jupyter-kernel:install)"
echo ""
echo "Or install from saved_acl2:"
echo "  ${SAVED_ACL2}"
echo "  :q"
echo "  (load \"${QUICKLISP_SETUP}\")"
echo "  (ql:quickload :acl2-jupyter-kernel)"
echo "  (acl2-jupyter-kernel:install :core \"${OUTPUT_DIR}/${CORE_NAME}\")"
