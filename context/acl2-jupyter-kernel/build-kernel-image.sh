#!/bin/sh

# Build a saved ACL2 Jupyter Kernel binary.
#
# Uses ACL2's own save-exec to create a saved binary (shell script + core),
# exactly as ACL2 creates saved_acl2.  The result is a standard saved ACL2
# binary with the Jupyter kernel system pre-loaded.
#
# On startup the binary runs:
#   sbcl-restart -> acl2-default-restart -> LP -> return-from-lp (exits LP)
#                -> (acl2-jupyter-kernel:start) via --eval toplevel-args
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

BINARY_NAME="saved_acl2_jupyter_kernel"

echo "=== Building ACL2 Jupyter Kernel Binary ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo "  Output:     ${OUTPUT_DIR}/${BINARY_NAME}"
echo ""

# Ensure output directory exists
mkdir -p "${OUTPUT_DIR}"

# Pipe commands to saved_acl2:
#   1. :q to exit LP (get to raw Lisp, ld-level 0)
#   2. Load Quicklisp + kernel system
#   3. save-exec with :return-from-lp to exit LP on restart,
#      and :toplevel-args to run the kernel after LP exits
"${SAVED_ACL2}" <<EOF
(value :q)
(sb-ext:disable-debugger)
(load "${QUICKLISP_SETUP}")
(ql:quickload :acl2-jupyter-kernel :silent t)
(save-exec "${OUTPUT_DIR}/${BINARY_NAME}" nil
  :return-from-lp '(value :q)
  :toplevel-args "--eval '(acl2-jupyter-kernel:start)'")
EOF

echo ""
echo "=== Build complete ==="
echo "  Binary: ${OUTPUT_DIR}/${BINARY_NAME}"
echo ""
echo "To install the kernelspec:"
echo "  ${OUTPUT_DIR}/${BINARY_NAME}  # starts ACL2, then at raw Lisp:"
echo "  (acl2-jupyter-kernel:install :launcher \"${OUTPUT_DIR}/${BINARY_NAME}\")"
