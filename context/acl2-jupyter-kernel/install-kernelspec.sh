#!/bin/sh

# Install the ACL2 Jupyter kernelspec.
#
# This loads the kernel system into ACL2 and calls the installer,
# which writes kernel.json pointing sbcl at the pre-built .core file.
#
# Usage: ./install-kernelspec.sh [core-path]
#
# The core path defaults to acl2-jupyter-kernel.core in the same directory.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CORE_PATH="${1:-${SCRIPT_DIR}/acl2-jupyter-kernel.core}"
ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"
SAVED_ACL2="${SAVED_ACL2:-${ACL2_HOME}/saved_acl2}"

echo "=== Installing ACL2 Jupyter Kernelspec ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo "  Core:       ${CORE_PATH}"
echo ""

if [ ! -f "${CORE_PATH}" ]; then
    echo "ERROR: Core file not found: ${CORE_PATH}"
    echo "Run ./build-kernel-image.sh first."
    exit 1
fi

"${SAVED_ACL2}" <<EOF
(value :q)
(sb-ext:disable-debugger)
(load "${QUICKLISP_SETUP}")
(ql:quickload :acl2-jupyter-kernel :silent t)
(acl2-jupyter-kernel:install :core "${CORE_PATH}")
(sb-ext:exit)
EOF

echo ""
echo "=== Kernelspec installed ==="
echo "  Check with: jupyter kernelspec list"
