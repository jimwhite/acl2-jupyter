#!/bin/sh

# Install the ACL2 Jupyter kernelspec.
#
# This loads the kernel system into ACL2 and calls the installer,
# which writes kernel.json pointing at start-kernel.sh.
#
# Usage: ./install-kernelspec.sh [launcher-path]
#
# The launcher path defaults to start-kernel.sh in the same directory.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LAUNCHER_PATH="${1:-${SCRIPT_DIR}/start-kernel.sh}"
ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"
SAVED_ACL2="${SAVED_ACL2:-${ACL2_HOME}/saved_acl2}"

echo "=== Installing ACL2 Jupyter Kernelspec ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo "  Launcher:   ${LAUNCHER_PATH}"
echo ""

if [ ! -f "${LAUNCHER_PATH}" ]; then
    echo "ERROR: Launcher script not found: ${LAUNCHER_PATH}"
    exit 1
fi

"${SAVED_ACL2}" <<EOF
(value :q)
(sb-ext:disable-debugger)
(load "${QUICKLISP_SETUP}")
(ql:quickload :acl2-jupyter-kernel :silent t)
(acl2-jupyter-kernel:install :binary "${LAUNCHER_PATH}")
(sb-ext:exit)
EOF

echo ""
echo "=== Kernelspec installed ==="
echo "  Check with: jupyter kernelspec list"
