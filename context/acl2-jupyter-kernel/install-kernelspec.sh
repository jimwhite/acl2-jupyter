#!/bin/sh

# Install the ACL2 Jupyter kernelspec.
#
# This loads the kernel system into ACL2 and calls the installer,
# which writes kernel.json with direct sbcl argv (no shell script wrapper).
# Paths to sbcl, saved_acl2.core, and quicklisp are auto-detected.
#
# Usage: ./install-kernelspec.sh

set -e

ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"
SAVED_ACL2="${SAVED_ACL2:-${ACL2_HOME}/saved_acl2}"

echo "=== Installing ACL2 Jupyter Kernelspec ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo ""

"${SAVED_ACL2}" <<EOF
(value :q)
(sb-ext:disable-debugger)
(load "${QUICKLISP_SETUP}")
(ql:quickload :acl2-jupyter-kernel :silent t)
(acl2-jupyter-kernel:install)
(sb-ext:exit)
EOF

echo ""
echo "=== Kernelspec installed ==="
echo "  Check with: jupyter kernelspec list"
