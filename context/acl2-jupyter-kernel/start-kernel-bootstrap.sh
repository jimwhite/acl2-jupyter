#!/bin/sh

# Start the ACL2 Jupyter Kernel in boot-strap mode.
#
# Unlike the normal kernel (which uses saved_acl2.core), this starts
# from init.lisp and builds the ACL2 world from scratch.
#
# Usage:
#   start-kernel-bootstrap.sh <connection-file>
#
# The kernel always starts in pass 1 mode.  The Python build script
# sends the :bootstrap-enter-pass-2 directive to transition to pass 2.

set -e

CONNECTION_FILE="$1"

if [ -z "${CONNECTION_FILE}" ]; then
    echo "Usage: $0 <connection-file>" >&2
    exit 1
fi

ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"

export SBCL_HOME="${SBCL_HOME:-/usr/local/lib/sbcl/}"

cd "${ACL2_HOME}"

exec /usr/local/bin/sbcl \
    --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 \
    --disable-ldb \
    --end-runtime-options \
    --no-userinit --disable-debugger \
    --load "init.lisp" \
    --eval '(acl2::load-acl2 :load-acl2-proclaims acl2::*do-proclaims*)' \
    --load "${QUICKLISP_SETUP}" \
    --eval '(ql:quickload :acl2-jupyter-kernel :silent t)' \
    --eval "(acl2-jupyter-kernel:start-boot-strap \"${CONNECTION_FILE}\")"
