#!/bin/sh

# Start the ACL2 Jupyter Kernel in boot-strap mode.
#
# Unlike the normal kernel (which uses saved_acl2.core), this starts
# from init.lisp and builds the ACL2 world from scratch.
#
# Usage:
#   start-kernel-bootstrap.sh <connection-file> [pass]
#
# pass: 1 (default) or 2
#   Pass 1: load-acl2, enter-boot-strap-mode, ld-skip-proofsp=initialize-acl2
#   Pass 2: same + enter-boot-strap-pass-2, ld-skip-proofsp=include-book

set -e

CONNECTION_FILE="$1"
PASS="${2:-1}"

if [ -z "${CONNECTION_FILE}" ]; then
    echo "Usage: $0 <connection-file> [pass]" >&2
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
    --eval "(acl2-jupyter-kernel:start-boot-strap \"${CONNECTION_FILE}\" :pass ${PASS})"
