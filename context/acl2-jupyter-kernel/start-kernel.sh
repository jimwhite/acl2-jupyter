#!/bin/sh

# Start the ACL2 Jupyter Kernel.
#
# No sbcl-restart, no LD, no set-raw-mode-on!.
# start sets up its own persistent LP context directly.

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
    --eval "(acl2-jupyter-kernel:start \"${CONNECTION_FILE}\")"
