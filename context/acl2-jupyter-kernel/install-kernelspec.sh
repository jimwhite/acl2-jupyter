#!/bin/sh

# Install the ACL2 Jupyter kernelspec.
#
# This loads the kernel system into ACL2 and calls the installer,
# which writes kernel.json with direct sbcl argv (no shell script wrapper).
# Paths to sbcl, saved_acl2.core, and quicklisp are auto-detected.
#
# If the acl2-jupyter-kernel ASDF system isn't already in Quicklisp's
# local-projects, copy it there.  The script locates itself via $0
# so it works from any working directory.
#
# Usage: ./install-kernelspec.sh

set -e

ACL2_HOME="${ACL2_HOME:-/home/acl2}"
QUICKLISP_SETUP="${QUICKLISP_SETUP:-${HOME}/quicklisp/setup.lisp}"
SAVED_ACL2="${SAVED_ACL2:-${ACL2_HOME}/saved_acl2}"
LOCAL_PROJECTS="${HOME}/quicklisp/local-projects"

# Resolve the directory where this script lives (= where the .asd is)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Ensure acl2-jupyter-kernel is in Quicklisp local-projects (copy if missing or stale)
TARGET="${LOCAL_PROJECTS}/acl2-jupyter-kernel"
NEEDS_COPY=0
if [ ! -e "${TARGET}/acl2-jupyter-kernel.asd" ]; then
    NEEDS_COPY=1
else
    # Update if any source file is newer than the target .asd
    for f in "${SCRIPT_DIR}"/*.lisp "${SCRIPT_DIR}"/*.asd; do
        if [ "$f" -nt "${TARGET}/acl2-jupyter-kernel.asd" ]; then
            NEEDS_COPY=1
            break
        fi
    done
fi
if [ "${NEEDS_COPY}" = "1" ]; then
    echo "Copying acl2-jupyter-kernel into ${LOCAL_PROJECTS}/"
    mkdir -p "${TARGET}"
    cp -a "${SCRIPT_DIR}"/*.lisp "${SCRIPT_DIR}"/*.asd "${TARGET}/"
fi

# Also install the VSCode extension if it's alongside us and not yet installed
EXTENSION_SRC="${SCRIPT_DIR}/../extension/acl2-language"
EXTENSION_DST="${HOME}/.vscode-server/extensions/acl2-jupyter.acl2-language-0.1.0"
if [ -d "${EXTENSION_SRC}" ] && [ ! -e "${EXTENSION_DST}/package.json" ]; then
    echo "Copying VSCode extension into ${EXTENSION_DST}"
    mkdir -p "${EXTENSION_DST}"
    cp -a "${EXTENSION_SRC}"/* "${EXTENSION_DST}/"
fi

# Kernel start options — set explicitly rather than relying on defaults.
# These become flags in kernel.json's argv start form.
export ACL2_JUPYTER_EVENT_FORMS="${ACL2_JUPYTER_EVENT_FORMS:-1}"
export ACL2_JUPYTER_FULL_WORLD="${ACL2_JUPYTER_FULL_WORLD:-0}"
export ACL2_JUPYTER_DEEP_EVENTS="${ACL2_JUPYTER_DEEP_EVENTS:-0}"

echo "=== Installing ACL2 Jupyter Kernelspec ==="
echo "  saved_acl2: ${SAVED_ACL2}"
echo "  event-forms: ${ACL2_JUPYTER_EVENT_FORMS}"
echo "  full-world:  ${ACL2_JUPYTER_FULL_WORLD}"
echo "  deep-events: ${ACL2_JUPYTER_DEEP_EVENTS}"
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
