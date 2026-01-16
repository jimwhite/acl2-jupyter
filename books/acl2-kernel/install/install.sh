#!/bin/bash
# Install ACL2 Jupyter Kernel
#
# Usage: ./install.sh [--user]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KERNEL_DIR="$SCRIPT_DIR/.."

# Default to user install
INSTALL_ARGS="--user"

if [ "$1" = "--sys-prefix" ]; then
    INSTALL_ARGS="--sys-prefix"
elif [ "$1" = "--prefix" ]; then
    INSTALL_ARGS="--prefix=$2"
fi

# Pre-populate the FASL cache by loading the kernel
# This prevents kernel startup timeout on first use
echo "Pre-compiling kernel dependencies ..."
cd "$KERNEL_DIR"
/home/acl2/saved_acl2 << 'EOF'
(include-book "top")
:q
(quit)
EOF

# Install kernel spec
echo "Installing ACL2 Jupyter Kernel..."
jupyter kernelspec install "$SCRIPT_DIR" --name=acl2-native $INSTALL_ARGS --replace

echo "ACL2 kernel installed successfully."
echo "You can now start Jupyter and select 'ACL2' as the kernel."
