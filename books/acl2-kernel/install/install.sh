#!/bin/bash
# Install ACL2 Jupyter Kernel
#
# Usage: ./install.sh [--user]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KERNEL_DIR="$SCRIPT_DIR"

# Default to user install
INSTALL_ARGS="--user"

if [ "$1" = "--sys-prefix" ]; then
    INSTALL_ARGS="--sys-prefix"
elif [ "$1" = "--prefix" ]; then
    INSTALL_ARGS="--prefix=$2"
fi

echo "Installing ACL2 Jupyter Kernel..."

# Install kernel spec
jupyter kernelspec install "$KERNEL_DIR" --name=acl2 $INSTALL_ARGS --replace

echo "ACL2 kernel installed successfully."
echo "You can now start Jupyter and select 'ACL2' as the kernel."
