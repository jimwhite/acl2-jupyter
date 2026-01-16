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

# Certify the kernel and all dependencies (including system books)
# This ensures everything is certified before first use
echo "Certifying kernel and dependencies (this may take a few minutes on first run)..."
/home/acl2/books/build/cert.pl --acl2 /home/acl2/saved_acl2 "$KERNEL_DIR/top.lisp"

# Pre-populate the FASL cache by loading the kernel
# This compiles quicklisp dependencies (pzmq, cffi, etc.)
echo "Pre-compiling Quicklisp dependencies..."
cd "$KERNEL_DIR"
/home/acl2/saved_acl2 << 'EOF'
(include-book "top" :ttags ((:quicklisp) (:quicklisp.bordeaux) (:acl2-kernel-pzmq) (:acl2-kernel-raw)))
:q
(quit)
EOF

# Install kernel spec
echo "Installing ACL2 Jupyter Kernel..."
jupyter kernelspec install "$SCRIPT_DIR" --name=acl2-native $INSTALL_ARGS --replace

echo "ACL2 kernel installed successfully."
echo "You can now start Jupyter and select 'ACL2' as the kernel."
