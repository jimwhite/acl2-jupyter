#!/bin/bash
# Test script for ACL2 GUIX package

set -e

echo "ACL2 GUIX Package Test Script"
echo "=============================="

echo
echo "This script demonstrates how to use the ACL2 GUIX package."
echo "Note: This requires GUIX to be installed on your system."
echo

# Check if GUIX is available
if ! command -v guix &> /dev/null; then
    echo "ERROR: GUIX is not installed or not in PATH"
    echo "Please install GUIX first: https://guix.gnu.org/en/download/"
    exit 1
fi

echo "✓ GUIX found at: $(which guix)"
echo "✓ GUIX version: $(guix --version | head -1)"
echo

# Test 1: Check package definition syntax
echo "Test 1: Checking package definition syntax..."
if guix build -f acl2.scm --dry-run &>/dev/null; then
    echo "✓ Package definition syntax is valid"
else
    echo "✗ Package definition has syntax errors"
    guix build -f acl2.scm --dry-run
    exit 1
fi

# Test 2: Check manifest syntax  
echo
echo "Test 2: Checking manifest syntax..."
if guix install -m manifest.scm --dry-run &>/dev/null; then
    echo "✓ Manifest syntax is valid"
else
    echo "✗ Manifest has syntax errors"
    guix install -m manifest.scm --dry-run
    exit 1
fi

# Test 3: Try to build (this may take a while)
echo
echo "Test 3: Attempting to build ACL2 package..."
echo "Note: This may take 30+ minutes and requires significant disk space"
read -p "Do you want to proceed with the build? (y/N): " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo "Building ACL2 package..."
    guix build -f acl2.scm
    echo "✓ Build completed successfully"
else
    echo "Skipping build test"
fi

echo
echo "✓ All tests completed successfully"
echo
echo "To install ACL2, run one of:"
echo "  guix install -f acl2.scm"
echo "  guix install -m manifest.scm"
echo "  guix shell -f acl2.scm      # for temporary environment"