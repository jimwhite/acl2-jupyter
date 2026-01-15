#!/bin/bash
# Test HMAC signing via raw Lisp
# Verifies the OpenSSL-based HMAC implementation

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KERNEL_DIR="$(dirname "$SCRIPT_DIR")"

echo "Testing HMAC signing..."

OUTPUT=$(cd "$KERNEL_DIR" && /home/acl2/saved_acl2 << 'EOF' 2>&1
(include-book "top")
:q
;; Test 1: Empty key returns empty string
(format t "~%TEST1: ~A~%" (equal (acl2-kernel::hmac-sign-raw "" "data") ""))

;; Test 2: Known HMAC value
;; Verified: printf 'test message' | openssl dgst -sha256 -hmac 'secret-key'
(format t "TEST2: ~A~%" (equal (acl2-kernel::hmac-sign-raw "secret-key" "test message")
                               "9a0eb7d4647a82cf2785df52d1e605fb531beb1f270c8215c8ffb3ff31a993b4"))

;; Test 3: Multiple args concatenated
(format t "TEST3: ~A~%" (equal (acl2-kernel::hmac-sign-raw "key" "hello" "world")
                               "90ad356894b519def4f954aab2a2c14d7cc64ab70a0f7ba0b8c31d3f2f1fb251"))
(quit)
EOF
)

echo "$OUTPUT"

# Check all tests passed
FAILURES=0
for i in 1 2 3; do
    if echo "$OUTPUT" | grep -q "TEST$i: T"; then
        echo "PASS: Test $i"
    else
        echo "FAIL: Test $i"
        FAILURES=$((FAILURES + 1))
    fi
done

if [ $FAILURES -eq 0 ]; then
    echo "All HMAC tests passed"
    exit 0
else
    echo "$FAILURES test(s) failed"
    exit 1
fi
