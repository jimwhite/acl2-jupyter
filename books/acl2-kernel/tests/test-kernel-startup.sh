#!/bin/bash
# Test ACL2 Jupyter Kernel startup
# This test verifies the kernel can start and bind to sockets

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KERNEL_DIR="$(dirname "$SCRIPT_DIR")"

# Create test connection file
TEST_CONN="/tmp/acl2-kernel-test-$$.json"
cat > "$TEST_CONN" << 'EOF'
{
  "transport": "tcp",
  "ip": "127.0.0.1",
  "control_port": 50001,
  "shell_port": 50002,
  "stdin_port": 50003,
  "hb_port": 50004,
  "iopub_port": 50005,
  "signature_scheme": "hmac-sha256",
  "key": "test-key-12345"
}
EOF

cleanup() {
    rm -f "$TEST_CONN"
}
trap cleanup EXIT

echo "Testing kernel startup..."

# Run kernel with timeout - it should start and print startup message
cd "$KERNEL_DIR"
OUTPUT=$(timeout 5 /home/acl2/saved_acl2 << EOF 2>&1
(include-book "top")
:q
(acl2-kernel::start-kernel "$TEST_CONN")
EOF
) || true

echo "$OUTPUT"

# Check for successful startup message
if echo "$OUTPUT" | grep -q "ACL2 Jupyter Kernel started"; then
    echo "PASS: Kernel started successfully"
    exit 0
else
    echo "FAIL: Kernel did not start"
    exit 1
fi
