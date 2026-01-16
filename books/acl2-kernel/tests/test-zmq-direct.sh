#!/bin/bash
# Test ACL2 kernel via direct ZMQ communication
# This bypasses jupyter_client to test raw Jupyter protocol

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Testing kernel via direct ZMQ..."

python3 "$SCRIPT_DIR/test-zmq-direct.py" 2>&1 | tail -20

# Check exit status 
if grep -q "SUCCESS" <<< "$(python3 "$SCRIPT_DIR/test-zmq-direct.py" 2>&1)"; then
    echo "PASSED"
    exit 0
else
    echo "FAILED"
    exit 1
fi
