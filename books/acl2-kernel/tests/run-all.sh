#!/bin/bash
# Run all ACL2 Kernel tests
#
# Usage: ./run-all.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=== ACL2 Jupyter Kernel Tests ==="
echo

FAILURES=0

for test in "$SCRIPT_DIR"/test-*.sh; do
    if [ "$test" = "$0" ]; then
        continue
    fi
    echo "--- Running $(basename "$test") ---"
    if bash "$test"; then
        echo "PASSED"
    else
        echo "FAILED"
        FAILURES=$((FAILURES + 1))
    fi
    echo
done

echo "=== Summary ==="
if [ $FAILURES -eq 0 ]; then
    echo "All tests passed"
    exit 0
else
    echo "$FAILURES test file(s) failed"
    exit 1
fi
