#!/bin/bash
# Run all ACL2 Kernel tests
#
# Usage: ./run-all.sh [--with-python-tests]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=== ACL2 Jupyter Kernel Tests ==="
echo

FAILURES=0

# Run shell tests
for test in "$SCRIPT_DIR"/test-*.sh; do
    if [ "$(basename "$test")" = "run-all.sh" ]; then
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

# Run Python tests if requested or if jupyter_client is available
if [ "$1" = "--with-python-tests" ] || python3 -c "import jupyter_client" 2>/dev/null; then
    for test in "$SCRIPT_DIR"/test-*.py; do
        if [ -f "$test" ]; then
            echo "--- Running $(basename "$test") ---"
            if timeout 120 python3 "$test"; then
                echo "PASSED"
            else
                echo "FAILED"
                FAILURES=$((FAILURES + 1))
            fi
            echo
        fi
    done
fi

echo "=== Summary ==="
if [ $FAILURES -eq 0 ]; then
    echo "All tests passed"
    exit 0
else
    echo "$FAILURES test file(s) failed"
    exit 1
fi
