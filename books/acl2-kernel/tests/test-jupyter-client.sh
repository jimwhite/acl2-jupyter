#!/bin/bash
# Test ACL2 kernel via jupyter_client
# This validates the kernel can communicate via Jupyter protocol

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Testing kernel via jupyter_client..."

python3 << 'EOF'
import json
import time
from jupyter_client import KernelManager

def test_kernel():
    km = KernelManager(kernel_name='acl2')
    km.start_kernel()
    
    # Give kernel time to fully initialize (load books, start ZMQ)
    time.sleep(5)
    
    try:
        kc = km.client()
        kc.start_channels()
        
        # Test kernel_info_request directly instead of wait_for_ready
        print("Sending kernel_info_request...")
        msg_id = kc.kernel_info()
        reply = kc.get_shell_msg(timeout=30)
        assert reply['msg_type'] == 'kernel_info_reply', f"Expected kernel_info_reply, got {reply['msg_type']}"
        assert reply['content']['status'] == 'ok', f"Expected status ok, got {reply['content']['status']}"
        print("kernel_info_request: PASS")
        print(f"  protocol_version: {reply['content']['protocol_version']}")
        print(f"  implementation: {reply['content']['implementation']}")
        
        # Test execute_request
        print("\nSending execute_request...")
        msg_id = kc.execute("(+ 1 2)")
        reply = kc.get_shell_msg(timeout=30)
        assert reply['msg_type'] == 'execute_reply', f"Expected execute_reply, got {reply['msg_type']}"
        assert reply['content']['status'] == 'ok', f"Expected status ok, got {reply['content']['status']}"
        print("execute_request: PASS")
        print(f"  execution_count: {reply['content']['execution_count']}")
        
        # Collect IOPub messages (status, execute_result)
        print("\nIOPub messages:")
        try:
            while True:
                msg = kc.get_iopub_msg(timeout=1)
                print(f"  {msg['msg_type']}")
        except:
            pass
        
        # Test shutdown
        print("\nSending shutdown_request...")
        kc.shutdown()
        print("shutdown_request: PASS")
        
        kc.stop_channels()
        
    finally:
        km.shutdown_kernel(now=True)
    
    print("\nAll jupyter_client tests passed")

test_kernel()
EOF

echo "PASSED"
