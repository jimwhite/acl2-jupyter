#!/bin/bash
# Test ACL2 kernel via jupyter_client
# This validates the kernel can communicate via Jupyter protocol

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Testing kernel via jupyter_client..."

python3 << 'EOF'
import asyncio
from jupyter_client import KernelManager

async def test_kernel():
    km = KernelManager(kernel_name='acl2')
    km.start_kernel()
    
    try:
        kc = km.client()
        kc.start_channels()
        
        # Wait for kernel to be ready
        kc.wait_for_ready(timeout=30)
        print("Kernel is ready")
        
        # Test kernel_info_request
        msg_id = kc.kernel_info()
        reply = kc.get_shell_msg(timeout=10)
        assert reply['msg_type'] == 'kernel_info_reply', f"Expected kernel_info_reply, got {reply['msg_type']}"
        assert reply['content']['status'] == 'ok', f"Expected status ok, got {reply['content']['status']}"
        print("kernel_info_request: PASS")
        
        # Test execute_request
        msg_id = kc.execute("(+ 1 2)")
        reply = kc.get_shell_msg(timeout=10)
        assert reply['msg_type'] == 'execute_reply', f"Expected execute_reply, got {reply['msg_type']}"
        assert reply['content']['status'] == 'ok', f"Expected status ok, got {reply['content']['status']}"
        print("execute_request: PASS")
        
        # Test shutdown
        kc.shutdown()
        print("shutdown_request: PASS")
        
        kc.stop_channels()
        
    finally:
        km.shutdown_kernel(now=True)
    
    print("All jupyter_client tests passed")

asyncio.run(test_kernel())
EOF

echo "PASSED"
