#!/usr/bin/env python3
"""Test the native ACL2 kernel via jupyter_client.

This tests the kernel through the standard Jupyter protocol,
verifying wait_for_ready, kernel_info, and execute_request.
"""

import jupyter_client
import time
import sys
import os

# Ensure ACL2 is available for the Python kernel comparison
os.environ.setdefault('ACL2', '/home/acl2/saved_acl2')

def test_kernel(kernel_name, timeout=30):
    """Test a kernel through jupyter_client."""
    print(f'\n=== Testing {kernel_name} ===')
    
    try:
        km = jupyter_client.KernelManager(kernel_name=kernel_name)
        km.start_kernel()
        kc = km.client()
        kc.start_channels()
        
        # Test 1: wait_for_ready
        print('Test 1: wait_for_ready...')
        try:
            kc.wait_for_ready(timeout=timeout)
            print('  PASS: Kernel ready')
        except Exception as e:
            print(f'  FAIL: {e}')
            km.shutdown_kernel(now=True)
            return False
        
        # Test 2: kernel_info_request
        print('Test 2: kernel_info_request...')
        kc.kernel_info()
        reply = kc.get_shell_msg(timeout=10)
        if reply['content'].get('status') == 'ok':
            impl = reply['content'].get('implementation', 'unknown')
            print(f'  PASS: status=ok, implementation={impl}')
        else:
            print(f'  FAIL: status={reply["content"].get("status")}')
            km.shutdown_kernel(now=True)
            return False
        
        # Test 3: execute_request
        print('Test 3: execute_request (+ 1 2)...')
        kc.execute('(+ 1 2)')
        reply = kc.get_shell_msg(timeout=10)
        if reply['content'].get('status') == 'ok':
            count = reply['content'].get('execution_count', 0)
            print(f'  PASS: status=ok, execution_count={count}')
        else:
            print(f'  FAIL: status={reply["content"].get("status")}')
            km.shutdown_kernel(now=True)
            return False
        
        # Test 4: IOPub messages
        print('Test 4: IOPub messages...')
        time.sleep(0.5)
        iopub_types = []
        for _ in range(20):
            try:
                msg = kc.get_iopub_msg(timeout=0.3)
                iopub_types.append(msg['msg_type'])
            except:
                break
        
        # Should have at least status messages
        if 'status' in iopub_types:
            print(f'  PASS: received {len(iopub_types)} messages: {iopub_types}')
        else:
            print(f'  WARN: no status messages in {iopub_types}')
        
        # Test 5: shutdown
        print('Test 5: shutdown_request...')
        km.shutdown_kernel()
        print('  PASS: kernel shutdown')
        
        print(f'\n{kernel_name}: ALL TESTS PASSED')
        return True
        
    except Exception as e:
        print(f'\n{kernel_name}: FAILED with exception: {e}')
        try:
            km.shutdown_kernel(now=True)
        except:
            pass
        return False


def main():
    """Run tests on available kernels."""
    results = {}
    
    # Test native ACL2 kernel
    results['acl2-native'] = test_kernel('acl2-native', timeout=30)
    
    # Optionally test Python ACL2 kernel for comparison
    if '--with-python-kernel' in sys.argv:
        results['acl2-python'] = test_kernel('acl2-python', timeout=60)
    
    # Summary
    print('\n' + '=' * 50)
    print('Summary:')
    for name, passed in results.items():
        status = 'PASSED' if passed else 'FAILED'
        print(f'  {name}: {status}')
    
    # Exit with failure if any test failed
    if not all(results.values()):
        sys.exit(1)


if __name__ == '__main__':
    main()
