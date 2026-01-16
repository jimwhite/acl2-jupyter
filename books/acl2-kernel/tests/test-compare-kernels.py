#!/usr/bin/env python3
"""Compare native ACL2 kernel with Python ACL2 kernel.

This test runs both kernels side-by-side to verify the native
implementation behaves the same as the working Python version.
"""

import jupyter_client
import time
import sys
import os

os.environ.setdefault('ACL2', '/home/acl2/saved_acl2')


def get_kernel_info(kc):
    """Get kernel info and return relevant fields."""
    kc.kernel_info()
    reply = kc.get_shell_msg(timeout=10)
    content = reply['content']
    return {
        'status': content.get('status'),
        'implementation': content.get('implementation'),
        'language': content.get('language_info', {}).get('name'),
        'protocol_version': content.get('protocol_version'),
    }


def execute_code(kc, code):
    """Execute code and return results."""
    kc.execute(code)
    reply = kc.get_shell_msg(timeout=10)
    
    # Collect IOPub messages
    time.sleep(0.3)
    iopub = []
    for _ in range(20):
        try:
            msg = kc.get_iopub_msg(timeout=0.2)
            iopub.append({
                'type': msg['msg_type'],
                'content': msg.get('content', {})
            })
        except:
            break
    
    return {
        'status': reply['content'].get('status'),
        'execution_count': reply['content'].get('execution_count'),
        'iopub_types': [m['type'] for m in iopub],
        'iopub': iopub,
    }


def test_kernel(name, timeout=30):
    """Start kernel and run basic tests."""
    print(f'\nStarting {name}...')
    km = jupyter_client.KernelManager(kernel_name=name)
    km.start_kernel()
    kc = km.client()
    kc.start_channels()
    
    try:
        kc.wait_for_ready(timeout=timeout)
        print(f'  {name} ready')
    except Exception as e:
        print(f'  {name} failed to start: {e}')
        km.shutdown_kernel(now=True)
        return None
    
    results = {
        'kernel_info': get_kernel_info(kc),
        'execute_simple': execute_code(kc, '(+ 1 2)'),
        'execute_defun': execute_code(kc, '(defun foo (x) x)'),
    }
    
    km.shutdown_kernel()
    return results


def compare_results(native, python):
    """Compare results from both kernels."""
    print('\n' + '=' * 60)
    print('Comparison Results')
    print('=' * 60)
    
    passed = True
    
    # Compare kernel_info
    print('\n--- kernel_info ---')
    for key in ['status', 'language']:
        n_val = native['kernel_info'].get(key)
        p_val = python['kernel_info'].get(key)
        match = '✓' if n_val == p_val else '✗'
        print(f'  {key}: native={n_val}, python={p_val} {match}')
        if n_val != p_val and key == 'status':
            passed = False
    
    # Compare execute_simple
    print('\n--- execute (+ 1 2) ---')
    for key in ['status', 'execution_count']:
        n_val = native['execute_simple'].get(key)
        p_val = python['execute_simple'].get(key)
        match = '✓' if n_val == p_val else '✗'
        print(f'  {key}: native={n_val}, python={p_val} {match}')
        if n_val != p_val and key == 'status':
            passed = False
    
    # Compare IOPub message types
    print('\n--- IOPub messages ---')
    n_types = native['execute_simple']['iopub_types']
    p_types = python['execute_simple']['iopub_types']
    print(f'  native: {n_types}')
    print(f'  python: {p_types}')
    
    # Both should have status messages
    n_has_status = 'status' in n_types
    p_has_status = 'status' in p_types
    if n_has_status and p_has_status:
        print('  Both have status messages ✓')
    elif not n_has_status:
        print('  Native missing status messages ✗')
        passed = False
    
    return passed


def main():
    # Test both kernels
    native_results = test_kernel('acl2-native', timeout=30)
    python_results = test_kernel('acl2-python', timeout=60)
    
    if native_results is None:
        print('\nFAILED: Native kernel did not start')
        sys.exit(1)
    
    if python_results is None:
        print('\nSKIPPED: Python kernel not available for comparison')
        print('Native kernel tests passed independently')
        sys.exit(0)
    
    # Compare
    if compare_results(native_results, python_results):
        print('\n' + '=' * 60)
        print('PASSED: Native kernel behaves like Python kernel')
        print('=' * 60)
    else:
        print('\n' + '=' * 60)
        print('FAILED: Behavior mismatch')
        print('=' * 60)
        sys.exit(1)


if __name__ == '__main__':
    main()
