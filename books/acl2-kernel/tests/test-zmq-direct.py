#!/usr/bin/env python3
"""Direct ZMQ test for the ACL2 kernel - bypasses jupyter_client."""

import json
import os
import sys
import time
import tempfile
import subprocess
import zmq
import uuid
from datetime import datetime

def create_connection_file():
    """Create a connection file with test ports."""
    connection = {
        "ip": "127.0.0.1",
        "transport": "tcp",
        "signature_scheme": "hmac-sha256",
        "key": "test-key-12345",
        "shell_port": 15551,
        "control_port": 15552,
        "iopub_port": 15553,
        "stdin_port": 15554,
        "hb_port": 15555,
    }
    
    fd, path = tempfile.mkstemp(suffix='.json', prefix='kernel-')
    with os.fdopen(fd, 'w') as f:
        json.dump(connection, f)
    
    return path, connection

def make_message(session, msg_type, content=None):
    """Create a Jupyter protocol message."""
    header = {
        "msg_id": str(uuid.uuid4()),
        "msg_type": msg_type,
        "username": "test",
        "session": session,
        "date": datetime.utcnow().isoformat() + "Z",
        "version": "5.3",
    }
    return {
        "header": header,
        "parent_header": {},
        "metadata": {},
        "content": content or {},
    }

def sign_message(key, header, parent, metadata, content):
    """Compute HMAC signature."""
    import hmac
    import hashlib
    
    h = hmac.new(key.encode(), digestmod=hashlib.sha256)
    h.update(header.encode())
    h.update(parent.encode())
    h.update(metadata.encode())
    h.update(content.encode())
    return h.hexdigest()

def main():
    print("Direct ZMQ test for ACL2 kernel")
    print("=" * 50)
    
    # Create connection file
    conn_file, conn_info = create_connection_file()
    print(f"Connection file: {conn_file}")
    print(f"Ports: shell={conn_info['shell_port']}, iopub={conn_info['iopub_port']}")
    
    # Start kernel
    kernel_cmd = [
        "/workspaces/acl2-jupyter/books/acl2-kernel/install/acl2-kernel",
        conn_file
    ]
    print(f"Starting kernel: {' '.join(kernel_cmd)}")
    
    kernel_proc = subprocess.Popen(
        kernel_cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True
    )
    
    # Wait for kernel to start
    time.sleep(3)
    
    # Connect to sockets
    ctx = zmq.Context()
    
    # Shell socket - DEALER to talk to kernel's ROUTER
    shell = ctx.socket(zmq.DEALER)
    shell.identity = b"test-client"
    shell.connect(f"tcp://127.0.0.1:{conn_info['shell_port']}")
    print(f"Connected to shell socket")
    
    # IOPub socket - SUB to receive broadcasts
    iopub = ctx.socket(zmq.SUB)
    iopub.subscribe(b"")  # Subscribe to all topics
    iopub.connect(f"tcp://127.0.0.1:{conn_info['iopub_port']}")
    print(f"Connected to iopub socket")
    
    # Create kernel_info_request message
    session = str(uuid.uuid4())
    msg = make_message(session, "kernel_info_request")
    
    header_json = json.dumps(msg["header"])
    parent_json = json.dumps(msg["parent_header"])
    metadata_json = json.dumps(msg["metadata"])
    content_json = json.dumps(msg["content"])
    
    signature = sign_message(
        conn_info["key"],
        header_json, parent_json, metadata_json, content_json
    )
    
    # Build wire message
    wire_parts = [
        b"test-client",  # identity
        b"<IDS|MSG>",
        signature.encode(),
        header_json.encode(),
        parent_json.encode(),
        metadata_json.encode(),
        content_json.encode(),
    ]
    
    print(f"\nSending kernel_info_request...")
    print(f"  identity: test-client")
    print(f"  signature: {signature[:40]}...")
    
    shell.send_multipart(wire_parts)
    
    # Wait for reply
    print("\nWaiting for reply...")
    
    poller = zmq.Poller()
    poller.register(shell, zmq.POLLIN)
    poller.register(iopub, zmq.POLLIN)
    
    start = time.time()
    timeout = 10  # seconds
    
    while time.time() - start < timeout:
        events = dict(poller.poll(1000))
        
        if shell in events:
            parts = shell.recv_multipart()
            print(f"\n=== SHELL REPLY ({len(parts)} parts) ===")
            for i, part in enumerate(parts):
                try:
                    decoded = part.decode('utf-8')
                    if decoded.startswith('{'):
                        print(f"  [{i}] JSON: {decoded[:100]}...")
                    else:
                        print(f"  [{i}] {decoded}")
                except:
                    print(f"  [{i}] (binary: {len(part)} bytes)")
            
            # Try to parse the reply
            try:
                # Find delimiter
                delim_idx = parts.index(b"<IDS|MSG>")
                header = json.loads(parts[delim_idx + 2])
                content = json.loads(parts[delim_idx + 5])
                print(f"\n  Reply type: {header.get('msg_type')}")
                print(f"  Content: {json.dumps(content, indent=2)[:500]}")
                print("\n*** SUCCESS! Got kernel_info_reply ***")
                break
            except Exception as e:
                print(f"  Parse error: {e}")
        
        if iopub in events:
            parts = iopub.recv_multipart()
            print(f"\n=== IOPUB MESSAGE ({len(parts)} parts) ===")
            for i, part in enumerate(parts):
                try:
                    decoded = part.decode('utf-8')
                    print(f"  [{i}] {decoded[:80]}")
                except:
                    print(f"  [{i}] (binary)")
    else:
        print("\n*** TIMEOUT waiting for reply ***")
        
        # Check kernel output
        print("\nKernel stdout (last 20 lines):")
        kernel_proc.poll()
        if kernel_proc.returncode is not None:
            print(f"Kernel exited with code: {kernel_proc.returncode}")
    
    # Cleanup
    print("\nCleaning up...")
    shell.close()
    iopub.close()
    ctx.term()
    kernel_proc.terminate()
    os.unlink(conn_file)
    
    print("Done.")

if __name__ == "__main__":
    main()
