#!/usr/bin/env python3
"""Test include-book via the ACL2 Bridge to verify it works.

This test starts a bridge server, connects, sends an include-book command,
and checks the result. Use this to compare bridge behavior vs kernel behavior.

Usage:
    # First start the bridge in a separate terminal:
    #   cd /home/acl2
    #   echo '(include-book "centaur/bridge/top" :dir :system)
    #   (bridge::start "/tmp/test-bridge.sock")' | saved_acl2
    #
    # Then run this test:
    #   python3 test_bridge_include_book.py
"""

import socket
import sys
import time


def send_command(sock, cmd_type, sexpr):
    """Send a bridge command."""
    content = sexpr
    header = f"{cmd_type} {len(content)}\n"
    sock.sendall((header + content + "\n").encode())


def read_message(sock):
    """Read a bridge message. Returns (type, content)."""
    buf = b""
    # Read header line
    while b"\n" not in buf:
        data = sock.recv(4096)
        if not data:
            return None, None
        buf += data
    
    header_end = buf.index(b"\n")
    header = buf[:header_end].decode()
    rest = buf[header_end + 1:]
    
    parts = header.split(" ", 1)
    if len(parts) != 2:
        return header, ""
    
    msg_type = parts[0]
    content_len = int(parts[1])
    
    # Read content
    while len(rest) < content_len + 1:  # +1 for trailing newline
        data = sock.recv(4096)
        if not data:
            break
        rest += data
    
    content = rest[:content_len].decode()
    return msg_type, content


def main():
    sock_path = "/tmp/test-bridge.sock"
    
    print(f"Connecting to bridge at {sock_path}...")
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    try:
        s.connect(sock_path)
    except FileNotFoundError:
        print(f"ERROR: Socket {sock_path} not found.")
        print("Start the bridge first:")
        print('  echo \'(include-book "centaur/bridge/top" :dir :system)')
        print('  (bridge::start "/tmp/test-bridge.sock")\' | saved_acl2')
        sys.exit(1)
    
    s.settimeout(120)
    
    # Read HELLO
    msg_type, content = read_message(s)
    print(f"Got: {msg_type} {content}")
    
    # Read READY
    msg_type, content = read_message(s)
    print(f"Got: {msg_type} {content}")
    
    # Send include-book command
    cmd = '(include-book "std/lists/append" :dir :system)'
    print(f"\nSending: {cmd}")
    send_command(s, "LISP", cmd)
    
    # Read responses until RETURN or ERROR
    while True:
        msg_type, content = read_message(s)
        if msg_type is None:
            print("Connection closed!")
            break
        print(f"  {msg_type}: {content[:200]}")
        if msg_type in ("RETURN", "ERROR", "READY"):
            break
    
    # Try a simple eval after to confirm bridge still works
    msg_type, content = read_message(s)
    print(f"Got: {msg_type} {content}")
    
    cmd2 = "(+ 1 2)"
    print(f"\nSending: {cmd2}")
    send_command(s, "LISP", cmd2)
    
    while True:
        msg_type, content = read_message(s)
        if msg_type is None:
            print("Connection closed!")
            break
        print(f"  {msg_type}: {content[:200]}")
        if msg_type in ("RETURN", "ERROR", "READY"):
            break
    
    s.close()
    print("\nDone!")


if __name__ == "__main__":
    main()
