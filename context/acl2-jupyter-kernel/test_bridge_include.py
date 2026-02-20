#!/usr/bin/env python3
"""Test include-book through the ACL2 Bridge to verify it works."""

import sys
sys.path.insert(0, "/home/acl2/books/centaur/bridge/python")

from acl2_bridge import Client, Command

client = Client()
client.connect("./demo-bridge")

# Read hello
msg = client.receive()
assert msg.type == "ACL2_BRIDGE_HELLO", f"Expected HELLO, got {msg}"
print(f"Connected to bridge worker: {msg.payload}")

# Wait for READY
msg = client.receive()
assert msg.type == "READY", f"Expected READY, got {msg}"

# Send include-book
cmd = '(include-book "std/lists/append" :dir :system)'
print(f"Sending: {cmd}")
client.send(Command("LISP", cmd))

# Collect responses
while True:
    msg = client.receive()
    if msg.type == "RETURN":
        print(f"RETURN: {msg.payload}")
        break
    elif msg.type == "STDOUT":
        print(msg.payload, end="")
    elif msg.type == "ERROR":
        print(f"ERROR: {msg.payload}")
        break
    elif msg.type == "READY":
        print("Got unexpected READY")
        break

# Wait for next READY
msg = client.receive()
assert msg.type == "READY", f"Expected READY, got {msg}"

# Verify kernel still works after include-book
client.send(Command("LISP", "(+ 100 200)"))
while True:
    msg = client.receive()
    if msg.type == "RETURN":
        print(f"After include-book, (+ 100 200) = {msg.payload}")
        break
    elif msg.type == "STDOUT":
        print(msg.payload, end="")
    elif msg.type == "ERROR":
        print(f"ERROR: {msg.payload}")
        break

# Stop bridge
msg = client.receive()
assert msg.type == "READY"
client.send(Command("LISP", "(bridge::stop)"))
client.disconnect()
print("Bridge test complete - include-book works!")
