# Plan: ACL2 Jupyter Kernel in Native Lisp

Implement a native ACL2 Jupyter kernel as ACL2 books, using raw Lisp only where necessary (ZeroMQ FFI, threading primitives). Tests are `defthm` forms verified by ACL2's theorem prover during `cert.pl` certification.

## Architecture

```
books/acl2-kernel/
├── package.lsp              # Raw: DEFPACKAGE for ACL2-KERNEL
├── package.lisp             # ACL2 book loading package.lsp
├── json.lisp                # ACL2: JSON encoding/decoding (pure functions)
├── json-tests.lisp          # ACL2: defthm tests for JSON
├── hmac.lisp                # ACL2: HMAC-SHA256 wrapper
├── hmac-raw.lsp             # Raw: ironclad FFI for HMAC
├── message.lisp             # ACL2: Message envelope construction
├── message-tests.lisp       # ACL2: defthm tests for messages
├── uuid.lisp                # ACL2: UUID generation wrapper
├── uuid-raw.lsp             # Raw: UUID v4 generation
├── zmq-raw.lsp              # Raw: ZeroMQ socket operations (pzmq)
├── zmq.lisp                 # ACL2: ZeroMQ wrapper book
├── channel.lisp             # ACL2: Channel abstraction
├── heartbeat.lisp           # ACL2: Heartbeat responder
├── iopub.lisp               # ACL2: IOPub output channel
├── shell.lisp               # ACL2: Shell request handlers
├── eval.lisp                # ACL2: ACL2 code evaluation
├── eval-raw.lsp             # Raw: Output capture, ACL2 channel binding
├── kernel.lisp              # ACL2: Main kernel orchestration
├── kernel-raw.lsp           # Raw: Threading, main loop
├── top.lisp                 # ACL2: Top-level book (includes all)
├── cert.acl2                # Certification instructions
└── Makefile                 # Runs cert.pl for all books
```

## Steps

1. **Create kernel directory and package** - Set up `books/acl2-kernel/` with package definition and top-level book structure. Create `cert.acl2` for certification.

2. **Implement JSON encoding/decoding** - Pure ACL2 functions for JSON serialization with `defthm` tests proving correctness properties (e.g., round-trip, valid output format).

3. **Implement HMAC-SHA256** - ACL2 wrapper book with raw Lisp FFI to ironclad. Tests verify signature computation matches known test vectors.

4. **Implement message envelope** - ACL2 functions for Jupyter protocol message construction. `defthm` tests verify envelope structure and HMAC integration.

5. **Implement ZeroMQ interface** - Raw Lisp for pzmq socket operations, ACL2 wrapper for channel abstraction.

6. **Implement output capture** - Raw Lisp using `bridge-ostream` pattern from bridge-sbcl-raw.lsp for ACL2 channel binding during evaluation.

7. **Implement kernel orchestration** - ACL2 book for kernel state and message dispatch, raw Lisp for threading and main event loop.

8. **Create kernel.json and installation** - Register kernel with Jupyter.

## Testing Strategy

All tests are `defthm` forms that ACL2 proves during certification:

```lisp
;; Example: JSON round-trip test
(defthm json-encode-decode-round-trip
  (implies (json-value-p x)
           (equal (json-decode (json-encode x)) x)))

;; Example: HMAC test vector
(defthm hmac-sha256-test-vector-1
  (equal (hmac-sha256 "key" "message")
         "6e9ef29b75fffc5b7abae527d58fdadb..."))
```

Run tests via cert.pl:
```bash
cd /workspaces/acl2-jupyter/books/acl2-kernel
cert.pl top.lisp  # Certifies all books, running all defthm proofs
```

## Further Considerations

1. **Reuse vs. fork common-lisp-jupyter?** Given ACL2 book requirement, implement fresh with reference to common-lisp-jupyter patterns. **Decision: Fresh implementation as ACL2 books**

2. **ACL2 book certification:** Top-level code is certifiable ACL2; raw Lisp only for FFI (ZeroMQ, crypto, threading). **Decision: ACL2-first approach**

3. **ZeroMQ transport preference:** TCP vs IPC (Unix sockets)? Support both with TCP as default for remote Jupyter compatibility.

## Key Reference Files

- `/home/acl2/books/centaur/bridge/bridge-sbcl-raw.lsp` - SBCL Bridge patterns for I/O, threading, ACL2 channel binding
- `/workspaces/acl2-jupyter/context/quicklisp/local-projects/common-lisp-jupyter/src/` - Existing CL Jupyter kernel infrastructure
- `/workspaces/acl2-jupyter/acl2-kernel-spec.md` - Jupyter protocol specification

## Tools

- `parinfer-rust -l lisp` - Fix Lisp parentheses (run `source ~/.cargo/env` first)
- `cert.pl` - ACL2 book certification (runs all defthm proofs)
- ACL2 MCP service - Search ACL2 details and test code

## Progress

- [ ] Step 1: Create kernel directory and package
- [ ] Step 2: Implement JSON encoding/decoding with defthm tests
- [ ] Step 3: Implement HMAC-SHA256 with test vectors
- [ ] Step 4: Implement message envelope with defthm tests
- [ ] Step 5: Implement ZeroMQ interface
- [ ] Step 6: Implement output capture
- [ ] Step 7: Implement kernel orchestration
- [ ] Step 8: Create kernel.json and installation
