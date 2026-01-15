# Plan: ACL2 Jupyter Kernel in Native Lisp

Implement a native ACL2 Jupyter kernel as ACL2 books, using raw Lisp only where necessary (ZeroMQ FFI, threading primitives). Tests are `defthm` forms verified by ACL2's theorem prover during `cert.pl` certification.

## Architecture

The kernel reuses existing ACL2 community books wherever possible:

### Existing Books to Include
- **JSON parsing**: `kestrel/json-parser/parse-json.lisp` - full JSON parser
- **JSON encoding**: `centaur/bridge/to-json.lisp` - JSON encoder for ACL2 objects  
- **HMAC-SHA-256**: `kestrel/crypto/interfaces/hmac-sha-256.lisp` - message signing
- **SHA-256**: `kestrel/crypto/interfaces/sha-256.lisp` - hashing
- **Strings**: `std/strings/top.lisp` - string utilities
- **Bridge patterns**: `centaur/bridge/top.lisp` - TCP/Unix socket I/O, threading

### New Kernel-Specific Books
```
books/acl2-kernel/
├── package.lsp              # DEFPACKAGE for ACL2-KERNEL
├── portcullis.lisp          # Package loading book
├── cert.acl2                # Certification config
├── connection.lisp          # Parse Jupyter connection files (uses kestrel/json-parser)
├── message.lisp             # Jupyter protocol message envelopes (uses bridge/to-json, crypto/hmac)
├── uuid-raw.lsp             # Raw: UUID v4 generation (no ACL2 book exists)
├── uuid.lisp                # ACL2 wrapper for UUID
├── channel.lisp             # ZeroMQ channel abstraction
├── zmq-raw.lsp              # Raw: pzmq FFI (ZeroMQ bindings)
├── handlers.lisp            # Request handlers (kernel_info, execute, etc.)
├── eval.lisp                # ACL2 code evaluation wrapper
├── eval-raw.lsp             # Raw: Output capture, ACL2 channel binding
├── kernel.lisp              # Main kernel state and dispatch
├── kernel-raw.lsp           # Raw: Threading, main event loop
├── top.lisp                 # Top-level book
└── Makefile                 # Runs cert.pl
```

## Steps

1. **[DONE] Create kernel directory and package** - Set up `books/acl2-kernel/` with package definition and top-level book structure. Include existing books for JSON, crypto.

2. **[DONE] Implement connection file parser** - Use `kestrel/json-parser` to parse Jupyter connection files. Write `defthm` tests verifying parsed structure. File: `connection.lisp`

3. **Implement message envelope** - Use `centaur/bridge/to-json` for encoding, `kestrel/crypto/interfaces/hmac-sha-256` for signing. `defthm` tests verify envelope structure.

4. **Implement UUID generation** - Raw Lisp for UUID v4 (no existing ACL2 book), ACL2 wrapper with type theorems.

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

- [x] Step 1: Create kernel directory and package (basic structure done)
- [ ] Step 2: Implement connection file parser using kestrel/json-parser
- [ ] Step 3: Implement message envelope using bridge/to-json and crypto/hmac
- [ ] Step 4: Implement UUID generation
- [ ] Step 5: Implement ZeroMQ interface
- [ ] Step 6: Implement output capture
- [ ] Step 7: Implement kernel orchestration
- [ ] Step 8: Create kernel.json and installation
