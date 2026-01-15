# ACL2 Jupyter Kernel Project

## Active Plan
Read `/workspaces/acl2-jupyter/PLAN-acl2-kernel.md` for the current implementation plan.

## Key Context
- This project implements a native ACL2 Jupyter kernel in Lisp
- Reference implementation: `/home/acl2/books/centaur/bridge/bridge-sbcl-raw.lsp`
- Jupyter spec: `/workspaces/acl2-jupyter/acl2-kernel-spec.md`

## STRICT Development Practices - TDD (Theorem Driven Development)

### MANDATORY Requirements
- **ALL guards MUST be verified** - never use `:verify-guards nil` or skip guard proofs
- **ALL tests MUST pass** - never disable, stub, or mock tests
- **Production code ONLY** - never generate placeholder or shortcut code
- **Proofs MUST complete** - if a proof fails, fix the code or add proper lemmas
- **cert.pl MUST succeed** - code is not complete until certification passes

### MANDATORY: Reuse Existing Code
- **ALWAYS search for existing implementations** before writing new code
- **ACL2 community books are the first source** - search `/home/acl2/books/`
- **Key existing books to use:**
  - JSON parsing: `kestrel/json-parser/parse-json.lisp`
  - JSON encoding: `centaur/bridge/to-json.lisp`
  - HMAC-SHA-256: `kestrel/crypto/interfaces/hmac-sha-256.lisp`
  - SHA-256: `kestrel/crypto/interfaces/sha-256.lisp`
  - Strings: `std/strings/top.lisp`
  - Utilities: `std/util/defines.lisp`, `std/basic/top.lisp`
- **Never duplicate functionality** that exists in community books

### When Proofs Fail
1. Analyze the checkpoint goals carefully
2. Add necessary lemmas or include appropriate arithmetic/bitops books
3. Strengthen guards or hypotheses as needed
4. Refactor code to be more proof-friendly
5. NEVER work around by disabling guards or tests

### Code Quality Standards
- Use `define` with proper `:guard` and `:returns` specifications
- Include type theorems (`character-listp`, `stringp`, etc.)
- Write `defthm` tests that ACL2 proves during certification
- Follow patterns from certified books like `centaur/bridge/to-json.lisp`

## Tools
- **Parinfer**: `source ~/.cargo/env ; parinfer-rust -l lisp` to fix parentheses
- **cert.pl**: `/home/acl2/books/build/cert.pl --acl2 /home/acl2/saved_acl2 <book>.lisp`
- **ACL2 MCP**: Use for searching ACL2 details and testing code snippets

## Running ACL2
```bash
echo "(ld \"file.lisp\")" | /home/acl2/saved_acl2
```

## Workspace Structure
- `/workspaces/acl2-jupyter/` - Main project workspace
- `/home/acl2/` - ACL2 installation with books
- `/home/acl2/books/centaur/bridge/` - ACL2 Bridge reference code (follow its patterns)
