# ACL2 Jupyter Kernel Project

## Active Plan
Read `/workspaces/acl2-jupyter/PLAN-acl2-kernel.md` for the current implementation plan.

## Key Context
- This project implements a native ACL2 Jupyter kernel in Lisp
- Reference implementation: `/home/acl2/books/centaur/bridge/bridge-sbcl-raw.lsp`
- Jupyter spec: `/workspaces/acl2-jupyter/acl2-kernel-spec.md`

## Development Practices
- **TDD**: Write tests as ACL2 books with `assert-event` forms
- **Parinfer**: Use `source ~/.cargo/env ; parinfer-rust -l lisp` to fix parentheses
- **ACL2 vs Raw Lisp**: Use `.lisp` for ACL2 logic, `.lsp` for raw SBCL code loaded via `include-raw`

## Running ACL2
```bash
echo "(ld \"file.lisp\")" | /home/acl2/saved_acl2
```

## Workspace Structure
- `/workspaces/acl2-jupyter/` - Main project workspace
- `/home/acl2/` - ACL2 installation with books
- `/home/acl2/books/centaur/bridge/` - ACL2 Bridge reference code
