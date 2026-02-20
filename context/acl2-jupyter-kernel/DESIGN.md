# ACL2 Jupyter Kernel (`acl2-jupyter-kernel`) — Design Document

## 1. Goal

Replace the existing Python-based ACL2 Jupyter kernel (`acl2_kernel`, which
uses pexpect to scrape a REPL) with a native Common Lisp kernel that runs
**inside** the ACL2 process itself. This gives us:

- Direct access to the ACL2 world (documentation, formals, guards, theorems)
- Proper output routing (CW, FMT, proofs-co all captured cleanly)
- ACL2-aware code completion and inspection
- No fragile regex-based prompt scraping
- Future path to debugger integration via common-lisp-jupyter's DAP support

## 2. Architecture Overview

```
┌─────────────────────────────────────────────────────────┐
│  Jupyter Frontend (JupyterLab / VS Code / etc.)         │
└──────────────┬──────────────────────────────────────────┘
               │  ZeroMQ (Jupyter Wire Protocol v5.5)
               │  TCP or IPC sockets
┌──────────────┴──────────────────────────────────────────┐
│  saved_acl2_jupyter  (shell script + .core from         │
│                       ACL2's save-exec)                  │
│                                                          │
│  ┌────────────────────────────────────────────────────┐  │
│  │  common-lisp-jupyter  (pzmq, ZeroMQ, wire proto)   │  │
│  │  - kernel base class, channels, heartbeat, etc.    │  │
│  └────────────┬───────────────────────────────────────┘  │
│               │ subclass                                 │
│  ┌────────────┴───────────────────────────────────────┐  │
│  │  acl2-jupyter-kernel                               │  │
│  │  - kernel.lisp    (evaluate-code, output routing)  │  │
│  │  - complete.lisp  (ACL2 symbol completion)         │  │
│  │  - inspect.lisp   (ACL2 documentation lookup)      │  │
│  │  - installer.lisp (kernelspec installation)        │  │
│  └────────────────────────────────────────────────────┘  │
│                                                          │
│  ACL2 world (axioms, books, state, world triples)        │
└──────────────────────────────────────────────────────────┘
```

### Key Insight: No Subprocess, No Bridge

Unlike the old Python kernel (which launched ACL2 as a child process and
scraped output via pexpect) or the ACL2 Bridge approach (which runs a TCP/Unix
socket server with its own message protocol), this kernel runs **inside** the
ACL2 process. The `common-lisp-jupyter` library handles all ZeroMQ
communication, and our code simply overrides `evaluate-code` to evaluate ACL2
forms with proper STATE binding.

## 3. Relationship to Existing Components

### 3.1 common-lisp-jupyter (Tarn Burton)

The `common-lisp-jupyter` library (already installed via Quicklisp in this
container) provides:

- **Jupyter wire protocol** implementation over ZeroMQ (via `pzmq`)
- **Base `kernel` class** with slots for connection-file, channels, session, etc.
- **Generic functions** that we override:
  - `evaluate-code` — evaluate a cell's code
  - `code-is-complete` — check for balanced parens
  - `complete-code` — tab completion
  - `inspect-code` — shift-tab documentation
- **Installer framework** for generating `kernel.json` specs
- **Debugger integration** (DAP protocol) — future potential
- **Channel management** (shell, control, iopub, stdin, heartbeat)
- **Message serialization** (JSON via `shasht`, HMAC signing)

Our kernel is a thin layer on top of this — about 400 lines of Lisp vs
the ~1700 lines of kernel.lisp in common-lisp-jupyter.

### 3.2 ACL2 Bridge (`books/centaur/bridge/`)

The bridge provided critical patterns that we reuse:

- **Output routing macros**: `with-acl2-channels-bound` and `with-acl2-output-to`
  redirect ACL2's `standard-co`, `proofs-co`, `trace-co` (which are *not*
  standard CL streams but ACL2-specific channel symbols) plus the CL special
  variables `*standard-output*`, `*trace-output*`, etc.
- **STATE binding pattern**: `(let ((acl2::state acl2::*the-live-state*)) ...)`
  makes ACL2 macros that implicitly use STATE work correctly.
- **World property access**: `acl2::getpropc`, `acl2::global-val`,
  `acl2::f-get-global` for looking up formals, guards, theorems, documentation.

We do **not** use the bridge's TCP/Unix socket server or its custom message
protocol. Instead, common-lisp-jupyter handles all networking via ZeroMQ.

### 3.3 Existing Python ACL2 Kernel (`acl2_kernel`)

The old kernel (`context/acl2-kernel/`) uses:
- `ipykernel.kernelbase.Kernel` as base class
- `pexpect.replwrap` to launch `saved_acl2` as a subprocess
- Regex to count top-level forms and detect prompts
- Custom prompt (`JPY-ACL2>`) injected via `set-ld-prompt`

Problems with this approach:
- Fragile prompt detection (breaks with multi-line output, errors)
- No access to ACL2 world data (can't do symbol completion)
- Output scraping loses structure (all output is a flat string)
- No way to distinguish stdout from proof output from errors

## 4. File Structure

```
context/acl2-jupyter-kernel/
├── acl2-jupyter-kernel.asd   # ASDF system definition
├── packages.lisp             # Package definition (acl2-jupyter-kernel / jupyter/acl2)
├── kernel.lisp               # Kernel class + evaluate-code + output routing + start
├── complete.lisp             # ACL2 symbol completion
├── inspect.lisp              # ACL2 documentation inspection
├── installer.lisp            # Kernelspec installer (generates kernel.json)
├── build-kernel-image.sh     # Build script: creates saved_acl2_jupyter via save-exec
├── install-kernelspec.sh     # Install script: writes kernel.json
└── test_kernel.py            # 21 pytest tests (arithmetic, defun, defthm, etc.)
```

## 5. Component Details

### 5.1 kernel.lisp — Core Evaluation

**Output routing** (`with-acl2-output-to`):
- Creates a temporary ACL2 output channel symbol
- Sets its `*open-output-channel-key*` property to the Jupyter stdout stream
- Rebinds `*standard-output*`, `*trace-output*`, `*error-output*`, `*debug-io*`
- Uses `with-acl2-channels-bound` (via PROGV) to redirect `standard-co`,
  `proofs-co`, `trace-co` — the ACL2 globals that `CW`, `FMT`, and proof
  output use
- Cleans up on unwind

**Form reading** (`read-acl2-forms`):
- Reads in the ACL2 package
- Handles three kinds of input:
  1. Standard s-expressions: `(defun foo (x) x)`
  2. ACL2 keyword commands: `:pe append` → `(PE 'APPEND)`
  3. Comment lines: skipped
- Returns a list of forms for sequential evaluation

**Evaluation** (`evaluate-code`):
- Iterates through forms from `read-acl2-forms`
- Each form is wrapped in `(let ((acl2::state acl2::*the-live-state*)) ...)`
  and passed to `EVAL` (same pattern as the ACL2 Bridge worker thread)
- Results are displayed via `jupyter:execute-result` using `jupyter:text`
- STATE values are filtered from display (they're not informative)
- Errors are caught and returned as `(values ename evalue traceback)`

**Code completeness** (`code-is-complete`):
- Tries to read the code; if `end-of-file` → "incomplete", if other error →
  "invalid", otherwise → "complete"

**Startup** (`start`):
- Entry point called after ACL2 initialization completes
- Disables the SBCL debugger (so errors don't hang the kernel)
- Reads the connection file path from `(uiop:command-line-arguments)`
- Calls `(jupyter:run-kernel 'kernel conn)` to start the event loop

### 5.2 complete.lisp — Symbol Completion

- Finds the token at cursor position (scanning backwards for symbol chars)
- Searches `ACL2`, `COMMON-LISP`, `ACL2-INPUT-CHANNEL`, `ACL2-OUTPUT-CHANNEL`
  packages for matching external symbols
- Reports type as "function", "macro", "variable", or "symbol"
- Uses `match-set-add` API from common-lisp-jupyter

### 5.3 inspect.lisp — Documentation Lookup

Provides rich markdown documentation for ACL2 symbols:

- **Type tags** from ACL2 world: Function, Macro, Theorem, Constant, Stobj
  (via `acl2::getpropc` on properties like `formals`, `macro-args`, `theorem`,
  `const`, `stobj`)
- **Signature**: from `acl2::formals` or `acl2::macro-args`, falling back to
  `sb-introspect:function-lambda-list`
- **Guard**: from `acl2::guard` property
- **Documentation**: from ACL2's `documentation-alist`, falling back to CL
  `documentation`
- **Current value**: for bound variables/constants (with truncation)

### 5.4 installer.lisp — Kernelspec

Generates a `kernel.json` that tells Jupyter to launch the kernel.
The argv is simply:

```json
{
  "argv": [
    "path/to/saved_acl2_jupyter",
    "{connection_file}"
  ],
  "display_name": "ACL2",
  "language": "acl2",
  "interrupt_mode": "message",
  "metadata": {}
}
```

The saved binary (shell script from `save-exec`) handles all bootstrapping —
SBCL flags, ACL2 restart, and the kernel start eval are all baked in.
No `env` dict is needed because the script already exports `SBCL_HOME`.

## 6. The Saved Image: `saved_acl2_jupyter`

### Build via ACL2's `save-exec`

The kernel binary is built using ACL2's own `save-exec` mechanism — the same
one that creates `saved_acl2` itself. This is done by `build-kernel-image.sh`:

1. Start `saved_acl2` and exit the ACL2 read-eval-print loop (`:q`)
2. Load Quicklisp and the `acl2-jupyter-kernel` ASDF system
3. Call `save-exec` with `:return-from-lp` and `:toplevel-args`

```lisp
(save-exec "saved_acl2_jupyter" nil
           :return-from-lp '(value :q)
           :toplevel-args "--eval '(acl2-jupyter-kernel:start)'")
```

This produces two files:

- **`saved_acl2_jupyter`** — a shell script (like `saved_acl2`)
- **`saved_acl2_jupyter.core`** — the SBCL core image

### Generated Shell Script

The shell script that `save-exec` generates looks like:

```sh
#!/bin/sh
export SBCL_HOME='/usr/local/lib/sbcl/'
exec "/usr/local/bin/sbcl" \
  --tls-limit 16384 \
  --dynamic-space-size 32000 \
  --control-stack-size 64 \
  --disable-ldb \
  --core "saved_acl2_jupyter.core" \
  ${SBCL_USER_ARGS} \
  --end-runtime-options \
  --no-userinit \
  --eval '(acl2::sbcl-restart)' \
  --eval '(acl2-jupyter-kernel:start)' \
  "$@"
```

Key points:

- **`--control-stack-size 64`**: Sets 64 MB control stack for ALL threads in
  the SBCL process. This is critical — the Jupyter Shell thread (created by
  bordeaux-threads via common-lisp-jupyter) inherits this setting. Without it,
  threads get SBCL's default ~2 MB which is insufficient for ACL2's deep
  recursion during `include-book`, proof search, etc.
- **`--eval '(acl2::sbcl-restart)'`**: Initializes ACL2 (runs
  `acl2-default-restart` → LP). Because `:return-from-lp` was set to
  `'(value :q)`, LP exits immediately after initialization.
- **`--eval '(acl2-jupyter-kernel:start)'`**: Runs after ACL2 init completes,
  reads the connection file from the command-line args, and starts the Jupyter
  kernel event loop.
- **`"$@"`**: Passes through the `{connection_file}` argument from kernel.json.

### Startup Flow

```
Jupyter launches: saved_acl2_jupyter /path/to/connection.json

  → Shell script execs: sbcl --control-stack-size 64 ...
      --eval '(acl2::sbcl-restart)'
      --eval '(acl2-jupyter-kernel:start)'
      /path/to/connection.json

  → SBCL starts, loads saved_acl2_jupyter.core
  → (acl2::sbcl-restart)
    → (acl2-default-restart)
      → (LP)
        → *return-from-lp* = '(value :q) → LP exits immediately
    → sbcl-restart returns

  → (acl2-jupyter-kernel:start)
    → (sb-ext:disable-debugger)
    → conn = (first (uiop:command-line-arguments))
           = "/path/to/connection.json"
    → (jupyter:run-kernel 'kernel conn)
      → Parses connection file (JSON: transport, IP, ports, key)
      → Creates ZeroMQ sockets (shell, control, iopub, stdin, heartbeat)
      → Spawns "Jupyter Shell" thread (bordeaux-threads)
      → Spawns heartbeat thread
      → Sends kernel_info_reply, status: idle
      → Ready for execute_request messages
```

### Why `save-exec`, Not `save-lisp-and-die`

Earlier iterations tried using `sb-ext:save-lisp-and-die` to create just a
`.core` file and then launching `sbcl --core ...` directly from kernel.json.
This failed because:

1. **Thread stack size**: SBCL's `--control-stack-size` flag (set in the shell
   script) controls the default stack for ALL threads. Without it, threads
   spawned by bordeaux-threads get ~2 MB, which causes
   `SB-KERNEL::CONTROL-STACK-EXHAUSTED` during ACL2 operations.
   `sb-thread:make-thread` in SBCL 2.6.1 does **not** accept a `:stack-size`
   keyword, so per-thread override is not possible.

2. **Consistency**: Using `save-exec` produces the exact same structure as
   `saved_acl2` — a shell script that sets `SBCL_HOME`, runtime flags, and
   passes `"$@"`. This is the well-tested pattern used by ACL2 itself and
   the ACL2 Bridge.

## 7. Cell Execution Flow

1. User submits cell code (e.g., `(defun app (x y) ...)`)
2. Jupyter frontend sends `execute_request` on shell channel
3. common-lisp-jupyter's `run-shell` receives it
4. Calls our `evaluate-code` method
5. We parse the code into forms via `read-acl2-forms`
6. For each form:
   a. Redirect all output via `with-acl2-output-to` (binds ACL2 channels
      + CL streams to Jupyter's iopub stdout)
   b. Eval with STATE bound: `(let ((state *the-live-state*)) ,form)`
   c. Display results via `jupyter:execute-result`
7. common-lisp-jupyter sends `execute_reply` on shell

## 8. Dependencies

### CL Libraries (via Quicklisp)

| Library | Purpose |
|---------|---------|
| common-lisp-jupyter | Jupyter wire protocol, kernel base class, ZeroMQ |
| pzmq | ZeroMQ bindings (used by common-lisp-jupyter) |
| bordeaux-threads | Threading (shell thread, heartbeat) |
| shasht | JSON parsing/writing |
| ironclad | HMAC message signing |
| alexandria | Utilities |
| babel | String encoding |
| trivial-gray-streams | Gray stream support |

### System Libraries

| Library | Purpose |
|---------|---------|
| libzmq / libczmq | ZeroMQ C library (required by pzmq) |

### ACL2 Internals Used

| Symbol | Purpose |
|--------|---------|
| `acl2::*the-live-state*` | The live ACL2 state object |
| `acl2::*standard-co*` | Standard character output channel |
| `acl2::global-symbol` | Get the special var for a state global |
| `acl2::*open-output-channel-key*` | Property for stream lookup |
| `acl2::*open-output-channel-type-key*` | Property for stream type |
| `acl2::f-get-global` | Read state globals (acl2-version, etc.) |
| `acl2::getpropc` | Read world triple properties |
| `acl2::global-val` | Read global-table values from world |
| `acl2::w` | Get the current ACL2 world from state |
| `acl2::save-exec` | Build saved ACL2 binaries |
| `acl2::*return-from-lp*` | Control LP exit behavior on restart |

## 9. Build & Install

### Prerequisites

- `saved_acl2` (ACL2 built on SBCL) with Quicklisp installed
- `libzmq` and `libczmq` system libraries
- `common-lisp-jupyter` available via Quicklisp

### Build

```sh
cd context/acl2-jupyter-kernel
./build-kernel-image.sh
```

This creates `saved_acl2_jupyter` (shell script) and
`saved_acl2_jupyter.core` in the same directory.

### Install Kernelspec

```sh
./install-kernelspec.sh
```

This writes `kernel.json` to `~/.local/share/jupyter/kernels/acl2/`.

### Test

```sh
python -m pytest test_kernel.py -v --timeout=120
```

21 tests covering arithmetic, lists, defun, defthm, keyword commands,
defconst, CW output routing, code completeness, error handling, and
kernel survivability.

## 10. Comparison with Alternatives

| Approach | Pros | Cons |
|----------|------|------|
| **This kernel** (CL in-process) | Direct world access, proper output, fast, completion/inspection | Must build saved image, ACL2 internals coupling |
| Python pexpect kernel | Simple, no CL deps | Fragile prompt scraping, no completion, flat output |
| ACL2 Bridge + Python | Clean protocol, async | Extra process, extra protocol layer, no ZeroMQ integration |
| Raw CL kernel (`common-lisp-jupyter`) | Already works | No ACL2-specific features, must use `(acl2::...)` prefixes |

## 11. Future Work

- **Proof output formatting**: Route `proofs-co` output to a separate
  stream/display for structured proof display.
- **XDOC rendering**: Render ACL2 XDOC documentation as HTML in inspect
  results.
- **Book loading progress**: Report `include-book` progress via Jupyter
  status messages.
- **Community books integration**: Move from `context/acl2-jupyter-kernel/`
  to `books/jupyter/` in the ACL2 community books.
- **Debugger integration**: common-lisp-jupyter has full DAP support with
  breakpoints, stepping, frame inspection.
- **CCL support**: The current implementation is SBCL-specific (uses
  `sb-ext:disable-debugger`, `sb-introspect`, `save-exec` generates SBCL
  flags). CCL would need a different save mechanism and ZeroMQ support.

## 12. Key Technical Decisions

1. **Subclass common-lisp-jupyter, not fork**: Minimizes maintenance burden.
   We override ~4 generic functions and get all the ZeroMQ / wire protocol /
   channel management / widget support for free.

2. **In-process, not subprocess**: Evaluating directly inside ACL2's Lisp
   image gives us access to the world, proper output routing, and is simpler
   than managing a child process.

3. **`save-exec` for the binary**: ACL2's own `save-exec` creates a shell
   script + core pair with all the right SBCL flags (`--control-stack-size 64`,
   `--dynamic-space-size`, `--tls-limit`, etc.). This ensures all threads
   get adequate stack space and the binary has exactly the same structure as
   `saved_acl2` itself.

4. **ASDF system, not ACL2 book**: The kernel loads via Quicklisp/ASDF from
   raw Lisp after `:q`, bypassing ACL2's book certification. ACL2 books use
   `include-book` which doesn't make sense for CL library loading.

5. **Reuse bridge's output routing pattern**: The `with-acl2-channels-bound`
   and `with-acl2-output-to` macros from `bridge-sbcl-raw.lsp` are proven
   to correctly capture all ACL2 output (CW, FMT, proofs-co, trace-co).
   We copy the pattern rather than depending on the bridge book.

6. **Connection file via command-line args**: The `{connection_file}` from
   kernel.json argv passes through the shell script's `"$@"` and becomes
   available via `(uiop:command-line-arguments)`. This is the same mechanism
   used by the standard CL SBCL kernel.
