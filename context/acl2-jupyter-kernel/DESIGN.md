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
├── packages.lisp             # Package definition (acl2-jupyter)
├── kernel.lisp               # Kernel class + evaluate-code + output routing + start
├── complete.lisp             # ACL2 symbol completion
├── inspect.lisp              # ACL2 documentation inspection
├── installer.lisp            # Kernelspec installer (generates kernel.json)
├── build-kernel-image.sh     # Build script: creates saved_acl2_jupyter via save-exec
├── install-kernelspec.sh     # Install script: writes kernel.json
├── test_dual.py              # 22 dual-fixture tests (Bridge vs Kernel)
└── test_metadata.py          # 7 tests for cell metadata (events, package)
```

## 5. Component Details

### 5.1 kernel.lisp — Core Evaluation

**Threading model**:
- Shell thread (Jupyter): owns `*kernel*`, IOPub socket, protocol
- Main thread (ACL2): owns 128MB stack, ACL2 state, output channels
- `evaluate-code` runs on the shell thread.  It dispatches ACL2 work
  to the main thread via `in-main-thread`, which blocks until done.

**Persistent LP context** (set up once by `start`):
- The main thread lives inside a persistent LP context mirroring `ld-fn0`
- `*ld-level*` stays at 1 for the kernel's lifetime
- `acl2-unwind-protect-stack` persists across cells
- Command history accumulates (`:pbt`, `:pe`, `:ubt` work across cells)

**Output routing** (`with-acl2-output-to`):
- Creates a temporary ACL2 output channel symbol
- Sets its `*open-output-channel-key*` property to the Jupyter stdout stream
- Rebinds `*standard-output*`, `*trace-output*`, `*error-output*`, `*debug-io*`
- Uses `with-acl2-channels-bound` (via PROGV) to redirect `standard-co`,
  `proofs-co`, `trace-co` — the ACL2 globals that `CW`, `FMT`, and proof
  output use
- Cleans up on unwind

**Form reading** (via ACL2's own reader):
- Creates a temporary ACL2 `:object` input channel backed by a CL string stream
- ACL2's `read-object` handles all reader macros, packages, etc.
- Handles three kinds of input:
  1. Standard s-expressions: `(defun foo (x) x)`
  2. ACL2 keyword commands: `:pe append` → `(ACL2::PE 'APPEND)` (via
     `expand-keyword-command` which looks up arity from the world)
  3. String commands: `"ACL2S"` → `(IN-PACKAGE "ACL2S")`
- `:q` exits the kernel process

**Evaluation** (`evaluate-code` → `jupyter-read-eval-print-loop`):
- Dispatches to main thread via `in-main-thread`
- Wraps eval in `acl2::with-suppression` (unlocks COMMON-LISP package,
  same as LP's own wrapping of `ld-fn`)
- Each form is evaluated via `trans-eval-default-warning`, which gives us:
  - Structured `(mv erp (stobjs-out . replaced-val) state)` results
  - ACL2's own reader (via `read-object` on a channel)
  - Full event processing, command landmarks, world updates
- For error triples `(stobjs-out = *error-triple-sig*)`:
  display `val` via `jupyter:execute-result` unless `:invisible`
- For non-triples: display `replaced-val` directly
- After each successful `trans-eval`, calls `maybe-add-command-landmark`
  with saved `old-wrld` and `old-default-defun-mode` — this is what
  makes `:pbt`, `:pe`, `:ubt` etc. work
- Per-cell `catch 'local-top-level` so a throw aborts the rest of the cell
  but not the kernel
- After eval completes, captures world diff and current package as cell
  metadata (see §5.5)

**Code completeness** (`code-is-complete`):
- Tries to read the code; if `end-of-file` → "incomplete", if other error →
  "invalid", otherwise → "complete"

**Startup** (`start`):
- Calls `acl2-default-restart` for image initialization
- Performs LP first-entry initialization (normally done by `lp` on first
  call): `saved-output-reversed`, `set-initial-cbd`,
  `establish-project-dir-alist`, `setup-standard-io`
- Suppresses slow alist/array warnings for interactive use
- Sets up persistent LP context (mirroring `ld-fn0`'s raw code):
  `acl2-unwind`, pushes onto `*acl2-unwind-protect-stack*`, `*ld-level*` = 1
- Starts Jupyter in a thread via `jupyter:run-kernel`
- Blocks main thread in work loop (`main-thread-loop`) inside LP context

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
The installer uses generic functions `make-kernel-argv` and `make-kernel-env`
dispatched on `(uiop:implementation-type)` so other CL implementations can
be supported by adding methods.  For SBCL the generated spec is:

```json
{
  "argv": [
    "/usr/local/bin/sbcl",
    "--dynamic-space-size", "32000",
    "--control-stack-size", "64",
    "--tls-limit", "16384",
    "--disable-ldb",
    "--core", "/path/to/saved_acl2_jupyter.core",
    "--end-runtime-options",
    "--no-userinit",
    "--eval", "(acl2-jupyter-kernel:start)",
    "{connection_file}"
  ],
  "env": { "SBCL_HOME": "/usr/local/lib/sbcl/" },
  "display_name": "ACL2",
  "language": "acl2",
  "interrupt_mode": "message",
  "metadata": {}
}
```

This bypasses the `saved_acl2_jupyter` shell script wrapper — `sbcl` is
invoked directly with the right core and runtime flags.  `SBCL_HOME` is
provided via `env` so SBCL can find its contribs.

### 5.5 Cell Metadata — Events and Package

Each `execute_reply` carries metadata describing what the cell changed in
the ACL2 world.  This is implemented via a `execute-reply-metadata` generic
function added to common-lisp-jupyter (see §12, decision 7).

**World diff capture** (in `evaluate-code`, after eval completes):
1. Save the old world (`acl2::w acl2::*the-live-state*`) before eval
2. After eval, walk the new world's triples until we reach the old world
3. Collect triples where `(car triple)` = `EVENT-LANDMARK` and
   `(cadr triple)` = `GLOBAL-VALUE`
4. Convert each event's value `(cddr triple)` to a string via `prin1-to-string`
5. Store the resulting vector in the kernel's `cell-events` slot

**Package capture**: After eval, read `(acl2::current-package
acl2::*the-live-state*)` and store in `cell-package`.

**Wire format** (in `execute-reply` message, `metadata` field):
```json
{
  "metadata": {
    "events": [
      "(DEFUN APP (X Y) ...)",
      "(DEFTHM APP-ASSOC ...)"
    ],
    "package": "ACL2"
  }
}
```

- `events`: JSON array of strings.  Each string is the `prin1` representation
  of an ACL2 event landmark value.  Empty array `[]` for cells with no events
  (e.g., arithmetic).
- `package`: JSON string.  The current ACL2 package after the cell executes.

This metadata enables frontends and tools to track world state without
parsing ACL2 output.

## 6. The Saved Image: `saved_acl2_jupyter`

### Build via ACL2's `save-exec`

The kernel binary is built using ACL2's own `save-exec` mechanism — the same
one that creates `saved_acl2` itself. This is done by `build-kernel-image.sh`:

1. Start `saved_acl2` and exit the ACL2 read-eval-print loop (`:q`)
2. Load Quicklisp and the `acl2-jupyter-kernel` ASDF system
3. Call `save-exec` with `:return-from-lp nil` (so the image starts
   directly at `--eval` without entering LP)

```lisp
(save-exec "saved_acl2_jupyter" nil
           :return-from-lp nil)
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
  "$@"
```

The kernel.json (from installer.lisp, §5.4) adds `--eval
'(acl2-jupyter-kernel:start)'` and `{connection_file}` to the argv, so
the full command line becomes:

```
sbcl ... --core saved_acl2_jupyter.core --end-runtime-options --no-userinit \
  --eval '(acl2-jupyter-kernel:start)' /path/to/connection.json
```

Key points:

- **`--control-stack-size 64`**: Sets 64 MB control stack for ALL threads in
  the SBCL process. This is critical — the Jupyter Shell thread (created by
  bordeaux-threads via common-lisp-jupyter) inherits this setting. Without it,
  threads get SBCL's default ~2 MB which is insufficient for ACL2's deep
  recursion during `include-book`, proof search, etc.
- **`(acl2-jupyter-kernel:start)`**: The `start` function (see §5.1)
  calls `acl2-default-restart` for ACL2 initialization, sets up the
  persistent LP context, spawns the Jupyter shell thread, and blocks
  the main thread in the work loop.

### Startup Flow

```
Jupyter launches kernel.json argv:
  sbcl --control-stack-size 64 ... --core saved_acl2_jupyter.core
       --eval '(acl2-jupyter-kernel:start)' /path/to/connection.json

  → SBCL starts, loads saved_acl2_jupyter.core

  → (acl2-jupyter-kernel:start)
    → (acl2-default-restart)           ; ACL2 image initialization
    → LP first-entry init:
        saved-output-reversed, set-initial-cbd,
        establish-project-dir-alist, setup-standard-io
    → Suppress W/A warnings for interactive use
    → Set up persistent LP context:
        acl2-unwind, push *acl2-unwind-protect-stack*, *ld-level* = 1
    → conn = (first (uiop:command-line-arguments))
    → Spawn Jupyter shell thread via (jupyter:run-kernel 'kernel conn)
        → Parses connection file (JSON: transport, IP, ports, key)
        → Creates ZeroMQ sockets (shell, control, iopub, stdin, heartbeat)
        → Spawns heartbeat thread
        → Sends kernel_info_reply, status: idle
    → Block main thread in (main-thread-loop) inside LP context
        → Waits for work dispatched by shell thread via in-main-thread
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
3. common-lisp-jupyter's shell thread receives it, calls `evaluate-code`
4. `evaluate-code` dispatches work to the main thread via `in-main-thread`:
   a. Save old world: `old-wrld = (acl2::w *the-live-state*)`
   b. Redirect output via `with-acl2-output-to` (ACL2 channels + CL streams
      → Jupyter IOPub stdout)
   c. Open an ACL2 input channel on the cell text
   d. Read forms one at a time via `acl2::read-object` (handles keywords,
      strings, s-expressions)
   e. For each form, inside `(catch 'acl2::local-top-level ...)`:
      - Call `(acl2::trans-eval-default-warning form ctx state t)`
      - On success: extract `(stobjs-out . replaced-val)`, display `val`
        via `jupyter:execute-result` (unless `:invisible`)
      - Call `maybe-add-command-landmark` so history commands work
   f. After all forms: capture world diff (EVENT-LANDMARK triples) into
      `cell-events`, read `current-package` into `cell-package`
   g. Return `(values)` — no values means success
5. common-lisp-jupyter calls `(execute-reply-metadata *kernel*)` to get
   the events/package metadata
6. common-lisp-jupyter sends `execute_reply` with metadata on shell channel

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
| `acl2::trans-eval-default-warning` | Evaluate a form with full ACL2 semantics |
| `acl2::*ld-level*` | Current nesting depth of `ld` |
| `acl2::current-package` | Get the current ACL2 package name |
| `acl2::acl2-default-restart` | Initialize ACL2 image (called by `start`) |
| `acl2::maybe-add-command-landmark` | Record a command in the world |
| `acl2::with-suppression` | Unlock COMMON-LISP package around eval |
| `acl2::read-object` | Read one form from an ACL2 input channel |
| `acl2::keyword-command-arity` | Look up keyword command arity from world |

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
python -m pytest test_dual.py test_metadata.py -v --timeout=120
```

29 tests total: 22 dual-backend tests (arithmetic, defun, defthm, keyword
commands, include-book, undo, etc. each run through both Bridge and Kernel
fixtures) and 7 metadata tests (events array, package tracking).

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
- **CCL support**: The installer already dispatches on
  `(uiop:implementation-type)` so adding CCL requires only new methods for
  `make-kernel-argv` and `make-kernel-env`.
- **Richer metadata**: Include theorem statements, proof summaries, or
  timing data in cell metadata.

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

7. **`execute-reply-metadata` extension to common-lisp-jupyter**: Rather than
   monkey-patching or subclassing the shell handler, we added a
   `execute-reply-metadata` generic function to common-lisp-jupyter.  The
   default method returns nil (no metadata).  The ACL2 kernel specializes it
   to return the world events and current package.  This required three small
   changes to common-lisp-jupyter: export the symbol, define the generic, and
   pass its return value through `send-execute-reply-ok`.

8. **`trans-eval` over raw `eval`**: ACL2's `trans-eval` provides structured
   results, full event processing, and proper error handling.  Raw `eval`
   bypasses the LP context and causes stack exhaustion on complex forms.
   See DESIGN-NOTES.md for the detailed rationale.

9. **Persistent LP context**: Rather than entering/exiting LP per cell, the
   main thread lives permanently at `*ld-level*` = 1.  This preserves command
   history, allows `:pbt`/`:ubt` across cells, and avoids LP startup cost.
