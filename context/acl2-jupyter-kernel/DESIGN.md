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
│  saved_acl2_jupyter_kernel  (SBCL core + ACL2 image)    │
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

### 3.4 saved_acl2_jupyter (existing CL kernel launcher)

The file `context/extension/saved_acl2_jupyter` shows the pattern for
launching the CL kernel today:

```sh
#!/bin/sh
export SBCL_HOME='/usr/local/lib/sbcl/'
exec "/usr/local/bin/sbcl" \
  --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 \
  --disable-ldb --core "/home/acl2/saved_acl2.core" \
  ${SBCL_USER_ARGS} --end-runtime-options \
  --load /home/jovyan/quicklisp/setup.lisp \
  --eval "(ql:quickload :common-lisp-jupyter ...)" \
  --eval "(jupyter:run-kernel 'jupyter/common-lisp:kernel)" \
  --eval '(acl2::sbcl-restart)' "$@"
```

This loads the generic CL kernel into ACL2's image. Our approach will be
similar but loading `acl2-jupyter-kernel` instead.

## 4. File Structure

```
context/acl2-jupyter-kernel/
├── acl2-jupyter-kernel.asd   # ASDF system definition
├── packages.lisp             # Package definition (acl2-jupyter-kernel / jupyter/acl2)
├── kernel.lisp               # Kernel class + evaluate-code + output routing
├── complete.lisp             # ACL2 symbol completion
├── inspect.lisp              # ACL2 documentation inspection
└── installer.lisp            # Kernelspec installer
```

Eventually this will move to `books/jupyter/` in the ACL2 community books.

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
  2. ACL2 keyword commands: `:pe append` (read as a list)
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
- Tries to read the code; if `end-of-file` → "incomplete", if other error → "invalid"

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

Generates a `kernel.json` that tells Jupyter to launch the kernel via:

```json
{
  "argv": [
    "saved_acl2_jupyter_kernel",
    "{connection_file}"
  ],
  "display_name": "ACL2",
  "language": "acl2",
  "interrupt_mode": "message"
}
```

The `saved_acl2_jupyter_kernel` script (see §6) handles all bootstrapping.

## 6. The Saved Image: `saved_acl2_jupyter_kernel`

### Why a Saved Image is Needed

The ACL2 binary (`saved_acl2`) launches SBCL with the ACL2 core and
immediately enters `(acl2::sbcl-restart)` which starts the ACL2 read-eval-print
loop. This REPL intercepts input and doesn't understand raw CL `--eval`
arguments properly (as we discovered — ACL2 rejects `#P` pathnames, `REQUIRE`,
etc.).

We need a separate launcher script (like `saved_acl2_jupyter`) that:

1. Uses the same SBCL binary and ACL2 core (`saved_acl2.core`)
2. Does **not** call `(acl2::sbcl-restart)` immediately
3. Instead loads Quicklisp, loads our kernel system, then starts the kernel
4. The kernel's `evaluate-code` handles the ACL2 ↔ CL boundary

### Launcher Script Pattern

```sh
#!/bin/sh
export SBCL_HOME='/usr/local/lib/sbcl/'
exec "/usr/local/bin/sbcl" \
  --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 \
  --disable-ldb \
  --core "/home/acl2/saved_acl2.core" \
  ${SBCL_USER_ARGS} --end-runtime-options \
  --load /home/jovyan/quicklisp/setup.lisp \
  --eval "(ql:quickload :acl2-jupyter-kernel)" \
  --eval "(acl2-jupyter-kernel:install)" \
  --eval "(jupyter:run-kernel 'acl2-jupyter-kernel:kernel)" \
  "$@"
```

Or, for a pre-built saved image approach (faster startup):

```lisp
;; Build script: build-saved-image.lisp
(require :sb-bsd-sockets)
(load (merge-pathnames "quicklisp/setup.lisp" (user-homedir-pathname)))
(ql:quickload :acl2-jupyter-kernel)
(acl2-jupyter-kernel:install)
(sb-ext:save-lisp-and-die "saved_acl2_jupyter_kernel"
  :toplevel (lambda ()
              (jupyter:run-kernel 'acl2-jupyter-kernel:kernel
                                  (first (uiop:command-line-arguments))))
  :executable t)
```

### Alternative: Dockerfile Build Step

In the Dockerfile, after building ACL2 and certifying books:

```dockerfile
# Build the ACL2 Jupyter kernel saved image
RUN /home/acl2/saved_acl2 --eval '...' # (raw Lisp eval to load QL and build)
```

Or more practically, we create the launcher script during install:

```dockerfile
# Install ACL2 Jupyter kernel
RUN ln -s /workspaces/acl2-jupyter-stp/context/acl2-jupyter-kernel \
          /home/jovyan/quicklisp/local-projects/acl2-jupyter-kernel
RUN sbcl --core /home/acl2/saved_acl2.core --no-userinit \
    --load /home/jovyan/quicklisp/setup.lisp \
    --eval '(ql:quickload :acl2-jupyter-kernel)' \
    --eval '(acl2-jupyter-kernel:install)' \
    --eval '(sb-ext:exit)'
```

## 7. How It Runs

### Startup Sequence

1. Jupyter launches `saved_acl2_jupyter_kernel {connection_file}`
2. SBCL starts with `saved_acl2.core` (ACL2 is loaded)
3. Quicklisp loads; `acl2-jupyter-kernel` system loads (which pulls in
   `common-lisp-jupyter` and all its ZeroMQ dependencies)
4. `jupyter:run-kernel` is called with our `kernel` class and the connection file
5. common-lisp-jupyter parses the connection file (JSON with transport, IP,
   ports, key, signature scheme)
6. ZeroMQ sockets are created for shell, control, iopub, stdin, heartbeat
7. The control thread (current thread) enters `run-control` loop
8. A shell thread is spawned for `run-shell` loop
9. A heartbeat thread echoes pings
10. Kernel sends `status: starting` then `status: idle` on iopub

### Cell Execution Flow

1. User submits cell code (e.g., `(defun app (x y) ...)`)
2. Jupyter frontend sends `execute_request` on shell channel
3. common-lisp-jupyter's `run-shell` receives it
4. Calls our `evaluate-code` method
5. We parse the code into forms via `read-acl2-forms`
6. For each form:
   a. Bind `*standard-output*` → Jupyter's iopub stream
   b. Redirect ACL2 channels via `with-acl2-output-to`
   c. Eval with STATE bound: `(let ((state *the-live-state*)) ,form)`
   d. Display results via `jupyter:execute-result`
7. common-lisp-jupyter sends `execute_reply` on shell

### Completion Flow

1. User presses Tab after typing `app`
2. Frontend sends `complete_request` with code and cursor position
3. Our `complete-code` finds token `APP`, searches ACL2 package
4. Returns matches with types (function/macro/variable)

### Inspection Flow

1. User presses Shift-Tab on `append`
2. Frontend sends `inspect_request`
3. Our `inspect-code` looks up `APPEND` in ACL2's world
4. Returns markdown with signature, guard, documentation, type

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

## 9. Comparison with Alternatives

| Approach | Pros | Cons |
|----------|------|------|
| **This kernel** (CL in-process) | Direct world access, proper output, fast, completion/inspection | Must build saved image, ACL2 internals coupling |
| Python pexpect kernel | Simple, no CL deps | Fragile prompt scraping, no completion, flat output |
| ACL2 Bridge + Python | Clean protocol, async | Extra process, extra protocol layer, no ZeroMQ integration |
| Raw CL kernel (`common-lisp-jupyter`) | Already works | No ACL2-specific features, must use `(acl2::...)` prefixes |

## 10. Future Work

- **Debugger integration**: common-lisp-jupyter has full DAP support with
  breakpoints, stepping, frame inspection. Our kernel class could override
  `debug-*` methods to provide ACL2-aware debugging.
- **Proof output formatting**: Route `proofs-co` output to a separate
  stream/display for structured proof display.
- **XDOC rendering**: Render ACL2 XDOC documentation as HTML in inspect
  results.
- **Book loading progress**: Report `include-book` progress via Jupyter
  status messages.
- **Community books integration**: Move from `context/acl2-jupyter-kernel/`
  to `books/jupyter/` with proper `cert.acl2`, `portcullis.acl2`, etc.
- **CCL support**: The output routing code uses `#+sbcl` for
  `sb-sys:without-interrupts` in the bridge, but our version avoids that.
  Main concern is ZeroMQ (pzmq) support on CCL.
- **Image-based install**: Pre-build a core with all dependencies baked in
  for instant startup (no Quicklisp load time).

## 11. Current Status

### Files Created

| File | Status | Description |
|------|--------|-------------|
| `acl2-jupyter-kernel.asd` | Done | ASDF system definition, depends on common-lisp-jupyter |
| `packages.lisp` | Done | Package `acl2-jupyter-kernel` (nickname `jupyter/acl2`) |
| `kernel.lisp` | Done | Kernel class, `evaluate-code`, output routing, form parsing |
| `complete.lisp` | Done | Symbol completion across ACL2 packages |
| `inspect.lisp` | Done | Documentation lookup with world property access |
| `installer.lisp` | Done | Kernelspec installer (generates kernel.json) |

### Not Yet Done

- **Saved image / launcher script**: Need `saved_acl2_jupyter_kernel` script
  that boots saved_acl2.core, loads Quicklisp + our system, and runs the kernel.
  Cannot use bare `saved_acl2` because its `sbcl-restart` enters the ACL2 REPL
  which intercepts `--eval` flags.
- **Testing**: No load test yet. Plain SBCL can't load it (no ACL2 package).
  Need the saved image to validate.
- **Dockerfile integration**: Build step to create saved image and install
  kernelspec.
- **Logo/resources**: No ACL2 logo for the kernel picker UI.

## 12. Key Technical Decisions

1. **Subclass common-lisp-jupyter, not fork**: Minimizes maintenance burden.
   We override ~4 generic functions and get all the ZeroMQ / wire protocol /
   channel management / widget support for free.

2. **In-process, not subprocess**: Evaluating directly inside ACL2's Lisp
   image gives us access to the world, proper output routing, and is simpler
   than managing a child process.

3. **ASDF system, not ACL2 book (for now)**: ACL2 books use `include-book`
   which doesn't make sense for CL library loading. The kernel loads via
   Quicklisp/ASDF from raw Lisp, bypassing ACL2's book certification.
   It will live under `books/jupyter/` but load via `include-raw` or
   a trust-tag protected `progn!`.

4. **Reuse bridge's output routing pattern**: The `with-acl2-channels-bound`
   and `with-acl2-output-to` macros from `bridge-sbcl-raw.lsp` are proven
   to correctly capture all ACL2 output (CW, FMT, proofs-co, trace-co).
   We copy the pattern rather than depending on the bridge book.

5. **Connection file via common-lisp-jupyter**: `jupyter:run-kernel` handles
   parsing the connection file (JSON with transport/IP/ports/key) and setting
   up ZeroMQ sockets. No need for us to handle TCP vs Unix sockets ourselves —
   that's all inside pzmq via the transport URI (`tcp://ip:port` or
   `ipc://path`).
