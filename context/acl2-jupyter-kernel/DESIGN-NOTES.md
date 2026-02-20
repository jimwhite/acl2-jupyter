# ACL2 Jupyter Kernel — Design Notes

Analysis of design decisions, architecture, and comparison with
Ruben Gamboa's `acl2_jupyter` (Python Jupyter kernel) and the
`centaur/bridge` (ACL2 Bridge) reference implementation.

---

## 1. THE CRITICAL INSIGHT: LP Context Is Required

**This is the single most important design constraint.**

ACL2 events (`include-book`, `defthm`, etc.) require LP (Logic
Programming loop) context: `*ld-level*` > 0, `catch 'local-top-level`,
`acl2-unwind-protect-stack`.  Without this context,
`throw-raw-ev-fncall` calls `interface-er` → `(error "ACL2 Halted")`
instead of throwing cleanly, causing stack exhaustion.

| Mechanism | Raw `(eval form)` | With LP scaffolding |
|---|---|---|
| `*ld-level*` | 0 (outside LP) | > 0 (inside LP) |
| `catch 'local-top-level` | absent | present |
| `throw-raw-ev-fncall` | calls `interface-er` → crash | clean throw |
| `include-book` | **FAILS** (stack exhaustion) | **WORKS** |
| `defthm` with failure | hard error | recoverable |

### Three approaches to providing LP context

**A. `ld` wrapping (acl2_jupyter's approach)**
```lisp
(ld '(form1 form2 ...) :ld-verbose nil :ld-prompt nil ...)
```
Simple but conflates result values with stdout — no structured results.

**B. LP scaffolding + `trans-eval` (our kernel's approach)**
Copy the essential LP setup from `ld-fn0` (raw code in `ld.lisp`),
then use `trans-eval` for each form individually.  This gives us:
- LP context (identical catch tags / `*ld-level*` / unwind-protect)
- Structured results via `(mv erp (stobjs-out . replaced-val) state)`
- Proper `execute_result` Jupyter messages (not stdout dumps)

**C. `ld` wrapping for Bridge tests**
The Bridge test fixture wraps commands in `(ld '(...) ...)` inside
`(bridge::in-main-thread ...)` — same approach as acl2_jupyter.
This is necessary because Bridge's `in-main-thread` does raw eval
with no LP context.

### Our kernel implementation (approach B)

```lisp
(defun jupyter-read-eval-print-loop (channel state)
  ;; LP scaffolding from ld-fn0:
  (acl2::acl2-unwind acl2::*ld-level* nil)
  (push nil acl2::*acl2-unwind-protect-stack*)
  (let ((acl2::*ld-level* (1+ old-ld-level)))
    (catch 'acl2::local-top-level
      (loop
        ;; Read via ACL2's own reader
        (acl2::read-object channel state)
        ;; Evaluate via trans-eval — returns structured results
        (acl2::trans-eval-default-warning form 'acl2-jupyter state t)
        ;; Extract result → jupyter:execute-result
        ...))))
```

`trans-eval` returns `(mv erp (stobjs-out . replaced-val) state)`:
- For error triples (`stobjs-out = (NIL NIL STATE)`): display `(cadr replaced-val)`
- For non-triples: display `replaced-val` directly
- `:invisible` values are suppressed (same as LD's `:command-conventions`)

---

## 2. Architecture: Main Thread Dispatch

Both Bridge and our kernel use the same pattern:

- **Worker/Shell thread**: handles protocol (Bridge socket / Jupyter ZMQ)
- **Main thread**: owns ACL2 state, 128MB stack, output channels

Every command is dispatched to the main thread. Bridge uses
`(bridge::in-main-thread ...)`, our kernel uses our own
`(in-main-thread ...)` macro (modeled on Bridge's `in-main-thread-aux`).

Our macro additionally forwards all Jupyter shell-thread specials
(`*kernel*`, `*stdout*`, `*stderr*`, `*stdin*`, `*message*`,
`*thread-id*`, `*html-output*`, `*markdown-output*`) so Jupyter
protocol calls work on the main thread.

---

## 3. Why We Don't Use `ld` Directly

`ld` conflates result values with stdout. All output — proof attempts,
event processing, and result values — goes to `standard-co` / `proofs-co`.
There is no way to extract structured per-form results for Jupyter
`execute_result` messages.

acl2_jupyter accepts this limitation: everything is text in stdout.
We chose to go further by copying the LP scaffolding from `ld-fn0`
and using `trans-eval` directly, which returns structured results.

### What we copy from `ld-fn0` (raw code in ld.lisp ~1870)

```lisp
(ACL2-UNWIND *LD-LEVEL* NIL)
(PUSH NIL *ACL2-UNWIND-PROTECT-STACK*)
(LET* ((*LD-LEVEL* (1+ *LD-LEVEL*)))
  (CATCH 'LOCAL-TOP-LEVEL ...))
```

### What we use from `ld-read-eval-print`

```lisp
(trans-eval-default-warning form 'top-level state t)
;; returns (mv erp (stobjs-out . replaced-val) state)
```

This gives us the best of both worlds: LP context for correctness,
and structured results for proper Jupyter display.

---

## 4. Reading: ACL2's Own Reader via Channels

We use ACL2's channel system to read user code. A temporary `:object`
input channel is created from a CL string stream:

```lisp
(defun make-string-input-channel (string)
  (let ((channel (gensym "JUPYTER-INPUT")))
    (setf (get channel *open-input-channel-type-key*) :object)
    (setf (get channel *open-input-channel-key*)
          (make-string-input-stream string))
    channel))
```

`acl2::read-object` reads from this channel using `*acl2-readtable*`
and the current package — handling all reader macros, keywords, etc.
No Python-side s-expression parsing needed (unlike acl2_jupyter's
`canonize_acl2` which is ~190 lines of Python parser).

---

## 5. Output Routing

### Proof/event output → Jupyter stdout (streaming)

ACL2's output channels (`standard-co`, `proofs-co`, `trace-co`) are
bound to a temporary character output channel backed by
`*standard-output*`, which is a synonym stream to `jupyter::*stdout*`.
Output appears incrementally as ACL2 produces it — superior to
acl2_jupyter's batch approach.

### Per-form results → Jupyter `execute_result` (structured)

`trans-eval` returns `(stobjs-out . replaced-val)`. For error triples
(`stobjs-out = (NIL NIL STATE)`), we extract `(cadr replaced-val)` and
send it as `jupyter:execute-result` with `text/plain` MIME type.
Values printed with `*print-case* :downcase` and `*print-pretty* t`
in the current ACL2 package.

Special cases:
- `:invisible` values suppressed (same as LD's `:command-conventions`)
- `:q` ignored (don't exit kernel)
- `erp-flag` non-nil: error already printed to stdout, no result sent
- Non-error-triples: display `replaced-val` directly unless it's just `state`
## 6. Error Handling

ACL2 errors within `trans-eval` are handled internally — the error is
printed to ACL2's output channels (which route to Jupyter stdout), and
`trans-eval` returns `erp` non-nil. We simply skip sending an
`execute_result` for that form.

The `handler-case` around `in-main-thread` catches truly unexpected CL
conditions (SBCL errors, memory exhaustion). Non-local exits (ACL2
`throw`) are caught by the `unwind-protect` in `in-main-thread-aux`
and converted to a `simple-error` condition.

The LP scaffolding's `(catch 'acl2::local-top-level ...)` handles
ACL2's internal throw-based control flow (e.g., `throw-raw-ev-fncall`).

---

## 7. `trans-eval` Return Value Format

```
(mv erp (stobjs-out . replaced-val) state)
```

- `erp` non-nil → error (already printed to channels)
- `stobjs-out` → signature of the return type
- `replaced-val` → the actual return value(s)

For error triples (`*error-triple-sig*` = `'(NIL NIL STATE)`):
```
replaced-val = (erp-flag val state-symbol)
```
- `(car replaced-val)` = erp-flag (T means the form itself signaled error)
- `(cadr replaced-val)` = val (the displayable result)

For single values, `replaced-val` is just the value.

---

## 8. Kernel Startup Sequence

```lisp
(defun start (&optional connection-file)
  ;; 1. Turn off raw mode (needed only for LP to call this function)
  ;; 2. Disable debugger
  ;; 3. Suppress slow alist/array warnings
  ;; 4. Start Jupyter in a thread (like Bridge's listener thread)
  ;; 5. Block main thread in work loop (like Bridge's start-fn)
  ...)
```

The startup script (`start-kernel.sh`) loads via quicklisp/ASDF inside
a saved ACL2 core, enters LP, enables raw mode, then calls `(start)`.

---

## 9. Test Architecture

`test_dual.py` runs every test through both Bridge and Kernel backends:

- **Bridge fixture**: starts `saved_acl2` with Bridge, connects via
  Unix socket, wraps commands in `(bridge::in-main-thread (ld '(...) ...))`
- **Kernel fixture**: starts ACL2 Jupyter kernel via `KernelManager`,
  sends `execute_request`, reads `execute_result`/`stream`/`error`

Both fixtures return `(result, stdout, error)`. Tests check
`(result or "") + stdout` for expected values.

The Bridge fixture wraps in `ld` for the same reason our kernel uses
LP scaffolding — without LP context, `include-book` etc. fail.

---

## 10. Comparison: Our Kernel vs acl2_jupyter

| Feature | acl2_jupyter | Our kernel |
|---|---|---|
| Language | Python (external) | Common Lisp (in-process) |
| ACL2 connection | Bridge socket | Direct (same process) |
| LP context | `ld` wrapper | LP scaffolding from `ld-fn0` |
| Result extraction | stdout text | `trans-eval` structured results |
| Jupyter result type | `stream` (stdout) | `execute_result` (text/plain) |
| Output streaming | batch (accumulate then send) | incremental (real-time) |
| Reader | Python s-expr parser (~190 lines) | ACL2's own `read-object` |
| Default package | ACL2S | ACL2 |
