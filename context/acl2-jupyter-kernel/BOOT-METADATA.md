# ACL2 Boot-strap Metadata Capture

## Overview

The ACL2 source files (`axioms.lisp`, `basis-a.lisp`, `defthm.lisp`, etc.)
are not certifiable books. They build the `saved_acl2` image through a
two-pass boot-strap process implemented in `initialize-acl2`
(`interface-raw.lisp`). Because they are never processed via `include-book`,
the normal Jupyter kernel execution path cannot capture event metadata for
these files. This system solves that gap by replaying the boot-strap process
with instrumentation, then injecting the captured metadata into the
corresponding notebook files.

---

## Research Findings

### ACL2 Build System Architecture

ACL2 8.6 on SBCL 2.6.1 builds in three stages:

1. **Compilation** (`make compile` / `load-acl2`):
   `init.lisp` → `acl2-init.lisp` → `acl2.lisp` define the `ACL2` package
   and `*acl2-files*`, an ordered list of ~43 source file stems. `load-acl2`
   compiles each file to FASL using raw CL `compile-file` + `load`.

2. **Boot-strap initialization** (`initialize-acl2` in `interface-raw.lisp`
   ~L9633): A two-pass process that populates the ACL2 logical world:

   - **Pass 1** (`:program` mode): `ld-skip-proofsp = 'initialize-acl2`.
     Each file in `*acl2-files*` is processed via `ld-fn` / `ld-alist-raw`,
     *except*:
     - Files matching `raw-source-name-p` (stem ends in `"-raw"`) — these
       are pure Common Lisp, loaded by CL `LOAD`, never seen by ACL2's `ld`.
     - `boot-strap-pass-2-a` and `boot-strap-pass-2-b` — deferred to pass 2.

   - **Pass 2** (`:logic` mode): `ld-skip-proofsp = 'include-book`.
     `enter-boot-strap-pass-2` switches the world to `:logic` mode. Then
     the files in `*acl2-pass-2-files*` are re-loaded. This variable is
     defined in `interface-raw.lisp` ~L8643:

     ```
     ("axioms" "memoize" "hons" "serialize" "boot-strap-pass-2-a"
      "float-a" "float-b" "apply-prim" "apply-constraints" "apply"
      "boot-strap-pass-2-b")
     ```

3. **Image save** (`save-acl2`): After `initialize-acl2` completes, the
   fully-populated SBCL heap is saved as `saved_acl2.core` (~240 MB).

**Key data structures:**

| Symbol | Location | Purpose |
|--------|----------|---------|
| `*acl2-files*` | `acl2.lisp` L1109 | Ordered list of all source stems |
| `*acl2-pass-2-files*` | `interface-raw.lisp` L8643 | Subset for pass 2 |
| `raw-source-name-p` | `interface-raw.lisp` L8850 | Predicate: stem ends in `"-raw"` |
| `*lisp-extension*` | `acl2.lisp` | `"lisp"` — file extension |
| `ld-alist-raw` | `interface-raw.lisp` | Builds the LD option alist for a file |
| `enter-boot-strap-mode` | Multiple | Sets up primordial world |
| `enter-boot-strap-pass-2` | Multiple | Switches world to `:logic` mode |

### ACL2 Jupyter Kernel Event Capture

The existing kernel (`kernel.lisp`) captures events via *world diffing*:

1. Before evaluation: snapshot `(w *the-live-state*)` as `world-before`.
2. After `trans-eval`: snapshot again as `world-after`.
3. Compute `(ldiff world-after world-before)` — the new triples.
4. Filter for triples where `(car triple) = 'event-landmark` and
   `(cadr triple) = 'global-value`.
5. Keep only depth-0 events (where `(car event-tuple)` is an integer,
   not a cons — cons indicates a nested/local event).
6. Emit as `display_data` with MIME type
   `application/vnd.acl2.events+json`.

This is the same algorithm our capture script uses.

### script2notebook Build Pipeline

`build_notebooks.py` has a multi-phase pipeline:
- **Phase 1 (convert):** `.lisp` → `.ipynb` using tree-sitter splitting.
- **Phase 1b (inject-boot-metadata):** Add boot-strap event metadata into
  ACL2 source notebooks.
- **Phase 2 (execute):** Run notebooks against the ACL2 kernel for certified
  books.

Raw source files (`-raw` suffix) are converted to notebooks with a Common
Lisp kernel spec since they are pure CL, never processed by ACL2's `ld`.

---

## Plan

The implementation has three layers:

### Layer 1: Lisp capture script

A standalone Lisp script that replays `initialize-acl2`'s two-pass
boot-strap but snapshots the world before/after each file's `ld` call,
extracting event landmarks. Outputs per-file JSON plus a manifest.

### Layer 2: Python injection code

New functions in `build_notebooks.py` that read the captured JSON and inject
`display_data` outputs (matching the kernel's MIME format) into the
corresponding `.ipynb` files.

### Layer 3: Makefile targets

Two new Make targets:
- `boot-metadata` — runs the Lisp capture script.
- `notebooks-inject-boot-metadata` — runs the Python injection.

---

## Implementation Details

### File inventory

| File | Role |
|------|------|
| `context/acl2-jupyter-kernel/capture-boot-metadata-loader.lisp` | **NEW** — Bootstrap loader |
| `context/acl2-jupyter-kernel/capture-boot-metadata.lisp` | **NEW** — Main capture script |
| `context/script2notebook/event_matching.py` | **NEW** — Event/form-to-cell matching |
| `context/script2notebook/inject_boot_metadata.py` | **NEW** — Boot metadata injection |
| `context/script2notebook/test_event_matching.py` | **NEW** — Tests for matching + forms |
| `Makefile` | **MODIFIED** — Venv support + new targets |

### 1. Lisp capture: two-file architecture

#### Problem: SBCL read-time package resolution

The main capture script references `acl2::event-landmark`,
`acl2::*the-live-state*`, `acl2::ld-fn`, etc. SBCL's loader reads the
*entire* file before executing any of it. Since `init.lisp` creates the
`ACL2` package, and `init.lisp` is loaded at runtime (execution time),
the reader fails with:

```
Package ACL2 does not exist.
```

#### Solution: loader/main split

**`capture-boot-metadata-loader.lisp`** — a ~30-line bootstrap that:

1. Disables the SBCL debugger (`sb-ext:disable-debugger`).
2. Loads `init.lisp` (creating the ACL2 package).
3. Resolves the main script relative to `*load-pathname*` and loads it.
4. Wraps everything in a `handler-case` for clean error exit.

This file contains *no* `acl2::` prefixed symbols, so the reader succeeds.

**`capture-boot-metadata.lisp`** — the main script (~320 lines), loaded
*after* `init.lisp` has run. It can freely use `acl2::` symbols.

#### Capture script structure

The main script has these functional sections:

**Output directory setup** (`*metadata-dir*`):
- Defaults to `.boot-metadata/` under CWD.
- Overridable via `$ACL2_BOOT_METADATA_DIR`.
- Uses `sb-ext:posix-getenv` (not `uiop:getenv`, which is unavailable in
  bare SBCL).

**Minimal JSON writer** (no external dependencies):
- `json-escape` — proper JSON string escaping (backslash, quotes,
  control characters, Unicode).
- `write-json-string-array` — `["a", "b", ...]`.
- `write-metadata-json` — writes an alist as a JSON object. Handles
  string, integer, null, boolean, and string-list values.

**World-diff event extraction** (`extract-events-since`):
Mirrors the kernel's algorithm:
```common-lisp
(loop for triple in (ldiff current-world baseline-world)
      when (and (eq (car triple) 'acl2::event-landmark)
                (eq (cadr triple) 'acl2::global-value))
      collect (cddr triple))
```
Then filters for depth-0 events and produces two parallel arrays via
`(VALUES events forms)`:
- **events**: `prin1-to-string` of each event tuple with
  `*print-case* :upcase` — the full event landmark including type
  prefix (e.g., `(DEFUN FOO ...)` or `(((DEFUN . T) FOO . :CLC) ...)`).
- **forms**: `prin1-to-string` of `(access-event-tuple-form et)` with
  `*print-case* :downcase` — the original submitted source form,
  stripped of `LOCAL` wrappers via `remove-local` (e.g.,
  `(defun foo ...)`).

This matches the dual output produced by the ACL2 Jupyter kernel
(`kernel.lisp` lines ~400–480).

**Per-file capture** (`capture-file-ld`):
1. Snapshots `(w *the-live-state*)` and `max-absolute-event-number`.
2. Calls `(ld-fn (ld-alist-raw filename skip-proofsp :error) state nil)`.
3. Snapshots again.
4. Calls `extract-events-since` on the before/after worlds, receiving
   `(VALUES events forms)`.
5. Records an alist of metadata (source file, stem, pass, position,
   timing, event counts, event strings, form strings, current package).
6. Returns `T` on success, `NIL` on error.

**Main orchestrator** (`run-capture`):
1. ~~Load `init.lisp`~~ (done by loader now).
2. `(load-acl2 :load-acl2-proclaims *do-proclaims*)` — compile/load FASLs.
3. Enter boot-strap mode:
   ```common-lisp
   (let ((*features* (cons :acl2-loop-only *features*)))
     (set-initial-cbd)
     (makunbound '*copy-of-common-lisp-symbols-from-main-lisp-package*)
     (enter-boot-strap-mode nil (get-os)))
   ```
4. Pass 1: iterate `*acl2-files*`, skip raw sources and pass-2-only files,
   call `capture-file-ld` with `ld-skip-proofsp = 'initialize-acl2`.
5. `(enter-boot-strap-pass-2)`. Then iterate `*acl2-pass-2-files*`,
   calling `capture-file-ld` with `ld-skip-proofsp = 'include-book`.
6. Call `write-results` to emit all JSON files.

**Error handling**:
- Top-level `handler-case` catches `serious-condition`, writes partial
  results, then exits with code 1.
- `safe-exit` tries `acl2::exit-lisp`, falls back to `sb-ext:exit`.
- Per-file errors are captured as metadata entries with `"error": true`
  rather than aborting the whole run.

#### Design decision: skip `acl2::read-file` pre-caching

The real `initialize-acl2` pre-reads pass-2 files into strings via
`acl2::read-file` before pass 2. Our initial implementation did the same,
but this triggered an SBCL memory fault:

```
CORRUPTION WARNING in SBCL pid 65712 tid 65712:
Memory fault at 0xa (pc=0x100237d9cc)
```

Since `ld-alist-raw` handles filename strings directly, we simply pass
filenames to `capture-file-ld` without pre-caching. This avoids the crash
with no functional difference for our metadata capture use case.

### 2. Output format

#### Per-file JSON (`{stem}-pass{N}.json`)

```json
{
  "source_file": "axioms.lisp",
  "stem": "axioms",
  "pass": 1,
  "position": 2,
  "elapsed_seconds": 45,
  "baseline_event_number": 0,
  "final_event_number": 1672,
  "event_count": 1593,
  "events": [
    "(DEFUN STRICT-TABLE-GUARD (X) (DECLARE (XARGS :GUARD T)) X)",
    "(DEFUN ZPF (X) (DECLARE (TYPE (UNSIGNED-BYTE 60) X)) (IF ..."
  ],
  "forms": [
    "(defun strict-table-guard (x) (declare (xargs :guard t)) x)",
    "(defun zpf (x) (declare (type (unsigned-byte 60) x)) (if ..."
  ],
  "package": "ACL2"
}
```

The `events` and `forms` arrays are parallel (same length, same order).
Events are printed with `*print-case* :upcase` and include the full
event-tuple prefix. Forms are printed with `*print-case* :downcase` and
contain the original submitted code as extracted by
`access-event-tuple-form`.

#### Manifest (`manifest.json`)

```json
{
  "acl2_files": ["serialize-raw", "axioms", "hons", ...],
  "acl2_pass_2_files": ["axioms", "memoize", "hons", ...],
  "files": [
    {
      "key": "axioms-pass1",
      "stem": "axioms",
      "pass": 1,
      "position": 2,
      "event_count": 1593,
      "baseline_event_number": 0,
      "final_event_number": 1672
    }
  ]
}
```

#### Capture results (from test run)

| Metric | Value |
|--------|-------|
| Total files captured | 46 |
| Pass 1 files | 35 |
| Pass 2 files | 11 |
| Output location | `/home/acl2/.boot-metadata/` |

### 3. Python injection (`build_notebooks.py`)

~250 lines added. Key components:

**Helper functions:**

- `_is_raw_source(stem)` — returns `True` if stem ends in `"-raw"`.
- `_ACL2_INFRA_STEMS` — frozenset of build infrastructure files
  (`acl2`, `acl2-check`, `acl2-fns`, `acl2-init`, etc.) that should be
  skipped during injection.
- `_load_boot_manifest(source_root)` — loads and parses `manifest.json`.
- `_load_boot_file_metadata(source_root, key)` — loads per-file JSON.
- `_is_acl2_source_file(source, source_root)` — checks that a `.lisp`
  file is directly under `source_root` (not in `books/` etc.).

**Core injection** (`_inject_boot_metadata_into_notebook`):

For each pass's metadata:
1. Creates a `display_data` output with MIME type
   `application/vnd.acl2.events+json`, matching the kernel's format:
   ```json
   {
     "output_type": "display_data",
     "data": {
       "application/vnd.acl2.events+json": {
         "events": ["(DEFUN FOO ...)", ...],
         "forms": ["(defun foo ...)", ...],
         "package": "ACL2",
         "source": "boot-strap-capture",
         "pass": 1,
         "stem": "axioms"
       }
     },
     "metadata": {}
   }
   ```
2. Wraps it in a code cell with provenance metadata
   (`boot_strap: true`, pass number, stem).
3. Prepends the cell to the notebook.
4. Sets notebook-level `acl2_boot_strap` metadata with source type,
   stem, and per-pass statistics.
5. Idempotent — skips if `acl2_boot_strap` metadata already present.

**Orchestrator** (`phase_inject_boot_metadata`):

1. Loads the manifest.
2. Builds a `stem → [manifest entries]` mapping.
3. Iterates every top-level `.lisp` file under `source_root`.
4. For each file: loads full per-pass metadata, calls the injection
   function on the corresponding `.ipynb`.
5. Returns `(injected, skipped, errors)` tuple.

**CLI sub-command:**

```
build-notebooks inject-boot-metadata /home/acl2 [-v] [--force] [-o OUTPUT]
```

Integrated into the existing argparse structure. Also runs as part of
`build-notebooks all`.

### 4. Makefile changes

**Venv integration** (lines 122–140):

```makefile
VENV ?= $(PWD)/.venv
VENV_PYTHON := $(VENV)/bin/python
VENV_PIP := $(VENV)/bin/pip
BUILD_NOTEBOOKS := $(VENV)/bin/build-notebooks
```

All `build-notebooks` invocations across all existing targets
(`notebooks`, `notebooks-convert`, `notebooks-execute`, etc.) were
updated to use `$(BUILD_NOTEBOOKS)` instead of bare `build-notebooks`.

The `install-script2notebook` target now installs into the venv and
depends on a `$(VENV)/bin/activate` target that creates the venv if
it doesn't exist.

**New targets** (lines 179–204):

```makefile
boot-metadata:
    cd $(ACL2_HOME) && sbcl \
        --dynamic-space-size 32000 \
        --control-stack-size 64 \
        --disable-ldb \
        --disable-debugger \
        --no-userinit \
        --load "$(CAPTURE_LOADER)"

notebooks-inject-boot-metadata: install-script2notebook
    $(BUILD_NOTEBOOKS) inject-boot-metadata $(ACL2_HOME) -v
```

### 5. Issues encountered and resolved

| # | Issue | Root Cause | Fix |
|---|-------|-----------|-----|
| 1 | SBCL debugger enters on errors | Default SBCL behavior | `sb-ext:disable-debugger` in loader + `--disable-debugger` CLI flag |
| 2 | `Package UIOP does not exist` | Bare SBCL has no ASDF/UIOP | Replaced `uiop:getenv` with `sb-ext:posix-getenv` |
| 3 | `Package ACL2 does not exist` | SBCL reads entire file before executing; `acl2::` symbols fail at read time before `init.lisp` runs | Split into loader (no `acl2::` refs) + main script (loaded after `init.lisp`) |
| 4 | Memory fault in pass-2 pre-read | `acl2::read-file` corrupts heap in this non-standard init context | Removed pre-caching; pass filenames directly to `ld-alist-raw` |
| 5 | Python not using workspace venv | `build-notebooks` invoked from system PATH | Added `VENV`/`BUILD_NOTEBOOKS` variables to Makefile; all targets use venv |

---

## Usage

### Full workflow

```bash
# 1. Capture boot-strap metadata (~5-10 min)
make boot-metadata

# 2. Convert source files to notebooks (if not already done)
make notebooks-convert

# 3. Inject metadata into notebooks
make notebooks-inject-boot-metadata
```

### Or as a single pipeline

```bash
make boot-metadata notebooks-convert notebooks-inject-boot-metadata
```

### Verify output

```bash
# Check capture output
ls /home/acl2/.boot-metadata/
python3 -c "import json; print(json.dumps(json.load(open('/home/acl2/.boot-metadata/manifest.json')), indent=2))" | head -30

# Check a per-file JSON
python3 -c "import json; d=json.load(open('/home/acl2/.boot-metadata/axioms-pass1.json')); print(f'{d[\"event_count\"]} events')"
```
