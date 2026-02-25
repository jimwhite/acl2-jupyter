## Plan: Non-World Metadata Capture for ACL2 Jupyter Kernel

> **Status**: Core features implemented on branch `exworld-metadata`.
> Phase 3 below is the current work item.

**TL;DR** — Extend the kernel's per-cell metadata beyond world event landmarks to include: (1) all symbols referenced in the cell with their resolved packages and kinds, (2) dependency edges from defined symbols to referenced symbols with typed refs, (3) macro expansion of ACL2 forms via `translate1`, and (4) detection of genuinely unexpected CL-level side effects. The metadata flows through the existing `display_data` / `application/vnd.acl2.events+json` MIME channel, gated behind the `:exworld` kernel option (`ACL2_JUPYTER_EXWORLD=1`).

---

### Phase 1 — Core exworld metadata (DONE)

Implemented symbols.lisp, kernel.lisp integration, .asd registration, feature gating, test segregation. All 12 exworld + 11 base tests passing. Renderer rewritten with sections for Forms, Symbols, Deps, Expand, Raw.

### Phase 2 — Renderer polish (DONE)

Ref badge color fix (badge-background/badge-foreground), symbols table column reorder (Package/Name/Kind/Pos with explicit widths).

### Phase 3 — Fix unknown kinds, typed dep refs, filter raw_definitions (CURRENT)

Three bugs/improvements discovered during hanoi.ipynb testing:

#### 3a. Post-eval re-classification of "unknown" symbols

**Problem**: `accumulate-form-symbols` calls `classify-symbol` via `symbols-table-to-json` BEFORE `trans-eval`. Symbols being defined by the cell (e.g. `foo` in `(defun foo ...)`) don't yet have world properties, so they get `kind: "unknown"`.

**Fix**: In `collect-cell-events` (kernel.lisp ~L576), after the world is updated, iterate over `cell-symbols` entries. For any with `kind == "unknown"`, re-query the post-eval world via `classify-symbol-safe` and update the entry in place.

- File: kernel.lisp `collect-cell-events`, after `(setf (world-baseline k) post-wrld)`
- Loop over `(cell-symbols k)`, parse each entry's `kind` field, re-classify if `"unknown"`
- Need helper in symbols.lisp: `reclassify-unknown-symbols(symbols-vector wrld)` that mutates the vector entries

#### 3b. Typed dependency references

**Problem**: Dependency refs are plain strings like `"COMMON-LISP::consp"`. User wants to see what kind each referenced symbol is.

**Fix** (already partially applied to symbols.lisp): `extract-body-references` now returns objects `{"name": "pkg::sym", "kind": "function"}` instead of strings. `build-dependency-edges` passes them through.

- File: symbols.lisp `extract-body-references` — DONE, returns `(:object-alist ("name" . n) ("kind" . k))`
- File: renderer/index.js `buildDependenciesSection` (~L205) — update to read `ref.name` and `ref.kind`, render kind-colored badge (reuse `KIND_COLORS` map) next to the ref name. Handle backward compat: if `ref` is a string (old format), treat as before.
- File: test_exworld_metadata.py — update `TestDependencies` assertions: `ref_names = [r["name"].lower() if isinstance(r, dict) else r.lower() for r in refs]`

#### 3c. Filter raw_definitions to only unexpected side effects

**Problem**: `raw_definitions` currently reports every symbol that gained `fboundp`/`boundp` after eval. But ACL2 `defun` always installs a CL-level `fboundp` — that's expected, not a "raw CL side effect". The feature reports noise.

**Fix**: In `collect-cell-events` (~L600), after building dependency edges (which calls `extract-defined-names`), pass the set of ACL2-defined names to the raw-change detection. Subtract them so only genuinely unexpected CL bindings appear.

- File: kernel.lisp `collect-cell-events` — get `defined-names` from `extract-defined-names(tuples)`, pass to a new function or filter inline
- File: symbols.lisp — add `filter-expected-definitions(changes defined-names)` or modify `detect-raw-changes` to accept an exclusion set
- The key: format defined names as `"pkg::name"` strings (same format as changes) and subtract

**Steps**

1. **symbols.lisp**: Add `reclassify-unknown-symbols` — takes the symbols vector and post-eval wrld, updates `"kind"` fields in place for any `"unknown"` entries
2. **kernel.lisp `collect-cell-events`**: Call `reclassify-unknown-symbols` on `(cell-symbols k)` with `post-wrld` after setting `world-baseline`
3. **kernel.lisp `collect-cell-events`**: Extract `defined-names` from `extract-defined-names(tuples)`, format as `"pkg::name"` strings, subtract from raw-changes result before storing in `cell-raw-defs`
4. **renderer/index.js `buildDependenciesSection`**: Read `ref.name`/`ref.kind` from each dep ref object; render `ref.name` text with a kind-colored badge from `KIND_COLORS[ref.kind]`; handle backward compat for plain string refs
5. **test_exworld_metadata.py**: Update `TestDependencies` assertions to handle `{name, kind}` objects; optionally add a test verifying defined symbols get correct kind post-eval
6. **Reinstall kernel**: Clear FASL cache, run `install-kernelspec.sh`
7. **Verify**: Run `pytest test_exworld_metadata.py`, execute hanoi.ipynb cells, confirm kinds are correct, dep refs show kinds, raw_definitions is empty for normal ACL2 defuns

**Verification**

- `pytest test_exworld_metadata.py -v --timeout=180` — all tests pass
- Execute `(defun mem (e x) ...)` in hanoi.ipynb — Symbols section shows `mem` as `kind: function` (not `unknown`)
- Dependencies show typed refs: `consp` with function badge, `equal` with function badge, etc.
- `raw_definitions` is absent/empty for normal ACL2 defun cells (no false positives)
- `pytest test_metadata.py -v --timeout=180` — base tests still pass (backward compat)

**Decisions**

- Re-classify post-eval (approach A) chosen over form-based inference — more accurate, catches all world properties including theorems/constants/stobjs
- raw_definitions: filter out ACL2-defined names rather than removing the feature (preserves detection of genuine CL side effects like `defparameter` in progn)
- Dependency ref format: `{name, kind}` objects with backward-compat string handling in renderer
- Same MIME channel, same feature gate (`ACL2_JUPYTER_EXWORLD=1`)
