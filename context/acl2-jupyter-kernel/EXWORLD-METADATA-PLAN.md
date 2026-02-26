## Plan: Non-World Metadata Capture for ACL2 Jupyter Kernel

> **Status**: Phases 1–4a DONE.  Phase 5 (community books, trust tags,
> deep events, stdout) in progress.

**TL;DR** — Extend the kernel's per-cell metadata beyond world event landmarks to include: (1) all symbols referenced in the cell with their resolved packages and kinds, (2) dependency edges from defined symbols to referenced symbols, (3) macro expansion of ACL2 forms via `translate1`, and (4) detection of genuinely unexpected CL-level side effects. The metadata flows through the existing `display_data` / `application/vnd.acl2.events+json` MIME channel, gated behind the `:exworld` kernel option (`ACL2_JUPYTER_EXWORLD=1`).

---

### Phase 1 — Core exworld metadata (DONE)

Implemented symbols.lisp, kernel.lisp integration, .asd registration, feature gating, test segregation. All 12 exworld + 11 base tests passing. Renderer rewritten with sections for Forms, Symbols, Deps, Expand, Raw.

### Phase 2 — Renderer polish (DONE)

Ref badge color fix (badge-background/badge-foreground), symbols table column reorder (Package/Name/Kind/Pos with explicit widths).

### Phase 3 — Fix unknown kinds, filter raw_definitions (DONE)

- 3a. Post-eval re-classification of "unknown" symbols via `reclassify-unknown-symbols`
- 3b. Typed dependency references — implemented then reverted; deps use plain strings
- 3c. Filter raw_definitions to subtract ACL2-defined names (expected fboundp)
- 3d. Arglist formals not marked as operators — `defun-like-p` + `walk-flat`

### Phase 4 — Source-based dependency extraction (DONE)

**Problem**: The previous `build-dependency-edges` pipeline used a hardcoded list of ~15 event types in `extract-defined-names` and queried world properties for symbol bodies via `get-symbol-body`. This failed for constants (world stores computed value, not source expression) and couldn't handle the hundreds of definition forms ACL2 supports (including user-defined ones).

**Solution**: Pre/post classification diff using source forms.

1. **Before eval**: snapshot `classify-symbol-safe` for every symbol extracted from source forms (first-sighting-only dedup for multi-form cells)
2. **After eval**: diff to find symbols that went `:unknown` → known kind — these are the symbols *defined* by the cell
3. **Walk source forms**: for each newly-defined symbol, find which stashed source s-expression mentions it, walk that form to extract references

#### Implementation

- **`cell-kind-snapshot` slot** (kernel.lisp): alist of `(sym . kind-keyword)`, reset per cell. Only the first sighting of each symbol is recorded so multi-form cells preserve pre-definition kinds.
- **`accumulate-form-symbols`** (kernel.lisp): after `extract-symbols`, captures pre-eval kinds into `cell-kind-snapshot` with first-sighting dedup (`unless (assoc sym ...)`).
- **`extract-newly-defined`** (symbols.lisp): returns symbols where pre-eval kind was `:unknown` but post-eval is no longer `:unknown`. Replaces `extract-defined-names` for both dependency extraction and raw_definitions filtering.
- **`build-source-dependencies`** (symbols.lisp): uses `extract-newly-defined` + source form walking. For each newly-defined symbol, finds its source form, walks it for references (excluding self), emits edges as `"pkg::name"` strings.
- **`collect-cell-events`** (kernel.lisp): calls `build-source-dependencies` instead of old `build-dependency-edges`; calls `extract-newly-defined` instead of old `extract-defined-names` for raw_defs filtering.

#### Deleted code

- `extract-defined-names` — hardcoded event type list, replaced by `extract-newly-defined`
- `get-symbol-body` — world property query, replaced by source form walking
- `extract-body-references` — used `get-symbol-body`, replaced by direct `extract-symbols` on source forms
- `build-dependency-edges` — replaced by `build-source-dependencies`

#### Edge cases

- **Multiple top-level forms**: each is a separate `cell-source-forms` entry; form-matching correctly attributes references per symbol.
- **Compound forms** (`mutual-recursion`, `defconsts`, `encapsulate`): all newly-defined symbols map to the same source form. Each gets the full set of references from that form minus itself. Over-broad edges accepted (simpler, still useful).
- **Snapshot deduplication**: first-sighting-only prevents multi-form cells from overwriting pre-definition kinds.

#### Decisions

- Pre/post classify diff over hardcoded event type list — universal, works for any definition form
- Source form walking over world property query — preserves original expressions
- Over-broad edges accepted for compound forms
- Output format unchanged — `{"defined-name": ["ref1", "ref2", ...]}`
- `extract-newly-defined` serves dual purpose (deps + raw_defs filtering)

### Phase 4a — Bootstrap pass-2 re-definition detection (DONE)

**Problem**: In `--pass2-only` bootstrap mode, pass 1 runs internally via `ld-fn` before the REPL starts. By the time pass 2 executes notebook cells, all symbols are already defined. The kind-snapshot diff (`extract-newly-defined`) sees `:function` → `:function` and finds no transitions, producing empty dependency sets for pass-2 notebooks.

**Solution**: Augment `extract-newly-defined` (kind diff) with `extract-event-defined-names` (event tuple extraction). Pass-2 forms still create event landmarks in the world (even though they're redundant re-definitions), so the event tuples from the world diff provide a reliable signal for what each cell defined.

#### Implementation

- **`extract-event-defined-names`** (symbols.lisp): iterates event tuples, strips LOCAL wrapper and event number, extracts the symbol name from `(cadr summary)` position. No hardcoded event type list — any symbol in the name position is included (filtered by `interesting-symbol-p`). Uses `pushnew` for dedup.
- **`build-source-dependencies`** (symbols.lisp): new optional `event-tuples` parameter. Computes `newly-defined` as the `union` of `extract-newly-defined` (kind diff, catches fresh definitions) and `extract-event-defined-names` (event tuples, catches re-definitions in bootstrap pass 2).
- **`collect-cell-events`** (kernel.lisp): passes `tuples` as 4th arg to `build-source-dependencies`. Guard changed from `(cell-kind-snapshot k)` to `(or (cell-kind-snapshot k) tuples)` so deps are computed even when no kind snapshot exists. Raw-defs filter likewise uses the union approach.

#### Key insight

Both signals are always available and complementary. In normal kernel mode, `extract-newly-defined` catches everything (symbols go unknown → known). In bootstrap pass 2, `extract-event-defined-names` catches re-definitions. The union is always safe — it can only add more defined names, never remove them.

---

### Phase 5 — Community Books, Trust Tags, Deep Events, Stdout

Four features extending the metadata infrastructure beyond bootstrap notebooks.
Implementation order: 5d → 5b → 5c → 5a.

### Phase 5d — Stdout line-buffered flushing (DONE)

**Problem**: The upstream `common-lisp-jupyter` `iopub-write-char` appends characters to a buffer but never flushes on newline. Output only appears after cell completion via `stream-finish-output` in the `evaluate-code :after` method. Long-running cells show no incremental output.

**Approach**: Kernel-layer wrapper — no modifications to the upstream fork.

#### Implementation

- **`stream-force-output` method** (kernel.lisp): defined on `jupyter::iopub-stream`, delegates to `iopub-finish-output`. Gives us a force-output entry point on the upstream class.
- **`line-buffered-stream` class** (kernel.lisp): Gray stream wrapper. `stream-write-char` delegates to the inner stream and calls `force-output` after every `#\Newline`. Also delegates `stream-finish-output`, `stream-force-output`, `stream-line-column`.
- **`make-line-buffered-stream`** (kernel.lisp): constructor.
- **`in-main-thread` updated**: `*standard-output*`, `*error-output*`, and `*trace-output*` now wrap their synonym streams through `make-line-buffered-stream`.

### Phase 5b — Trust tag tracking (DONE)

**Problem**: Trust tags (`defttag`) bypass ACL2's soundness guarantees. No per-cell metadata records which trust tags a cell introduces.

**Mechanism**: `ttags-seen` is a world global (alist: ttag keyword → list of book names). Updated by `chk-acceptable-ttag1` in history-management.lisp when `defttag` is processed. Propagated through `include-book`, `encapsulate`, `make-event` (used by `progn!` / `include-raw`).

#### Implementation

- **`cell-ttags-before` slot** (kernel.lisp): alist snapshot of `(global-val 'ttags-seen wrld)` taken before eval.
- **`cell-trust-tags` slot** (kernel.lisp): vector of JSON-ready trust-tag entries.
- **`diff-ttags-seen`** (symbols.lisp): compares before/after alists, returns new or extended ttag entries formatted as `[{"tag": ":foo", "books": ["bar"]}]`.
- **`evaluate-code` reset**: clears both new slots per cell.
- **`eval-cell`**: snapshots ttags-seen before dispatching to REPL loop.
- **`collect-cell-events`**: diffs post-eval ttags-seen against snapshot.
- **`send-cell-metadata`**: emits `trust_tags` key (gated on `exworld-p`).

### Phase 5c — Deep events flag rework (DONE)

**Problem**: `deep-events-p` controlled both internal processing (deps, raw-defs) and output serialization. Enrichment needs deep events for dependency analysis even when users want shallow output.

#### Implementation

- **`collect-cell-events`**: calls `extract-event-tuples` with `t` (deep) to get `all-tuples` for internal work. Separately derives `output-tuples` using `(deep-events-p k)` for serialization.
- **Internal consumers** (`build-source-dependencies`, `extract-event-defined-names`, raw-defs pipeline) use `all-tuples`.
- **Output functions** (`format-event-tuples`, `format-event-forms`) use `output-tuples`.
- No new env var — `ACL2_JUPYTER_DEEP_EVENTS` controls only what the user sees.

### Phase 5a — Community book raw CL dependencies (DONE — kernel side)

**Problem**: Community books use `(include-raw "foo-raw.lsp")` to load raw Common Lisp code. This creates no event landmark — only a `value-triple :invisible` event. The `.lsp` filename must be extracted from source forms.

#### Kernel-side implementation

- **`extract-include-raw-files`** (symbols.lisp): walks source forms looking for `(include-raw "filename" ...)`. Handles `progn`, `progn!`, `encapsulate`, `with-output`, `local` wrappers. Returns list of filename strings.
- **`cell-raw-includes` slot** (kernel.lisp): vector of filename strings, reset per cell.
- **`accumulate-form-symbols`** (kernel.lisp): calls `extract-include-raw-files` on each source form and accumulates into slot.
- **`send-cell-metadata`** (kernel.lisp): emits `raw_includes` key (gated on `exworld-p`).

#### Python-side (.lsp enrichment — NOT YET IMPLEMENTED)

After Phase 2 execute in `build_notebooks.py`:
1. Scan executed notebooks for cells with `raw_includes` in metadata.
2. Group `.lsp` files by parent book.
3. For each group: start a fresh kernel, `include-book` the parent book, then send each `.lsp` cell via `:analyze-source-cl`.
4. Write per-cell display_data to the `.lsp` notebook, fix language tag.

### Decisions

| Decision | Choice |
|----------|--------|
| Stdout approach | Kernel-layer wrapper (Gray stream), not upstream fork modification |
| `.lsp` enrichment world state | Fresh kernel per parent book (`include-book` for accurate classification) |
| Implementation order | 5d → 5b → 5c → 5a |
| Deep events split | Collect-once / filter-for-output, no new env var |
| Trust tags | Pre/post diff of `ttags-seen` world global |
| Include-raw detection | Kernel-level source form walking with wrapper recursion |