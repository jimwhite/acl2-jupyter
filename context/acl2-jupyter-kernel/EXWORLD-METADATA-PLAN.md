## Plan: Non-World Metadata Capture for ACL2 Jupyter Kernel

> **Status**: Core features implemented on branch `exworld-metadata`.
> Phase 4 below is the current work item.

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
