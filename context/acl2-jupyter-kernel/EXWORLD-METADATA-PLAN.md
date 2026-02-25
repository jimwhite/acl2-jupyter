## Plan: Non-World Metadata Capture for ACL2 Jupyter Kernel

**TL;DR** — Extend the kernel's per-cell metadata beyond world event landmarks to include: (1) all symbols referenced in the cell with their resolved packages and kinds, (2) dependency edges from defined symbols to referenced symbols, (3) macro expansion of ACL2 forms via `translate1`, and (4) detection of raw CL-level side effects (new `fboundp`/`boundp` bindings not covered by world events). The metadata flows through the existing `display_data` / `application/vnd.acl2.events+json` MIME channel.

**Steps**

1. **Add a symbol extraction utility** in a new file context/acl2-jupyter-kernel/symbols.lisp. Implement `extract-symbols` — a recursive walker over read s-expressions that collects every symbol into a hash table (deduped). After `read-object` returns a form but before `trans-eval`, walk the form. For each symbol, record:
   - `symbol-name`, `symbol-package` (the package it resolved in during read)
   - Position: operator vs argument (is it `(car ...)` of a cons = function position?)
   - This captures the reader's *actual* symbol resolution — no separate parser needed since forms are already live Lisp objects with packages resolved.

2. **Classify referenced symbols against the ACL2 world** (also in symbols.lisp). For each extracted symbol, query the world (before eval) via `getpropc`:
   - `'acl2::formals` → function
   - `'acl2::macro-args` → macro
   - `'acl2::theorem` → theorem
   - `'acl2::const` → constant
   - `'acl2::stobj` → stobj
   - `boundp` / `fboundp` at CL level → raw Lisp binding
   - None of the above → unknown/forward-reference

3. **Capture macro expansions** in kernel.lisp. Between `read-object` and `trans-eval`, call ACL2's `translate1` on the form:
   ```
   (translate1 form :stobjs-out '((:stobjs-out . :stobjs-out)) t ctx wrld state)
   ```
   This returns `(mv erp translated-term bindings state)`. The `translated-term` is the fully macro-expanded, translated ACL2 term. Compare surface symbols in the original form vs the translated term to identify which macros expanded and what they expanded into. Wrap in `ignore-errors` — translation can fail for event forms like `defun` (which aren't expressions); for those, fall back to extracting the body and translating just that.

4. **Detect raw CL-level side effects** in kernel.lisp. Before `trans-eval`, snapshot a set of "interesting" CL-level bindings:
   - `fboundp` status for symbols in the cell's form (from step 1)
   - `boundp` status for the same symbols
   - Optionally: count of symbols in `ACL2_*1*_ACL2` package (detects new *1* compiled functions)
   
   After `trans-eval`, re-check these. Any newly `fboundp`/`boundp` symbol not accounted for by world event landmarks is a raw CL-level definition. Report these separately.

5. **Build dependency edges** in symbols.lisp. After eval, for each symbol *newly defined* by this cell (detected via world diff in `collect-cell-events`):
   - Retrieve its `'unnormalized-body` from the post-eval world via `(getpropc sym 'acl2::unnormalized-body nil post-wrld)`
   - Walk the body to extract all referenced symbols (reusing `extract-symbols`)
   - For macros: walk the `'macro-body` property
   - For theorems: walk the `'theorem` property (the theorem body is stored as a translated term)
   - Each `(defined-symbol . referenced-symbols-list)` pair is a dependency edge

6. **Extend `send-cell-metadata`** in kernel.lisp (around kernel.lisp). Add new keys to the `application/vnd.acl2.events+json` payload:

   | Key | Type | Description |
   |-----|------|-------------|
   | `symbols` | array of objects | Each: `{name, package, kind, defined}` |
   | `dependencies` | object | `{defined_sym: [referenced_sym, ...], ...}` |
   | `expansions` | array of objects | Each: `{form, expansion}` (macro-expanded forms) |
   | `raw_definitions` | array of strings | CL-level `fboundp`/`boundp` changes not in world events |

7. **Register the new file** in acl2-jupyter-kernel.asd — add `"symbols"` to the `:components` list.

8. **Accumulate across forms in a cell** — the read-eval-print loop in `jupyter-read-eval-print-loop` processes multiple forms per cell. Add per-cell accumulator slots to the `kernel` class (e.g., `cell-symbols`, `cell-dependencies`, `cell-expansions`, `cell-raw-defs`) that get reset at the start of `eval-cell` and populated incrementally by each form in the loop.

**Verification**

- Test with a cell containing `(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))` — should report `app` as defined (function), and `consp`, `cons`, `car`, `cdr`, `if` as referenced, with dependency edge `app → {consp, cons, car, cdr, app}` (self-recursive).
- Test with `(defmacro my-mac (x) ...)` followed by `(my-mac foo)` in a later cell — the second cell should show `my-mac` as a referenced macro, and `expansions` should show what `(my-mac foo)` expanded to.
- Test with a `:pe` keyword command — should resolve symbols referenced in the expansion `(ACL2::PE 'sym)`.
- Run the existing `test_kernel.py` and `test_kernel_eval.lisp` tests to ensure no regressions.

**Decisions**

- **S-expression walking over pre-parsing**: Since `read-object` already resolves symbols into live Lisp objects with correct packages, walking the resulting form is simpler and more accurate than running a separate parser (tree-sitter/Eclector). Tree-sitter doesn't know package state; Eclector would need to replicate ACL2's readtable. The read form IS the ground truth.
- **`translate1` for macro expansion**: ACL2 macros are expanded by `translate`, not CL's `macroexpand` — so `*macroexpand-hook*` is useless for ACL2 macros. Calling `translate1` directly is the correct approach, matching how `trans-eval0` uses it internally.
- **Dependency from world properties, not from source**: Extracting dependencies from `'unnormalized-body` / `'theorem` in the post-eval world is more reliable than trying to parse the source form, because the world stores the actual processed body after macro expansion and normalization.
- **Same MIME channel**: Extending the existing vendor MIME type keeps the transport unified and ensures metadata persists in `.ipynb` files for downstream tools.
