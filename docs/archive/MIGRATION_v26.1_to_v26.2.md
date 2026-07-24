# Migration guide: v26.1 → v26.2

**Target audience.** Users or downstream projects that link against
the `latex_parse` library or consume the CLI / REST surface. This guide
covers what changed, what you need to do, and what's safe to ignore.

**TL;DR.** v26.2 is additive. No existing API is removed or reshaped;
you can upgrade without touching your code. The big news is:
- A new **compile-guarantee pre-flight contract** (T0–T5 gate) via
  `Compile_contract.check_ready_to_compile`.
- A new **byte-lossless CST** via `Cst_of_ast.of_source` / `Cst.serialize`.
- A new **rewrite engine** via `Rewrite_engine.apply` /
  `Cst_edit.{insert,delete,replace}`.

None of these replace existing APIs; they sit alongside.

---

## 1. What's new

### 1.1 Project-aware runtime

| Module | Purpose |
|--------|---------|
| `Project_model` | Typed project record — files, root, engine, declared features. Built via `of_root : ?engine -> ?declared_features -> string -> (t, error) result`. |
| `Build_graph` | Artefact dependency graph (Tex/Aux/Bbl/Bib/Pdf/Log). `is_acyclic` for T2 precondition. |
| `Aux_state` | Brace-balanced pdflatex `.aux` parser. Returns labels, bibcites, bibstyle, bibdata. |
| `Compile_contract` | `check_ready_to_compile : ?aux_path -> Project_model.t -> Build_profile.t -> ready_check_result`. Returns `Ready` or `NotReady [reason; …]` with T0–T5 violation categories. |

**When to use.** Before invoking a LaTeX compiler on a project root,
call `check_ready_to_compile`. If it returns `NotReady`, don't compile —
surface the reasons to the user so they can fix them first. See
[`specs/v26/compilation_guarantee_stack.md`](../specs/v26/compilation_guarantee_stack.md)
for the full theorem stack and [`COMPILATION_GUARANTEE.md`](COMPILATION_GUARANTEE.md)
for user-facing framing.

### 1.2 CST + rewrite engine

| Module | Purpose |
|--------|---------|
| `Stable_spans` | Byte-range spans with shift-on-edit semantics (`shift_after`, `damaged_by`). |
| `Cst` | Lossless CST variants; `serialize : t list -> string`. |
| `Cst_of_ast` | AST → CST builder; `of_source : string -> Cst.t list`. |
| `Cst_edit` | Edit algebra (insert / delete / replace) with conflict detection. |
| `Rewrite_engine` | `apply` + `apply_and_reparse`. |

**Byte-lossless guarantee.** `Cst.serialize (Cst_of_ast.of_source src) = src`
for arbitrary `src`. See [`docs/CST_ROUNDTRIP_SCOPE.md`](CST_ROUNDTRIP_SCOPE.md).

### 1.3 Proofs added

| File | Status |
|------|--------|
| `proofs/ProjectClosure.v` | T2 proof (mechanized) |
| `proofs/BuildProfileSound.v` | T3 proof (mechanized) |
| `proofs/CompileProgress.v` | T6 (hypothesis-parametric; v27 WS8 discharge) |
| `proofs/CompileWellFormed.v` | T7 (hypothesis-parametric; v27 WS8 discharge) |
| `proofs/T{0,1,4,5}_wrapper.v` | thin wrappers over existing proofs |
| `proofs/CSTRoundTrip.v` | byte-lossless serialization |
| `proofs/RewritePreservesCST.v` | rewrite preserves partition |
| `proofs/RewritePreservesSemantics.v` | ws-edit preserves tokens |

All zero-admit, zero-axiom. See `proofs/ADMISSIBILITY_MAP.md` for the
v27 discharge checklist.

---

## 2. What's changed (breaking-ish)

**None of the v26.1 public API has been removed or reshaped.**
The one intentional change to an existing type:

### 2.1 `Parser_l2.loc` gains `end_offset : int`

- **What.** `loc = { line; col; offset; end_offset }` now has a fourth field.
- **Why.** CST builder needs the end of each node's byte range.
- **Impact.** Any code that constructs `Parser_l2.loc` with a record literal
  `{ line; col; offset }` now fails to type-check. Fix: add `; end_offset`.
  For zero-length markers, use `end_offset = offset`.
- **Migration.** Search your code for `{ line = _; col = _; offset = _` record
  literals (or `Parser_l2.line = _; …`); add `end_offset` to each.

**Everything else is additive.**

---

## 3. Deprecations

None in v26.2. Continue using v26.1 APIs as-is.

---

## 4. What you can ignore

- `core/l2_parser/{cst,cst_edit,rewrite_engine,stable_spans}` — these
  are memo-alias re-exports of the canonical modules under
  `latex-parse/src/`. They exist so memo-referenced paths resolve, but
  you should continue importing from the canonical paths.
- Hypothesis-parametric proofs (T6, T7, `RewritePreservesCST`,
  `RewritePreservesSemantics`, `CSTRoundTrip` structure-lossless
  section). These are discharged in v27 WS8 against concrete toolchain
  models; v26.2 users see them as compile-time scaffolding only.

---

## 5. Known gaps

- **Per-rule `fix` suggestions** are not yet in `Validators.result`. The
  rewrite engine is in place; the validator integration ships in a
  follow-up PR (v26.2.1 or v26.3). Track progress on that work via
  GitHub issues labelled `rewrite-integration`.
- **L3 AST-derived rules** remain source-regex-derived (memo §15.5);
  migration to AST + project semantics is v27 scope per
  [`docs/L3_ROADMAP.md`](L3_ROADMAP.md).

---

## 6. Upgrade checklist

1. Bump your `latex_parse` dep to `26.2.0`.
2. If you construct `Parser_l2.loc` directly, add `end_offset` to every
   record literal. Existing `end_offset = offset` is fine for every
   site that doesn't know the exact end.
3. Rebuild; fix any type errors (there should only be the `loc` ones).
4. Optionally: call `Compile_contract.check_ready_to_compile` before
   compile; build the CST via `Cst_of_ast.of_source` and use
   `Rewrite_engine.apply` for source transformations.
5. If you ship your own proofs in the same `LaTeXPerfectionist` theory,
   add the new files to your `_CoqProject` (copy the v26.2 section).

---

## 7. Reporting issues

File issues at https://github.com/ClanClanClanClan/latex_perf/issues
with `[v26.2]` in the title. Reference this migration guide and the
specific section that wasn't clear.
