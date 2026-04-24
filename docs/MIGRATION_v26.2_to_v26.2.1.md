# Migrating from v26.2.0 to v26.2.1

v26.2.1 is an additive patch release that closes the fix-producer
track. The only consumer-visible change is the new
`Validators_common.result.fix` field; downstream code that
constructed `result` values directly as record literals must migrate
to the new helpers. Everything else is backward-compatible.

## What changed

### `result` record gained a `fix` field

```ocaml
type result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
  fix : Cst_edit.t list option;   (* NEW in v26.2.1 *)
}
```

Raw record literals `{ id = ...; severity = ...; message = ...;
count = ... }` no longer typecheck — the compiler requires the new
field. Two new constructors cover every case:

```ocaml
val mk_result :
  id:string -> severity:severity -> message:string -> count:int -> result
(** Sets [fix = None]. *)

val mk_result_with_fix :
  id:string -> severity:severity -> message:string -> count:int ->
  fix:Cst_edit.t list -> result
(** Sets [fix = Some fix]. Raises [Invalid_argument] on empty list
    — use [mk_result] for the no-fix case. *)
```

### Type deviation from v26.2.0 CHANGELOG

The v26.2.0 CHANGELOG announced the field as `Cst_edit.t option`
(singular). The shipped type is `Cst_edit.t list option`. This was
corrected in v26.2.1 because TYPO-002/003 aggregate `count` per
document and need one edit per match — a single-edit shape could
not represent that. No v26.2.0 release exposed the field, so the
change is purely a plan/CHANGELOG correction.

### New CLI mode: `--apply-fixes`

```
validators_cli --apply-fixes <file.tex>
# or
L0_APPLY_FIXES=1 validators_cli <file.tex>
```

Runs validators, flattens every `r.fix = Some edits`, applies the
combined edit set via `Cst_edit.apply_all`, and emits the modified
source to stdout. On overlapping fixes (not expected in practice;
rule conflict resolution prevents most cases), emits
`E.apply-fixes.overlap` to stderr and exits 2 without touching
stdout.

Decision per `specs/v26/V26_2_PLAN.md` §3.2 B3: all-or-nothing only.
`--apply-fixes-for RULE-ID` remains v26.3 scope.

### Rules that produce fixes

v26.2.1 ships three exemplar producers. Every other rule continues
to emit `fix = None` via `mk_result`.

| Rule | Fix |
|---|---|
| STRUCT-001 | Insert `\documentclass{article}\n` at offset 0. |
| TYPO-002 | For each non-overlapping `--`, replace with `–` (en-dash). |
| TYPO-003 | For each non-overlapping `---`, replace with `—` (em-dash). |

## Mechanical migration recipe

If your code built `Validators_common.result` values as record
literals:

```diff
-Some {
-  id = "X-001";
-  severity = Warning;
-  message = "...";
-  count = 1;
-}
+Some
+  (Validators_common.mk_result
+     ~id:"X-001" ~severity:Warning ~message:"..." ~count:1)
```

Record **patterns** that destructured the result by field need a
wildcard to absorb the new field:

```diff
-let { id; severity; message; count } = r in
+let { id; severity; message; count; _ } = r in
```

Emitting a fix:

```ocaml
let fix = [ Cst_edit.replace ~start_offset:s ~end_offset:e "…" ] in
Validators_common.mk_result_with_fix
  ~id:"X-042" ~severity:Warning ~message:"…" ~count:1 ~fix
```

The `scripts/tools/migrate_result_literals.py` one-shot script used
by the repo for its own migration is available for reference; it
handles OCaml strings, character literals, quoted strings
(`{|...|}`), comments, and qualified field names.

## New gate

`scripts/tools/check_result_helpers.py` is wired into
`pre_release_check.py` as gate #15. It rejects any raw four-field
`result` record literal in `validators_*.ml` or test files. Use the
helpers instead; if a new required field lands in a future release,
only the helpers need updating.

## Upstream references

- `specs/v26/V26_2_1_PLAN.md` — PR slate + design decisions.
- `docs/v26_2/FIX_STYLE_GUIDE.md` — author-facing style guide for
  new fix producers (refreshed in v26.2.1).
- `CHANGELOG.md` — `[v26.2.1]` entry with the five PR references.
