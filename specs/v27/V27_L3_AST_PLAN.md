# V27_L3_AST_PLAN — L3 AST migration (revised stage decomposition)

> ⚠ **NOT CURRENT — historical plan (banner added 2026-09-30; the text below is unchanged).**
> None of the 9 stage boxes below is checked, and this plan is not among the
> current priorities (proven tier: [ADR-015](../../docs/v27/adr/ADR-015-static-proven-tier-on-translated-engine.md);
> measured position and open work: [PROJECT_STATE.md](../../docs/v27/PROJECT_STATE.md)).
> Part of the L3-AST work shipped under Tier 2 (v27.1.28/36, `ast_semantic_state`);
> treat this file as a record of intent, not of status.


**Goal:** Migrate the L3 semantic layer from its current
source-regex-derived form to a true AST/project-semantics-derived
representation, per `docs/L3_ROADMAP.md` and memo §15.5.

**Tag target:** v27.2.0 capstone.

**Scope estimate:** 10–14 sessions across 3–4 months.

## Why migrate

Memo §15.5 documents the current L3 honestly: parts of L3 fall back
to regex patterns over the source rather than reading the project's
AST. This works for many lint rules but blocks:
- Rules that need cross-file label/ref resolution.
- Rules that need counter-state knowledge.
- Rules that depend on macro expansion shape.

The migration goal: every L3 rule that currently uses
`source_regex_finder` switches to a path that consumes the project's
AST + semantic state.

## Stage decomposition

### Stage 1 — `ast_semantic_state.ml` skeleton
**Branch:** `v27.2/L3-stage1-skeleton`

Define the new module:

```ocaml
(* latex-parse/src/ast_semantic_state.ml *)
type t = {
  ast : Cst_ast.t;
  labels : (string, file_id) Hashtbl.t;
  refs : (string, file_id list) Hashtbl.t;
  counter_state : (string, int) Hashtbl.t;
  (* further fields as L3 rules require *)
}

val of_project : Project_state.t -> t
val resolve_label : t -> string -> file_id option
val labels_in_scope : t -> string list
```

Wire into the existing `Project_state.t` pipeline.

**Acceptance:** `dune build` green; the new module compiles; one
unit test passes (label resolution on a 2-file fixture).

### Stage 2 — Inventory current L3 rules
**Branch:** `v27.2/L3-stage2-inventory`

Audit `latex-parse/src/rules/L3/` (or wherever L3 rules live).
Produce `specs/v27/L3_MIGRATION_INVENTORY.md` listing each L3 rule
with its current source-regex pattern and the AST-equivalent shape
it should target.

Bucket rules:
- **Easy** — mechanical replacement of regex with AST traversal.
- **Hard** — requires new semantic state (counters, bibs).
- **Defer** — currently regex but no AST equivalent (rare).

**Acceptance:** inventory file exists; ~80% of rules in "Easy"
bucket.

### Stage 3 — Migrate easy bucket (batch 1)
**Branch:** `v27.2/L3-stage3-batch1`

Migrate ~10 easy-bucket rules from regex to AST. Per rule:
1. Replace `source_regex_finder.find` with `ast_semantic_state`
   query.
2. Keep the rule's runtime behavior identical (golden tests pass).
3. Update `rule_contracts.yaml` to reflect the new path.

**Acceptance:** ~10 rules migrated; all golden tests pass; 0 diffs
on differential test.

### Stage 4 — Migrate easy bucket (batch 2)
**Branch:** `v27.2/L3-stage4-batch2`

Continue ~10 more rules.

### Stage 5 — Counter-state semantic engine
**Branch:** `v27.2/L3-stage5-counter-state`

Define `counter_state.ml` for counters (section, equation, figure,
table, etc.). Connect to `\setcounter` / `\stepcounter` / etc. in
the AST. Hard-bucket rules now have the semantic state they need.

**Acceptance:** `Counter_state.t` defined; counter-dependent rules
pass.

### Stage 6 — Bibliography resolution
**Branch:** `v27.2/L3-stage6-bib`

Define `bib_state.ml` for bibtex / biber entries. Connect
`\cite{key}` to entry resolution. Bibliography-dependent rules
pass.

### Stage 7 — Migrate hard bucket
**Branch:** `v27.2/L3-stage7-hard-bucket`

Migrate the hard-bucket rules using the new counter / bib state.

### Stage 8 — Parity gate
**Branch:** `v27.2/L3-stage8-parity-gate`

Add a CI gate: for each L3 rule, run both the old-path (regex) and
new-path (AST) on the corpus; assert outputs match. Strict parity
prevents regression during migration. Once all rules migrate,
delete the old-path code.

**Acceptance:** parity gate green; old `source_regex_finder` paths
deleted.

### Stage 9 — Coq updates
**Branch:** `v27.2/L3-stage9-coq`

Update `proofs/L3/` (if any) to reflect the AST-based semantics.
Re-prove rule soundness against the new shape.

### Stage 10 — Release-bump v27.2.0
**Branch:** `v27.2/release-bump`

Bump version, CHANGELOG `[v27.2.0]` entry. Tag.

## Multi-session memory protocol

`~/.claude/.../memory/v27_L3_status.md` tracks per-stage state.

## Acceptance criteria

- [ ] `ast_semantic_state.ml` defined and used by every L3 rule.
- [ ] `source_regex_finder` paths deleted (after parity gate
  green).
- [ ] All L3 rules pass golden tests through the AST path.
- [ ] Counter and bibliography state subsystems defined.
- [ ] L3 Coq proofs updated (if applicable).
- [ ] Memo §15.5 marked resolved in `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md`.
- [ ] `docs/L3_ROADMAP.md` updated to "MIGRATED" status.
- [ ] CHANGELOG `[v27.2.0]` entry.
- [ ] Tag v27.2.0 on main.
