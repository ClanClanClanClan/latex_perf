# ADR-008: CST generation via post-process AST + source slicing

- **Status:** Provisional — pending PR B0.5 audit
- **Context owner:** v26.2 architectural decisions (plan §2.8)

## Context

To produce a lossless CST, we need a strategy that:
1. Doesn't duplicate parsing work (Parser_l2 already exists + is proven).
2. Preserves source-byte information (whitespace, comments, exact positions).
3. Can be implemented in ~3 engineering days (PR B1 budget).

## Decision

**Post-process existing `Parser_l2` output + source slicing.**

Algorithm:
1. Parse source with existing `Parser_l2` → list of `located_node` with
   offsets.
2. Traverse the AST; for each node, slice the source string at the
   recorded offsets to produce a typed CST node.
3. Fill gaps between nodes (whitespace, comments) by scanning the
   source between consecutive AST offsets.
4. For unrecognized spans (e.g. `\verb` bodies), produce
   `Unparsed { text; span; reason }` nodes per ADR-005.

## Prerequisite audit (PR B0.5)

Before PR B1 commits to this strategy, verify `Parser_l2` records
enough information:
- ✅ / ❌ `located_node.offset` accurate per AST node
- ✅ / ❌ Comments preserved OR scannable from source directly
- ✅ / ❌ Whitespace positions recoverable from offset diffs
- ✅ / ❌ Group delimiter spans captured

If audit reveals gaps, fallback: add a lightweight lex pass in
`Cst_of_ast.ml` (~0.5 day extra).

## Alternatives considered

- **Option A: Parallel parser — write a CST-producing parser from scratch.**
  Duplicates parsing logic. Risk of divergence from existing Parser_l2.
  Rejected.
- **Option B: Modify `Parser_l2` to emit CST directly.**
  Destabilizes a proven, tested module. Breaks `ParserSound.v` proof
  surface. Rejected.
- **Option C: AST only — no CST.**
  Loses memo §16.3 deliverable. Rejected.

## Consequences

- PR B0.5 (parser audit, 0.5 day) is a hard prerequisite of PR B1.
- If audit fails, B1 grows by 0.5 day for a lightweight lex pass.
- `Cst_of_ast.ml` is the sole module implementing the strategy;
  all other code consumes `Cst.t` directly.
- Future Parser_l2 changes must preserve offset accuracy — add a
  regression test in B0.5 that locks this invariant.
