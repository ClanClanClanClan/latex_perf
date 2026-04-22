# Parser_l2 Capability Audit (v26.2 PR B0.5)

**Scope.** Before shipping the lossless CST in PR B1, this document
audits exactly what `latex-parse/src/parser_l2.ml` records, what it
loses, and which strategy for CST generation is cheapest to add
without breaking the existing runtime.

**Outcome.** Post-process-only strategy is feasible (per ADR-008) with
**one required parser change**: add `end_offset` to the `loc` record.
Everything else the CST needs can be recovered by re-walking the source
between adjacent AST-node start offsets.

---

## 1. Inventory of what Parser_l2 records

### 1.1 AST shape (`parser_l2.mli:6-48`)

| Node variant | Fields | Byte-lossless? |
|--------------|--------|-----------------|
| `Word of string` | text | **yes** |
| `Cmd of cmd` | `{ name; opts: string list; args: string list }` | **no** (loses whitespace + delimiters between opt/arg groups) |
| `Group of node list` | body | **no** (loses exact `{`/`}` positions) |
| `Environment of { env_name; opts; body }` | env body as `node list` | **no** (body loses locations; `\begin{…}`/`\end{…}` not represented structurally) |
| `MathInline of string` | content | **yes** (but `$...$` delimiters lost; stored implicit) |
| `MathDisplay of string` | content | **yes** (but `$$`/`\[`/environment delimiters lost) |
| `Comment of string` | `%` to EOL text | **yes** (leading `%` implicit) |
| `Verbatim of { env_name; content }` | opaque content | **yes** |
| `Whitespace of string` | raw whitespace run | **yes** |
| `Newline` | (tagged) | **yes** (literal `\n`) |
| `Error of { message; position }` | error marker | n/a (synthetic) |

### 1.2 Location representation (`parser_l2.mli:3`)

```ocaml
type loc = { line : int; col : int; offset : int }
type located_node = { node : node; loc : loc }
```

**Every `located_node` carries a START offset but NO length or end
offset.** The existing consumers (`Node_id.of_located`,
`Partial_cst.classify`) compute a node "extent" by re-scanning or by
approximating via downstream offsets. This is the single biggest gap
for CST generation.

### 1.3 Document-level structure (`parser_l2.mli:21-48`)

- `document` record exposes `preamble`, `body`, `labels`, `refs`,
  `errors`, `packages`, `documentclass`.
- `preamble` and `RawNodes` carry `located_node list` — good, locations
  propagate.
- `Paragraph` / `Float { body }` also keep `located_node list`.
- `Section { children : doc_element list }` — no direct located info
  on the section heading itself, only on its body.

---

## 2. What the CST needs (per `specs/v26/V26_2_PLAN.md` §2.5)

The planned CST type (v26.2):

```ocaml
type cst_node =
  | CToken of { kind; text; span: span }
  | CTrivia of { kind; text; span: span }  (* whitespace, comments *)
  | CGroup of { delim; children: cst_node list; span }
  | CEnvironment of { name; delim_begin; delim_end; body: cst_node list; span }
  | CCommand of { name; opts: cst_arg list; args: cst_arg list; span }
  | CMathInline of { delim; content: string; span }
  | CMathDisplay of { delim; content: string; span }
  | CVerbatim of { env_name; content; span }
  | CUnparsed of { text; span }
```

with `span = { start_offset; end_offset }` and strong invariants:
- **Byte-lossless:** `serialize cst = original_source` for arbitrary
  input (via the `Unparsed` fallback).
- **Structure-lossless:** for the declared LP-Core subset, parsing
  the serialized CST round-trips through Parser_l2 identically.

Per ADR-007 / ADR-008, CST is generated **post-process** from the
existing AST; we don't clone the scanner.

---

## 3. Gap analysis

| CST requirement | Parser_l2 status | Gap |
|-----------------|-------------------|-----|
| `start_offset` per node | ✓ (`loc.offset`) | none |
| `end_offset` per node | ✗ | **must add** |
| Trivia (whitespace/comment) preserved | ✓ (first-class nodes) | none |
| Command `name` span separate from args | ✗ (no per-arg span) | recoverable via rescan + ADR-008 fallback to `CUnparsed` |
| Group delimiter positions | ✗ (implicit) | recoverable via rescan — `{` at `loc.offset`, match closing `}` via balanced walk |
| Environment `\begin{…}` / `\end{…}` spans | ✗ | recoverable — start is `loc.offset`, end requires rescan through `\end{name}` |
| Math mode delimiter preservation | ✗ (content stored without surrounding `$`/`$$`/`\[`/`\]`) | recoverable — first char at `loc.offset` tells us which flavour |
| Verbatim content | ✓ (opaque string) | none |
| Error nodes | ✓ (synthetic) | none — CST emits `CUnparsed` around errors |

**Net:** one intrusive change (add `end_offset`); everything else is
"scan source between offset_N and offset_{N+1}" work in the CST
builder.

---

## 4. Strategy comparison

### 4.1 Post-process only (ADR-008, recommended)

**Approach.** CST builder `Cst_of_ast.of_source_and_ast :
string -> document -> cst_node list` walks the AST in order, using
`loc.offset` (and new `loc.end_offset`) to pull exact source bytes for
each span. Gaps between adjacent nodes become `CTrivia` (reclassified
from raw whitespace) or `CUnparsed` (if the gap contains unrecognizable
content — rare, only around `Error` nodes).

**Pros.**
- No scanner duplication; Parser_l2 remains single source of truth.
- The `Unparsed` fallback means byte-losslessness is easy:
  whenever the builder can't classify, it emits `CUnparsed` with the
  raw bytes.
- Perf: one linear pass over source + AST.

**Cons.**
- Need to add `end_offset` to `loc`. Ripples through `parser_l2.ml`
  (every `{ node; loc }` construction site) and consumers that
  destructure `loc` (currently only `Node_id.of_located` and
  `Partial_cst.classify` — both can be updated trivially since they
  already compute extent by other means).
- Slightly heavier `located_node` memory footprint (+ 1 int per node).

### 4.2 Post-process + lightweight re-lex (fallback)

**Approach.** If adding `end_offset` proves too invasive, write a
minimal re-lexer (`Cst_lexer.scan_between : string -> int -> int ->
cst_token list`) that the CST builder calls for each AST-node range.

**Pros.**
- No changes to Parser_l2.
- Explicit classification of delimiters.

**Cons.**
- Scanner duplication — violates ADR-008. The minimal re-lexer has to
  handle at least: whitespace runs, `%` to EOL, balanced `{...}`,
  `$`/`$$` matching. In practice this IS the scanner.
- Perf: two passes over the source for every CST conversion.

**Verdict.** Option 4.1 is cheaper and compatible with ADR-008.

---

## 5. Required parser changes (PR B1 prerequisite)

### 5.1 Add `end_offset` to `loc`

```ocaml
(* latex-parse/src/parser_l2.mli *)
type loc = {
  line : int;
  col : int;
  offset : int;
  end_offset : int;  (* NEW: byte offset just past the last byte of the node *)
}
```

**Why `end_offset` and not `length`.** Consumers generally want the
byte range `[offset, end_offset)` directly, not a length that they have
to add. Matches the `span` type planned for CST. Equivalent up to a
trivial arithmetic.

**Callers to update.** A rough `grep` says ~45 record-literal sites in
`parser_l2.ml` and ~8 callers in `partial_cst.ml`, `node_id.ml`,
`rest_api_server.ml`. Most are straightforward: at the emission site,
`end_offset := st.pos` (parser state after emission).

### 5.2 Preserve `located_node` for environment body

Currently:
```ocaml
Environment { env_name; opts = []; body : node list }
```

For structural CST, we need:
```ocaml
Environment { env_name; opts = []; body : located_node list }
```

The parser *already* builds `body_lnodes : located_node list` internally
(`parser_l2.ml:373-378`) and then maps away the locations. Preserving
them is a one-line change at the `node = Environment …` emission.

**Impact on existing consumers.** One extra `.node` accessor per
caller that iterates `body`. ~6 sites; trivial.

### 5.3 (Optional, deferred) per-arg `loc` on `cmd`

Currently `cmd.opts` and `cmd.args` are `string list` with no
location. v26.2 scope for the rewrite engine can live with this —
rewrites fire on whole commands, not on individual arg characters.
Adding per-arg locations is v26.3 scope unless the rewrite engine
immediately needs it.

---

## 6. Implementation plan for PR B1

1. **Extend `loc`** with `end_offset` (§5.1). Update all record-literal
   sites in `parser_l2.ml`. Update direct consumers of `loc` fields in
   `partial_cst.ml`, `node_id.ml`, `rest_api_server.ml`. Run
   `dune build` + `dune runtest` — all existing tests should pass.

2. **Preserve located_node in env body** (§5.2). Update 1 site in
   `parser_l2.ml`, update ~6 consumers.

3. **Create `cst.{ml,mli}`** with the type in §2. Initially just types
   + a `serialize : cst_node list -> string` that concatenates spans.

4. **Create `cst_of_ast.{ml,mli}`** — the post-process builder.
   Take `source` + `document`, walk ordered `located_node list`, emit
   CST. Gaps between node-end and next-node-start become `CTrivia` or
   `CUnparsed`.

5. **Create `stable_spans.{ml,mli}`** — shift-on-edit semantics for
   `span = { start_offset; end_offset }`. Reuse / extend `Node_id`.

6. **Perf test** — `test_cst_perf.ml` measures `Cst.of_source` on a
   10 MB LaTeX file. Ratchet at 100 ms (vs current parser ~30 ms).

7. **Unit tests.** `test_cst.ml`, `test_cst_of_ast.ml`,
   `test_stable_spans.ml`. At minimum: byte-lossless serialize for the
   common node kinds + round-trip test on `corpora/lint/` smallest
   files.

---

## 7. Risks

- **`end_offset` addition touches many sites.** Mitigation: do it in a
  single atomic commit; pre-B1 CI catches any regression. Estimated
  ~200 LoC of mechanical edits plus testing.
- **Gap classification corner cases.** Environments nest; our gap
  finder needs to know when a gap is "inside an environment" (so it's
  part of the CEnvironment.body) vs "between top-level nodes" (so it
  becomes trivia at the document level). Handled by the recursive
  structure of the builder — gaps are computed per-scope.
- **Whitespace and `Newline` are already tokenized.** The builder
  preserves them as `CTrivia` nodes rather than coalescing them into
  gaps; gap-finding only runs where no node exists between two AST
  nodes (e.g. between `\begin{foo}` and its first body node, where
  the parser doesn't emit trivia).

---

## 8. Estimated effort for PR B1

| Task | Days |
|------|------|
| `loc` + `end_offset` surgery | 1.0 |
| CST type + serialize | 0.5 |
| Cst_of_ast builder | 1.0 |
| Stable spans | 0.5 |
| Perf + unit tests | 0.5 |
| **Total** | **3.5 (matches plan §3.2)** |

---

## 9. References

- `specs/v26/V26_2_PLAN.md` §3.2 — PR B1 scope
- ADR-005 — CST two-level round-trip (byte vs structure)
- ADR-006 — CST subset definition
- ADR-008 — CST-gen via post-process AST (this audit confirms feasibility)
- `latex-parse/src/parser_l2.ml` — parser source
- `latex-parse/src/parser_l2.mli` — parser interface
