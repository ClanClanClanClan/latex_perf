# Fix-suggestion style guide (v26.2 / v26.2.1)

As rule authors add `fix : Cst_edit.t list option` suggestions,
consistency matters: users see these in validator output and
potentially `--apply-fixes` their source. Inconsistent style erodes
trust.

**v26.2.1 update:** the field is a **list** of edits per result
(`Cst_edit.t list option`), not a single edit, because many rules
aggregate matches per document (see TYPO-002/003 below). The list
must be non-empty when `Some`; use `None` for "no fix available".
Construct via `Validators_common.mk_result_with_fix ~fix` — never
populate the record literal directly (gate: `check_result_helpers`).

## Canonical patterns

### Replacement fixes
- Use minimum span: replace only the problem span, not surrounding context.
- Preserve capitalization / punctuation outside the span.
- Prefer Unicode characters that render correctly in both pdflatex + UTF-8
  input mode (XeLaTeX) OR that have `\tex` escapes that work in both.

### Insertion fixes
- Insert at a semantically meaningful span boundary (start of env, after
  `\documentclass`), not arbitrary offsets.
- Include a trailing newline if inserting a line-shaped construct
  (`\documentclass{article}\n`).

### Deletion fixes
- Delete minimal span. If the problem is `  ,` (space before comma),
  delete the space, not the comma.

## Examples (exemplar rules — v26.2.1 PRs #2, #3)

**STRUCT-001: Missing `\documentclass`** (single insertion at top)
```ocaml
let fix = [ Cst_edit.insert ~at:0 "\\documentclass{article}\n" ] in
mk_result_with_fix ~id:"STRUCT-001" ~severity:Warning
  ~message:"Missing \\documentclass" ~count:1 ~fix
```

**TYPO-002: `--` should be `–` (en dash)** (N replacements, one per
match — requires a second scan pass to collect offsets because the
rule aggregates `count`)
```ocaml
let edits =
  List.map
    (fun off -> Cst_edit.replace ~start_offset:off ~end_offset:(off + 2) "–")
    offsets
in
mk_result_with_fix ~id:"TYPO-002" ~severity:Warning
  ~message:"Double hyphen -- should be en-dash –" ~count:(List.length edits)
  ~fix:edits
```

**TYPO-003: `---` should be `—` (em dash)** — same shape as TYPO-002
with `end_offset:(off + 3)` and replacement `"—"`.

## Anti-patterns (reject in review)

- **Overly aggressive span.** Don't replace a whole sentence to fix one
  character.
- **Ambiguous replacement text.** `text = "corrected"` without explanation
  leaves the user confused.
- **Multi-location fixes in one edit.** One `edit` per problem span;
  composite rewrites use multiple `edits`.
- **Fixes that change semantics subtly.** E.g., "--" vs "\," changes
  math vs text interpretation. Don't automate ambiguous cases.
- **Localized/translated fix text.** Always English in v26.2; future
  versions may add locale.

## Review checklist for new fix-suggesting rules

- [ ] Fix has minimal span.
- [ ] Replacement text renders correctly in pdflatex + xelatex + lualatex
  (or comment lists which engines NOT supported).
- [ ] `Cst_edit.edit` constructor matches the user's intent (Insert vs
  Replace vs Delete).
- [ ] Unit test verifies the fix applies without corrupting surrounding
  context.
- [ ] E2E test (`test_rule_fix_integration.ml`) includes this rule.
- [ ] CHANGELOG mentions the new fix in the rule's row.

## When NOT to provide a `fix`

Not every rule should suggest a fix:
- **Ambiguous cases** (user needs context): no fix.
- **Style rules** (Class D) with taste-dependent outcomes: no fix.
- **Rules that fire on multi-span patterns** where single-span edit
  can't express the correction: no fix.

Leaving `fix = None` is always acceptable.
