# LaTeX Perfectionist — Formal Language Contract (v26)

**Status:** v26 normative
**Source of truth:** this document + `specs/v26/language_contract.yaml`
**Runtime:** `latex-parse/src/language_profile.ml`
**Proof:** `proofs/LanguageContract.v`
**Spec reference:** `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` §4

---

## Purpose

The language contract defines **what "LaTeX" means for the purposes of LaTeX Perfectionist's guarantees.** Every document the analyzer processes is classified into one of three tiers with explicit, bounded support claims.

The contract is the boundary between:
- what the formal soundness theorems claim,
- what the runtime offers weaker contracts for,
- what is explicitly outside the supported domain.

---

## Tiers

### LP-Core — fully guaranteed subset

Documents in LP-Core receive the strongest claims: parser soundness, macro expansion determinism, bounded user macro admissibility, and compile-log-derived diagnostics under declared engine profiles.

#### Supported engines
- pdfLaTeX (primary target)

#### Admitted syntax
- Standard document structure: `\documentclass`, `\usepackage`, `\begin{document}`, `\end{document}`
- Sections (`\section`, `\subsection`, `\subsubsection`, `\paragraph`), figures, tables, lists
- Math environments: `$...$`, `$$...$$` (discouraged), `\[...\]`, `equation`, `align`, `align*`, `gather`, `multline`, `eqnarray`
- Cross-references: `\label`, `\ref`, `\cite`, `\bibliography`, `\includegraphics`
- Standard commands: `\textbf`, `\emph`, `\textit`, `\texttt`, `\url`, `\href`, `\footnote`, `\caption`
- Catcode-passive control sequences only

#### Admitted macros
- Full built-in macro catalogue (`core/l1_expander/macro_catalogue.json` — 520 macros)
- Bounded user macros: `\newcommand`, `\renewcommand`, `\providecommand` with:
  - Fixed arity ≤ 9
  - No catcode changes in body
  - No delimited-argument tricks
  - Cycle-detected, fuel-bounded expansion
  - See `latex-parse/src/user_macro_registry.ml`

#### Admitted packages
- `inputenc`, `fontenc`, `babel`, `polyglossia`
- `amsmath`, `amssymb`, `amsthm`, `mathtools`
- `graphicx`, `xcolor`, `caption`, `subcaption`
- `hyperref`, `url`, `cleveref`, `booktabs`
- `natbib`, `biblatex`
- `enumitem`, `microtype`
- Per-project additions only if they do not mutate catcodes or execute shell commands.

#### Proof claims
- Parser soundness (`ParserSound.v`)
- Lexer determinism + totality (`LexerDeterminism.v`, `LexerTotality.v`)
- User macro termination + cycle detection (`UserExpand.v`)
- Partial parse locality (`PartialParseLocality.v` — E0)
- Damage containment (`DamageContainment.v` — E1)
- Project include-graph soundness (`IncludeGraphSound.v`)
- Hybrid invalidation soundness (`InvalidationSound.v`)
- Per-rule soundness for all LP-Core-applicable rules (`proofs/generated/`)

#### Forbidden constructs
- Arbitrary `\def` (non-`\newcommand` macro definition)
- Catcode mutation via `\catcode`, `\makeatletter`, `\makeatother` outside package boundaries
- Shell-escape: `\write18`, `\immediate\write18`, `\ShellEscape`
- `\csname...\endcsname` metaprogramming
- `\expandafter`-heavy conditional programming
- Primitive TeX conditionals outside supported macro catalogue (`\if`, `\ifnum`, `\ifdim`, `\ifx`, etc.)
- TikZ programs with `\pgfmathparse` calls that mutate state
- Package-less arbitrary redefinition of built-in commands

A document containing a single forbidden construct is not LP-Core.

---

### LP-Extended — practical but weaker contracts

Documents that use features beyond LP-Core but remain analyzable. Contracts are extractor-based and sandboxed; downgraded proof claims apply.

#### Supported engines (with caveats)
- XeLaTeX (beta)
- LuaLaTeX (beta)

#### Additional syntax
- `\def\x{...}` — detected but not expanded (surfaced as unsupported-feature diagnostic)
- Conditional macros (`\ifdefined`, `\@ifundefined`)
- Package-declared commands outside the built-in catalogue (treated as opaque)

#### Additional packages (contract-tested)
- `fontspec` (XeLaTeX/LuaLaTeX)
- `luacode` blocks (opaque)
- `listings`, `minted` (syntax highlighting — minted requires shell-escape, borders LP-Foreign)
- `pgfplots`, `tikz` with bounded compilation time
- Institution-specific packages (`acmart`, `elsarticle`, `IEEEtran`, `revtex`)

#### Contracts
- Parser continues on degraded input; `Partial_cst.classify` assigns Partial/Broken trust zones where parsing was error-recoverable.
- Compile-log evidence (overfull boxes, undefined refs) is Class C diagnostics.
- No soundness claim for semantically resolved labels/refs if an LP-Extended package modifies cross-reference behaviour.

#### Proof claims (downgraded)
- Parser accepts input (no soundness on derived AST for unresolved constructs)
- Compile-log evidence is monotonic (`BuildLog.v` conditional theorems)
- L3 file validators remain formally conservative (`proofs/generated/L3_FIG.v`, etc.)

---

### LP-Foreign — explicit rejection domain

Documents that exceed LP-Extended boundaries. The analyzer detects them, surfaces the boundary, and refuses strongest claims.

#### Triggers
- Shell-escape (`\write18`, `\immediate\write18`, `\ShellEscape`)
- Catcode mutation via `\catcode\` or primitive `\let\` redefining catcode-carrying tokens
- `\csname...\endcsname` with dynamically constructed names
- TeX primitive metaprogramming: `\csstring`, `\detokenize`, `\scantokens`
- External preprocessors: `knitr`, `sweave`, dynamic LaTeX generated from non-LaTeX sources
- Executable document modes: `\openout`, `\input` via `\jobname` interpolation
- TikZ programs that invoke `\pgfmathparse` with global state mutation
- Custom drivers that redefine engine primitives

#### Contracts
- Document is rejected for guaranteed-mode analysis.
- Best-effort linting proceeds; results carry `LP-Foreign` tag.
- No soundness claim whatsoever.
- User is notified which constructs triggered the classification.

---

## Tier membership decision procedure

The classifier runs in the following order (deterministic, total on any input):

1. **LP-Foreign detection pass** — scan source for any construct listed above. If found, return `LP_Foreign` with the list of triggering constructs.
2. **LP-Core violation pass** — scan source for arbitrary `\def`, catcode mutation, `\csname` metaprogramming, primitive TeX conditionals outside catalogue. If found, return `LP_Extended` with the list of violations.
3. **Otherwise** — return `LP_Core`.

The two passes are defined in `latex-parse/src/unsupported_feature.ml`. The classifier is in `latex-parse/src/language_profile.ml`.

---

## Formal guarantees

Proved in `proofs/LanguageContract.v`:

- **`tier_subset_transitivity`** — LP-Core features form a subset of LP-Extended features; LP-Extended forms a subset of "all inputs".
- **`tier_membership_decidable`** — The classify function is total: every input source maps to exactly one tier.
- **`unsupported_feature_detection_sound`** — If the classifier returns LP-Core, the source contains none of the forbidden constructs.
- **`lp_foreign_implies_no_soundness_claim`** — Documents classified LP-Foreign carry no per-rule soundness obligation.

Zero admits, zero axioms.

---

## CLI / API surface

- `validators_cli --profile {lp-core|lp-extended|lp-foreign|auto} <file.tex>` — force a profile or auto-detect. Default `auto`.
- REST request body field: `"profile": "lp-core"` (optional; env `L0_PROFILE_OVERRIDE` can force).
- When a document is classified `LP_Extended` or `LP_Foreign`, each validator result is tagged with the effective profile so consumers can filter.

---

## Relationship to rule contracts

Every rule in `specs/rules/rule_contracts.yaml` (PR #237) declares its minimum supported tier via the `project_scope` field. Rules with `project_scope: lp_core_only` do not fire on LP-Extended or LP-Foreign documents. Rules with `project_scope: any` fire regardless of tier but their confidence may be downgraded.

---

## Scope boundary (what this contract does NOT do)

- It does not implement full catcode tracking.
- It does not attempt to resolve LP-Extended package semantics beyond declared opaque regions.
- It does not compile documents; compile-guarantee theorems (T0–T7) are deferred to v26.2 (memo §5).
- It does not perform editorial policy selection; that is v27 (memo §13).
