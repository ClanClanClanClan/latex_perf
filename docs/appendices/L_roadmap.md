# Appendix L -- Roadmap & De-scoped Ideas

Revision 2026-04-14. Current position: Week 80 of 156.

---

## L-1 De-scoped from v25

Features explicitly excluded from the v25 release, with rationale:

| Feature | Reason | Target Release |
|---------|--------|----------------|
| Full catcode reassignment (`\catcode`) | Turing-complete; violates epsilon-safety property | v27+ |
| `\newcommand` expansion | Requires document-wide state; L1 scope only handles catalogued macros | v26 |
| Beamer frame structure | No validators in v25 rule catalogue; `\documentclass{beamer}` not parsed | v26 |
| Algorithm environment deep parsing | No validators beyond float detection | v26 |
| PDF output analysis | Requires LaTeX compilation; true L3-semantic layer | v26 |
| Compile-log parsing (full) | 55 rules need `.log` file analysis (LAY, PAGE families); partial in v25 | v26 |
| GPU TikZ rasterisation | Experimental L5; needs A100 GPU access | v26 |
| Full Unicode equivalence beyond NFC | NFKC, NFD intentionally out of scope (see Appendix F) | v27 |
| Unicode collation | Locale-specific sorting not needed for validation | v27+ |
| Complex text layout (ligatures, shaping) | Rendering engine territory, not lint territory | v27+ |
| Emoji handling | Not applicable to academic LaTeX documents | Deferred |
| ICU BreakIterator integration | Pure OCaml range-check approach chosen for determinism | Deferred |
| Interactive IDE protocol (full LSP) | v25 is CLI/REST only; IDE via REST proxy | v27 |

---

## L-2 v25 Timeline Position

### Completed Milestones

| Weeks | Phase | Status | Key Deliverables |
|-------|-------|--------|-----------------|
| 1--10 | Bootstrap + L0 lexer | Done | Catcode model, tokenizer, basic validators |
| 11--20 | L1 expander + proofs | Done | Fuel-bounded expansion, Coq proofs |
| 21--30 | L2 parser + RegexFamily | Done | PEG parser, generic soundness tactic |
| 31--40 | ML span extractor v1 | Done (retired) | SciBERT tagger, ceiling at F1=0.8503 |
| 41--50 | L3 semantic interpreter | Done | Label/ref tracking, semantic state |
| 51--60 | L4 style validators | Done | Sentence-level heuristic rules |
| 61--70 | Elder runtime | Done | Layer sync, event bus, lock-free queue |
| 71--80 | Corpus + coverage | Done | 99.7% parser corpus, 568 rules |
| 86--91 | Proof farm scale | Done | 429 theorems, parallel CI |
| 92--96 | CJK + RTL pipelines | Done | Language detection, 7 live packs (PR #167) |
| 97--101 | Language-specific validators | Done | 84 new rules, 568 total (PR #168/#169) |

### Current and Upcoming

| Weeks | Phase | Status | Description |
|-------|-------|--------|-------------|
| 102--104 | Corpus expansion + i18n test | Done | 33 i18n corpus files, QA gate operational (PRs #197/#198) |
| 105--110 | ML v2 training | Done | ByteClassifier v2 F1=0.9799 on A100; SpanExtractorSound.v QED |
| 111--120 | Performance hardening | Done | Chunk store, EDF scheduler, ML confidence, Str→Re migration |
| 121--130 | Proof maturity | Done | 606 faithful proofs; paragraph-local Coq models; 10 severity fixes |
| 131--140 | Integration testing | Done | 36 paranoid e2e tests; 0 weak assertions across 97 files |
| 141--150 | Release preparation | Done | CHANGELOG, Dockerfile, release.yml, docker-push.yml, scripts/release.sh |
| 151--156 | GA release | Done | v25.0.0-rc1 tagged; SBOM + Cosign signing in CI |

---

## L-3 v26 Forward-Looking

### L-3.1 L3 Compile-Log Integration

Parse `.log` files for overfull/underfull boxes, widow/orphan penalties, and
page layout violations. Enables the remaining 55 unimplemented rules (LAY and
PAGE families).

Key lesson from PR #169: the LAY rules in the spec require compile-log output
(e.g., "page number suppressed on chapter opener") that cannot be approximated
from source text alone.

### L-3.2 User Macro Registry

Parse `\newcommand`/`\renewcommand`/`\DeclareMathOperator` from the preamble
into a per-document macro table. Feed into the L1 expander as a document-scoped
catalogue extension.

Current L1 expander (`simple_expander.ml`) only handles the 520 catalogued
macros (441 symbol + 79 argsafe).

### L-3.3 Multi-File Linting

Resolve `\input`/`\include` chains. Build a file dependency graph. Run
validators across the full document tree.

### L-3.4 Beamer Support

Detect `\documentclass{beamer}`, parse `frame` environments, validate slide
structure (e.g., frametitle presence, itemize nesting depth).

### L-3.5 gRPC IPC API

Implement the spec's streaming API:

```protobuf
service Elder {
  rpc Validate     (stream Patch)       returns (stream IssueDelta);
  rpc SnapshotSave (SnapshotRequest)    returns (SaveReply);
  rpc SnapshotLoad (SnapshotId)         returns (SnapshotReply);
}
```

---

## L-4 v27 Research Items

### L-4.1 Full Catcode Support

Track `\catcode` assignments through the document. Requires a catcode-state
machine per chunk boundary.

### L-4.2 Conditional Expansion

Limited `\ifx`/`\iftrue`/`\iffalse` support for common patterns (package
detection, engine detection). Not full Turing-complete expansion.

### L-4.3 Interactive IDE Protocol

LSP-compatible incremental analysis. Real-time diagnostics with sub-10ms
latency on keystroke. Requires the full Elder runtime with chunk store and
EDF scheduler.

### L-4.4 Formal PEG Verification

Prove the PEG grammar in `l2_parser_peg_grammar.peg` is unambiguous and
complete for the LaTeX-epsilon subset.

### L-4.5 Cross-Language Transfer Learning

Per-script ML adapters for the byte classifier. Train on English, transfer to
French/German/CJK with minimal fine-tuning.

---

## L-5 Gated Features (v25)

Features that exist in the v25 codebase but are gated behind environment
variables or feature flags:

| Feature | Gate | Status | Notes |
|---------|------|--------|-------|
| TYPO rules | `L0_VALIDATORS=pilot` | Active in CI | Env var activates pilot rule set |
| SIMD xxHash | `L0_USE_SIMD_XXH=1` | Optional | Falls back to scalar on failure |
| Lock-free event bus | Always on | Production | Requires OCaml 5.x Atomic |
| ML byte classifier | Requires trained model checkpoint | Blocked | A100 GPU needed |

---

## L-6 Governance (Post-GA)

| Role | Responsibility | Bus-factor |
|------|---------------|------------|
| Steward | Roadmap, breaking changes, proof standards | Steward + 2 deputies |
| Core maintainer | Merge, CI infra, proof review | 5+ |
| Triage team | Labels, first-line support | Unlimited |
| Security team | Private CVE intake, embargo | 3+ |

Process: RFC -> 7-day open comment -> Steward verdict.

---

## L-7 Deprecation & Compatibility

SemVer policy:
- **MAJOR** = DSL or layer API break
- **MINOR** = new validators, performance improvements, CI changes
- **PATCH** = bug fixes, documentation, proof corrections

Deprecation flow:
1. RFC filed with rationale
2. Mark `@deprecated` in code with migration guide
3. Two MINOR releases with compiler warnings
4. Removal in next MAJOR

CI enforcement: `check_deprecated.ml` verifies the deprecation sequence is
followed for all `@deprecated` annotations.

---

## L-8 Security Policy

From `docs/SECURITY.md`:

- **Reporting:** `security@latex-perfectionist.dev` (72-hour response SLA)
- **Disclosure:** CVD best practices; 45-day max disclosure window, 15 days if
  actively exploited
- **Scoring:** CVSS v4 with modifier for macro-expansion RCE
- **SBOM:** CycloneDX JSON generated in CI; attached to every release
- **Scanning:** Weekly cron: `cargo audit`, `opam audit`, `trivy fs`; fail on
  High with available fix
- **Sandboxing:** seccomp profile at `scripts/sandbox/seccomp.json` restricts
  syscalls to file I/O, mmap, socket, clone, clock_gettime

---

## L-9 Knowledge-Transfer Artefacts

| Artefact | Location | Update Frequency |
|----------|----------|-----------------|
| Architecture handbook | `docs/ARCH.md` | Evergreen |
| Proof-writers guide | `docs/PROOF_GUIDE.md` | Every MINOR |
| Release process video | S3 archive | On process change |
| Brown-bag recordings | `recordings/` index | Quarterly |

---

## L-10 On-boarding (New Maintainers)

Five-step process:

1. **Contributor survey** — time-zone, expertise areas, language skills
2. **Starter quest** — fix a TYPO rule, add a unit test, prove a trivial lemma
3. **Pair-review** with steward on first real PR
4. **Triage team** — after 2 green PRs, invited to triage rotation
5. **Core eligibility** — after 10 merged PRs + 2 proof modules reviewed

Mentor checklist: `maintainers/onboarding_checklist.yaml`

---

## L-11 Release Cadence

| Train | Branch | SLA | Frequency |
|-------|--------|-----|-----------|
| main | `main` | CI green; 0 admits | ~weekly |
| beta | `v25.x-beta` | Same proofs; perf may lag | monthly |
| LTS | `v25-lts` | Only security/critical fixes | ~9 months |
| next-major | `v26-dev` | Proof debt behind gates OK | none |

---

## L-12 Regression-Budget Policy

- **Proof debt** must remain zero.
- **Performance budget:** p95 latency may rise at most +5% over last LTS;
  improvements are banked as negative budget.
- If a PR exceeds budget: regression freeze; author must add compensating
  optimisation or hide behind feature-flag.

---

## L-13 Sustainability

| Stream | Status | Annual Target (USD) |
|--------|--------|-------------------|
| GitHub Sponsors | Live | 8k |
| OpenCollective | Live | 6k |
| Enterprise support | Pilot @ GA | 30k |
| Research grants | Pipeline | n/a |

Budget split: 60% infra (CI runners, hosting) / 25% stipend / 10% bounties /
5% community/docs.

---

## L-14 End-of-Life (EOL)

If 12 months pass with zero commits and no steward:
- Org becomes read-only archive.
- Third-party forks may adopt trademark under MIT adhesive licence if they:
  1. Preserve copyright
  2. Maintain 0-admit
  3. Publish SBOM for each release

---

## L-15 Appendix Change-log

- 2026-04-05 — Initial revision (PR #194). De-scoped features, timeline,
  v26/v27 items, governance, release cadence, security policy, on-boarding.
- 2026-04-06 — Added deprecation policy (L-7), security policy (L-8),
  knowledge-transfer artefacts (L-9), on-boarding (L-10).

---

End of Appendix L.
