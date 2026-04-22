# v26.2 communication plan

## Audience channels

- **GitHub Releases page** — primary announcement surface.
- **GitHub Discussions** (if enabled) — ongoing Q&A.
- **CHANGELOG.md** — authoritative record.
- **Repo README** — version recommendation.

No mailing list, no Discord, no Twitter — this is a library/CLI, not a
product.

## Release-stage template

Each alpha or full tag publishes a Release page with the following
structure:

```markdown
# v26.2.0-alpha1 — <YYYY-MM-DD>

⚠️ **Pre-release.** For testing the compile-guarantee pipeline.
Not for production use. Known incomplete: CST + rewrite engine
(lands in alpha2).

## Highlights
- `latex-parse/src/compile_contract.ml` — pre-compile readiness predicate
- T0–T5 theorem wrappers; T6/T7 hypothesis-parametric in CompileProgress.v

## Breaking changes
None (strictly additive per plan §8).

## Try it
```bash
opam install latex_parse.26.2.0-alpha1
latex_parse_cli --compile-check path/to/main.tex
```

## Known issues
- [link to open issues tagged `v26.2.0-alpha1`]

## Full changelog
[see CHANGELOG.md for the [v26.2.0-alpha1] section]
```

## Template for v26.2.0 final

```markdown
# v26.2.0 — <YYYY-MM-DD>

## Summary
Ships partial-parsing substrate, lossless CST, rewrite engine v1, and
the compilation-guarantee theorem stack T0–T7 (hypothesis-parametric).
Strictly additive over v26.1 — no breaking changes.

## For users of v26.1.0
- Upgrade path: `opam update && opam upgrade latex_parse`. No code
  changes required.
- New CLI flags: `--apply-fixes`, `--compile-check`.
- New library modules: see `docs/MIGRATION_v26.1_to_v26.2.md`.

## For library consumers
- `Validators.result` gains `fix : Cst_edit.edit option`. Existing
  pattern matches keep working (field is optional).
- New modules: `Cst`, `Cst_edit`, `Rewrite_engine`, `Project_model`,
  `Build_graph`, `Aux_state`, `Compile_contract`, `Stable_spans`.

## Verification
- 13 CI gates green on tag commit.
- Differential test vs v26.1.0 on corpus: 0 unexpected diffs.
- All existing tests PASS.

## Artefacts
- Docker image: `ghcr.io/.../latex-perfectionist:26.2.0`
- opam: `opam install latex_parse.26.2.0`
- SBOM: attached to this release as sbom-cyclonedx.json
- Cosign signature: `sigstore verify ...`

## Credits
[contributor list]
```

## Alpha user expectations

Explicitly document:
- **No SLA.** Alpha users accept the tool may break between alpha1 and
  alpha2.
- **Feedback welcomed** via GitHub Issues tagged `v26.2-alpha-feedback`.
- **Bug reports** to the regular Issues tracker. High-severity alpha
  bugs trigger Scenario 1 in ROLLBACK_DRILL.md.
- **Upgrade path.** Alpha users should pin the alpha version until
  the final v26.2.0 ships; then upgrade via `opam upgrade`.

## Post-tag checks (for whoever publishes)

Within 10 min of `git push origin v26.2.0`:
1. `gh run watch` until `release.yml` completes.
2. Visit the Releases page and confirm artefacts attached.
3. Try `docker pull ghcr.io/.../latex-perfectionist:26.2.0` from a
   clean machine. If it fails, Scenario 3 in ROLLBACK_DRILL.md.
4. Post a Discussions thread (if enabled) linking the release.

## Silence policy

Between alphas and the final, no external communication is required.
Internal development continues on `main`. Alpha testers read
CHANGELOG.md working sections if they care.
