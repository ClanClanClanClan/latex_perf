#!/usr/bin/env python3
"""Generate specs/rules/rule_contracts.yaml from rules_v3.yaml + runtime.

Produces the machine-readable rule-contract manifest consumed at runtime
by Rule_contract_loader (OCaml). Each rule receives deterministic defaults
based on its family; the 17 Class C rules from
latex-parse/src/execution_class.ml are handled explicitly.

Per PR #237 (memo §10, §15.4):
- Every rule gets phase, execution_class, proof_class, evidence_class,
  consumes, provides, depends_on, conflicts_with, fix_scope, project_scope.
- Output replaces Validator_dag.default_meta in validators.ml.

Usage:
    python3 scripts/tools/generate_rule_contracts.py [--output specs/rules/rule_contracts.yaml]
"""

from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]

# Single source of truth for which rules ship fix producers comes from the
# ledger generator (which is in turn cross-checked against the validator
# source by check_fix_producer_ledger.py).  Importing it avoids duplication
# and guarantees rule_contracts.yaml and FIX_PRODUCER_LEDGER.md cannot drift
# on the shipped-producer set.
_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))
from generate_fix_producer_ledger import SHIPPED_VERSIONS  # noqa: E402

SHIPPED_FIX_PRODUCERS: set[str] = set(SHIPPED_VERSIONS.keys())

# Rules that explicitly will NOT ship a fix producer, with documented reason.
# Per V27_FIX_PRODUCER_CADENCE.md acceptance criterion #3, every rule that
# cannot be fix-producing must carry `produces_fix: false` and a reason here.
#
# Three categories:
#   1. NLP-deferred (Bucket B): require sentence-tokenizer / language model.
#   2. Redundant: already covered by another shipped producer at the byte
#      level — emitting both would mean duplicate non-overlapping edits at
#      the same offset (which the apply_best_effort merger does deduplicate,
#      but explicit opt-out documents the design choice).
#   3. Pending-refinement: detection logic as currently written would
#      corrupt valid input if naively fix-produced; deferred until the
#      detection scope is narrowed.
FIX_PRODUCER_DEFERRED: dict[str, str] = {
    "SPC-018": (
        "Bucket C (candidate, --list-candidate-fixes / demoted from auto-fix in v27.1.16): "
        "inserting a space after a period+capital is IRREDUCIBLY intent-dependent — a "
        "common-word-stemmed dotted identifier (main.Py, time.Now, data.Frame) is lexically "
        "identical to a real sentence break, so an auto-fix would corrupt it. SPC-018 now "
        "emits a reviewable candidate instead of applying."
    ),
    # === Category 1: NLP-deferred (mirrors NLP_DEFERRED in the ledger gen) ===
    "TYPO-019": (
        "Bucket B: requires NLP / sentence tokenizer (rule detects "
        "context-dependent prose issues that cannot be statically resolved)."
    ),
    "TYPO-020": (
        "Bucket B: requires NLP / sentence tokenizer."
    ),
    "TYPO-030": (
        "Bucket B: requires NLP / abbreviation disambiguation."
    ),
    "TYPO-031": (
        "Bucket B: requires NLP / subject-verb agreement model."
    ),
    # === Category 2: Redundant with shipped producers (avoid duplicate edits) ===
    "CHAR-010": (
        "Redundant with ENC-020 (shipped v27.0.25, which deletes U+200E/200F "
        "LRM/RLM via dual-needle pattern).  CHAR-010 (U+200F right-to-left "
        "mark) is fully covered by ENC-020's `\\xe2\\x80\\x8f` needle; "
        "shipping a separate CHAR-010 producer would emit a duplicate delete "
        "edit at the same offset."
    ),
    "CHAR-011": (
        "Redundant with ENC-020 (shipped v27.0.25, which deletes U+200E/200F "
        "LRM/RLM via dual-needle pattern).  CHAR-011 (U+200E left-to-right "
        "mark) is fully covered by ENC-020's `\\xe2\\x80\\x8e` needle."
    ),
    # === Category 3: Pending refinement ===
    "CHAR-022": (
        "Current detection range covers U+E0000-U+E007F (4-byte UTF-8 with "
        "prefix `\\xf3\\xa0\\x80/\\x81`).  Post Unicode 8.0, U+E0020-U+E007F "
        "are TAG letters used inside flag emoji sequences "
        "(e.g. \U0001f3f4 + tag-letters for England/Scotland/Wales flags). "
        "A naive delete would corrupt valid flag emoji.  Producer deferred "
        "until detection scope is narrowed to U+E0000-U+E001F "
        "(deprecated language-tag range with no current valid use)."
    ),
    # === Category 2 additions (v27.0.43): more redundant rules ===
    "TYPO-063": (
        "Redundant with ENC-018 (shipped v27.0.31, which replaces "
        "U+2011 non-breaking hyphen `\\xe2\\x80\\x91` with `-`, "
        "URL+math-aware).  TYPO-063 detects the same exact byte sequence "
        "but message-flags it as \"inside URL\"; the underlying byte is "
        "the same.  ENC-018's fix already handles every TYPO-063 match."
    ),
    "SPC-007": (
        "Redundant with TYPO-008 (shipped v26.3.1, which collapses runs of "
        "`\\n` to 2 newlines).  SPC-007 detects 3+ consecutive blank lines; "
        "TYPO-008's fix normalises any such run."
    ),
    "SPC-013": (
        "Redundant with SPC-002 (shipped v26.2.1, which empties any "
        "whitespace-only line).  SPC-013 detects whitespace-only paragraphs "
        "(which are unions of whitespace-only lines); SPC-002 already empties "
        "each constituent line, leaving the paragraph empty."
    ),
    "SPC-014": (
        "Redundant with ENC-013 (shipped v27.0.30, which normalises mixed "
        "CR/LF line endings to LF).  SPC-014 detects mixed-LF/CRLF within "
        "a file; ENC-013's fix already handles every SPC-014 occurrence."
    ),
    "SPC-024": (
        "Redundant with SPC-002 (shipped v26.2.1, which empties any "
        "whitespace-only line).  SPC-024 detects \"leading spaces on a "
        "blank line\" which is a subset of \"whitespace-only line\"."
    ),
    "CHAR-021": (
        "U+FEFF inside paragraph conflicts with both ENC-002 (shipped "
        "v26.3.0, deletes BOM at file start) and SPC-012 (shipped v26.3.0, "
        "deletes mid-file BOM).  All three rules target the same 3-byte "
        "UTF-8 sequence `\\xef\\xbb\\xbf`.  ENC-002 + SPC-012 already form "
        "a known pre-existing conflict that the rewrite engine resolves "
        "via apply_best_effort; adding CHAR-021 as a third producer for "
        "the same bytes would expand the conflict without changing the "
        "auto-fix outcome.  Defer until the BOM-rule conflict is "
        "consolidated into a single producer."
    ),
    # === Category 4 (v27.0.43): rules whose nature precludes a static fix ===
    "ENC-001": (
        "Cannot auto-fix: mixed UTF-8 / Latin-1 in the same file is by "
        "definition ambiguous — without provenance information we cannot "
        "decide which encoding the user intended.  Surfaces as a diagnostic "
        "only; user must re-save with a single declared encoding."
    ),
    "ENC-003": (
        "Cannot auto-fix: invalid UTF-8 byte sequences are by definition "
        "unrecoverable — the original codepoint(s) cannot be reconstructed "
        "from corrupted bytes.  Surfaces as a diagnostic only."
    ),
    "ENC-008": (
        "Cannot auto-fix: Private-Use Area (U+E000-U+F8FF) codepoints have "
        "application-defined semantics (e.g., Apple's `` symbol at "
        "U+F8FF, Microsoft's Wingdings PUA mappings, custom-font glyphs).  "
        "A blind delete would corrupt valid uses; a replace cannot pick a "
        "canonical equivalent without knowing the source application."
    ),
    "ENC-009": (
        "Cannot auto-fix: same reason as ENC-008 — Private-Use Area "
        "codepoints have application-defined semantics that this rule "
        "cannot infer.  Different PUA range from ENC-008 but identical "
        "auto-fix risk profile."
    ),
    "ENC-010": (
        "Cannot auto-fix without breaking valid presentation: variation "
        "selectors U+FE00-U+FE0F modify the rendering of the preceding "
        "character.  VS15 (U+FE0E) and VS16 (U+FE0F) in particular force "
        "text-vs-emoji presentation on emoji-capable codepoints "
        "(e.g., `❤` is text presentation, `❤️` = ❤ + VS16 is emoji).  "
        "VS1-VS14 select CJK ideograph variants.  A blind delete would "
        "corrupt all of these.  Producer would require per-VS context "
        "analysis that is beyond a byte-level fix."
    ),
    "ENC-011": (
        "Overlaps with CHAR-005 (shipped v27.0.41, which deletes the "
        "control range U+0000-U+001F with exclusions for TAB/LF/CR and "
        "the dedicated bytes covered by CHAR-006/007/008).  ENC-011's "
        "detection scope is identical or a superset.  Defer until "
        "the families are consolidated into a single producer."
    ),
    # === v27.0.46 cleanup: redundant fix retracted ===
    "SPC-012": (
        "Fix-emission redundant with ENC-002 (shipped v26.3.0).  Both "
        "rules detect the same condition (BOM `\\xef\\xbb\\xbf` at a "
        "non-leading byte offset) and pre-v27.0.46 both emitted the "
        "IDENTICAL delete edit at the IDENTICAL offsets — `apply_best_"
        "effort` deduplicated but the duplicate emission was wasted work.  "
        "v27.0.46 reverted SPC-012 to count-only at the runtime level "
        "(diagnostic preserved per the v26.3.0 contract — both rules "
        "still fire as separate diagnostics, encoding different aspects "
        "of the same source issue); only ENC-002 emits the auto-fix."
    ),
    # === v27.1.13: Bucket C (context-required / --apply-fixes-with-prompt,
    #     v27.4.0) — confirmed per-rule during the shipping audit ===
    "MATH-012": (
        "Bucket C (context-required, --apply-fixes-with-prompt / v27.4.0): a multi-letter math token may be a FUNCTION name OR a product of scalar variables ($abc = a\\cdot b\\cdot c$). Wrapping the latter in \\operatorname is wrong; cannot decide statically."
    ),
    "MATH-032": (
        "Bucket C: the detected bracket may be a bare matrix delimiter OR the operand of \\bigl/\\bigr sizing (e.g. \\bigl[\\begin{smallmatrix}...\\bigr]). Converting the latter to bmatrix is wrong; needs delimiter/sizing context."
    ),
    "MATH-064": (
        "Bucket C: \\eqalign is a brace-delimited plainTeX macro used INSIDE math; converting to the align display environment is a structural rewrite (\\cr->newline, \\noalign handling, illegal-in-inline-math), not a byte edit."
    ),
    "MATH-102": (
        "Bucket C: eqnarray->align is a multi-site structural rewrite \u2014 eqnarray is 3-column (&=&) vs align's 2-column (&=), with nested \\begin{cases} needing per-row remapping. Not a mechanical env rename."
    ),
    "VERB-006": (
        "Bucket C (suggest_verbatim_env is advisory): converting inline \\verb to a verbatim environment is structural, and an unclosed \\verb makes the captured content span ambiguous."
    ),
    "VERB-010": (
        "Bucket C: \\verb is fragile and illegal inside moving arguments (\\section{`grep`} breaks); backtick-code cannot be mechanically injected as \\verb."
    ),
    "CMD-002": (
        "Bucket C: \\def -> \\renewcommand is not value-preserving \u2014 \\renewcommand errors if the target is undefined; the rule cannot know whether the macro pre-exists (else \\newcommand). Needs user choice."
    ),
    "CMD-011": (
        "Bucket C: the fix requires choosing \\makeatletter/\\makeatother placement (ambiguous), and the warning is often a false positive (\\def with no @). Not a deterministic edit."
    ),
    "BIB-011": (
        "Bucket C: moving note->url is ambiguous when a url field already exists or note holds non-URL prose; a correct migration depends on bib content/style. Interactive."
    ),
    "REF-006": (
        "Bucket C (suggest_pageref is an editor suggestion): \\ref vs \\pageref depends on author intent (render the number vs the page number); cannot be decided statically."
    ),
    "PKG-022": (
        "Bucket C: swapping an obsolete package (e.g. epsfig->graphicx) is not a drop-in \u2014 the old macros (\\epsfig) remain undefined. A correct migration rewrites call sites; needs user review."
    ),
    "CHEM-001": (
        "Bucket C: wrapping a formula in \\ce needs semantic judgment \u2014 $H_2$ may be a Hamiltonian component, $E_0$ a ground-state energy, $T_2$ a relaxation time. The regex matches any letter+subscript; auto-wrapping corrupts non-chemistry."
    ),
    # === v27.1.13: 5 more Bucket-C, confirmed during the Bucket-A shipping
    #     audit (agents proved a concrete corruption case for each) ===
    "FR-008": (
        "Bucket C: the detector matches 'oe' by whole-document substring (not word/token boundary), so it fires on ANY 'oe' (does, poet, coefficient); replacing all with the ligature oe corrupts non-French / non-ligature words. A correct fix needs a French word list or morphology."
    ),
    "MATH-101": (
        "Bucket C: the detector counts EVERY bare \\over (incl. chained {a \\over b \\over c}, brace-less 'a \\over b' spanning the whole formula, nested groups); \\over->\\frac needs unambiguous numerator/denominator parsing those cases do not admit. Only a narrow single-group subset (which the detector does not isolate) is deterministic."
    ),
    "MATH-052": (
        "Bucket C: suggest_frac is advisory and its detection set is a STRICT SUBSET of MATH-101's \\over detection; the same numerator/denominator ambiguity applies. The interactive \\frac suggestion is the intended surface."
    ),
    "MATH-025": (
        "Bucket C: the detector gates only on absence of '&' (column alignment), NOT on absence of row breaks; a multi-row single-column align (a // b // c) converted to the single-line equation environment breaks. A safe fix needs an extra single-row check."
    ),
    "ZH-001": (
        "Bucket C: fires on any ASCII '.' after a CJK glyph, but that '.' may be a sentence period (->U+3002) OR a filename/identifier dot (\\includegraphics{fig.pdf} with a CJK stem, name.tex); replacing the latter corrupts the path. Needs sentence-vs-token context."
    ),
}

# === v27.0.46: Reserved rules from rules_v3.yaml ===
# These rules have maturity=Reserved — they exist as placeholders in the
# catalogue for future spec work but have no runtime implementation, no
# definition beyond a one-line description, and no test cases.  Annotate
# them as produces_fix:false with a clear reason so the FIX_PRODUCER_LEDGER
# does not list them as Bucket-A-pending (they are not pending; they are
# spec placeholders).  Identifies any future drift between rules_v3.yaml
# maturity and the produces_fix annotation.
_RESERVED_REASON = (
    "⟦Reserved⟧ — rules_v3.yaml maturity=Reserved.  Placeholder for "
    "future spec work; no rule definition or runtime implementation "
    "currently exists.  Will move to produces_fix:null/true once the "
    "spec is fleshed out and the rule is implemented."
)
for _rid in [
    "CHAR-001", "CHAR-002", "CHAR-003",
    "MATH-001", "MATH-002", "MATH-003", "MATH-004", "MATH-005",
    "MATH-007", "MATH-008",
    "PDF-001", "PDF-002", "PDF-003", "PDF-004",
]:
    FIX_PRODUCER_DEFERRED[_rid] = _RESERVED_REASON

# Bucket D — defer indefinitely per V27_FIX_PRODUCER_CADENCE.md §"Bucket D".
# Rules in these families do not admit a static fix (they require pdflatex
# runtime state, compile log diagnostics, or external-binary file inspection).
BUCKET_D_FAMILIES: set[str] = {"FIG", "FONT", "PDF", "L3", "SYS"}
BUCKET_D_REASON = (
    "Bucket D (cadence plan §Bucket D): defer indefinitely.  Rule depends "
    "on pdflatex runtime / compile-log / external-binary state and cannot "
    "be statically fix-produced from the source bytes alone."
)

# Class C rule IDs — sourced from latex-parse/src/execution_class.ml.
# Kept in sync with runtime list; drift-checked by check_rule_contracts.py.
CLASS_C_RULE_IDS = {
    "FIG-020",
    "LAY-001", "LAY-002", "LAY-003", "LAY-004",
    "LAY-006", "LAY-009", "LAY-011",
    "LAY-017", "LAY-018", "LAY-021",
    "MATH-026", "MATH-027",
    "TIKZ-002",
    "LAY-025", "LAY-026", "LAY-027",
}

# Rules with formal_conditional proofs (BuildLog.v conditional theorems).
CONDITIONAL_PROOF_RULE_IDS = {"LAY-025", "LAY-026", "LAY-027"}

# Rules with formal_conservative proofs (L3 file-based rules).
CONSERVATIVE_PROOF_RULE_IDS = {
    "FIG-004", "FIG-006", "FIG-016", "FIG-021", "FIG-023",
    "COL-001", "COL-002", "COL-003", "COL-004", "COL-005", "COL-007",
    "PDF-006", "PDF-007", "PDF-008", "PDF-009", "PDF-011", "PDF-012",
    "TIKZ-002", "TIKZ-008", "CJK-007",
}

# ML-statistically-validated ambiguous rules.
ML_STATISTICAL_RULE_IDS = {
    "TYPO-001", "TYPO-005", "TYPO-012", "TYPO-028",
    "TYPO-048", "TYPO-052", "TYPO-056", "TYPO-062",
}

# Phase A (keystroke-critical) families: fast, local, deterministic.
# Gated additionally on precondition=L0 so that a family member at L2+
# stays at Class B even if the family prefix is in this set
# (e.g. STRUCT-005 is L2 AST-dependent even though STRUCT-001..004 are L0).
PHASE_A_FAMILIES = {"TYPO", "CHAR", "ENC", "SPC", "DELIM", "VERB", "STRUCT"}

# Phase D (advisory) families: style, ML-gated, language-specific heuristics.
PHASE_D_FAMILIES = {"STYLE"}

# PR #241 (p1.1-#4): PRJ-001..004 + PRT-001/002 + CMD-015/016/017 are
# now included in rules_v3.yaml (spec catch-up). No runtime-only back
# door needed.


def rule_family(rule_id: str) -> str:
    return rule_id.split("-", 1)[0] if "-" in rule_id else rule_id


def pick_phase(rule_id: str, precondition: str | None) -> str:
    """Choose execution class. Explicit Class C first; then by family."""
    if rule_id in CLASS_C_RULE_IDS:
        return "C"
    family = rule_family(rule_id)
    if family in PHASE_D_FAMILIES:
        return "D"
    if family in PHASE_A_FAMILIES:
        # A Phase-A family member stays Class A only at L0 — L2+ members
        # need debounce (Class B) because they rely on parser output.
        if precondition is None or precondition.startswith("L0"):
            return "A"
    # Default heuristic by layer: L0/L1 → B (debounce); L2/L3 → B; L4 already D.
    return "B"


def pick_proof_class(rule_id: str) -> str:
    if rule_id in CONDITIONAL_PROOF_RULE_IDS:
        return "formal_conditional"
    if rule_id in CONSERVATIVE_PROOF_RULE_IDS:
        return "formal_conservative"
    return "formal_faithful"


def pick_evidence_class(rule_id: str) -> str:
    if rule_id in ML_STATISTICAL_RULE_IDS:
        return "statistical_ml_bounded"
    if rule_id in CONDITIONAL_PROOF_RULE_IDS:
        return "compile_log_evidence"
    if rule_id in CONSERVATIVE_PROOF_RULE_IDS:
        return "external_binary_evidence"
    return "source_pattern_evidence"


def pick_project_scope(rule_id: str, phase: str) -> str:
    """LP-Core / any. Rules that require full build context are project-wide."""
    if phase == "C":
        return "any"  # Class C rules apply across tiers when build log present
    family = rule_family(rule_id)
    if family in {"REF", "LAB"}:
        return "any"  # cross-file concern
    return "lp_core_or_extended"


def pick_fix_scope(rule_id: str, severity: str | None) -> str:
    """Local vs document. Default: local for Warning/Info, document for Error."""
    if severity and severity.lower() == "error":
        return "document"
    return "local"


def load_rules_v3(repo: Path) -> list[dict]:
    path = repo / "specs/rules/rules_v3.yaml"
    with open(path, encoding="utf-8") as f:
        data = yaml.safe_load(f)
    return [r for r in data if isinstance(r, dict) and "id" in r]


def pick_produces_fix(rid: str) -> tuple[object, str | None]:
    """Return (produces_fix, fix_status_reason).

    - True: rule ships a fix producer in the OCaml runtime.
    - False: rule has explicit deferral reason (Bucket D, NLP, redundant, etc.).
    - None: rule is Bucket-A-pending (no decision yet).

    Per cadence plan acceptance criterion #3, every rule that *cannot* be
    fix-producing must surface here with a documented reason.  This is what
    flips the field from None → False.
    """
    if rid in SHIPPED_FIX_PRODUCERS:
        return True, None
    if rid in FIX_PRODUCER_DEFERRED:
        return False, FIX_PRODUCER_DEFERRED[rid]
    if rule_family(rid) in BUCKET_D_FAMILIES:
        return False, BUCKET_D_REASON
    return None, None


def build_contract(rule: dict) -> dict:
    rid = rule["id"]
    precondition = rule.get("precondition")
    phase = pick_phase(rid, precondition)
    proof_class = pick_proof_class(rid)
    evidence_class = pick_evidence_class(rid)
    project_scope = pick_project_scope(rid, phase)
    fix_scope = pick_fix_scope(rid, rule.get("default_severity"))
    produces_fix, fix_status_reason = pick_produces_fix(rid)

    # Layer from precondition: fed to Validator_dag.phase_of_string.
    # Default to L0 if missing (shouldn't happen for any current rule).
    layer = precondition or "L0_Lexer"

    contract: dict = {
        "rule_id": rid,
        "layer": layer,
        "execution_class": phase,
        "proof_class": proof_class,
        "evidence_class": evidence_class,
        "consumes": [],        # capabilities this rule reads (populated hand-audited below)
        "provides": [rid],     # self-provision (matches default_meta behaviour)
        "depends_on": [],      # rules this must run after (hand-audited below)
        "conflicts_with": [],  # competing rules (hand-audited below)
        "fix_scope": fix_scope,
        "project_scope": project_scope,
        "produces_fix": produces_fix,
    }
    # Only attach a reason when the rule is explicitly deferred.  Keeps the
    # YAML clean for "pending" rules where the decision hasn't been made.
    if fix_status_reason is not None:
        contract["fix_status_reason"] = fix_status_reason
    return contract


def _add_conflict(by_id: dict, a: str, b: str) -> None:
    """Symmetric conflict edge. Both rules declare the other."""
    for ra, rb in ((a, b), (b, a)):
        if ra in by_id:
            c = by_id[ra]
            if rb not in c["conflicts_with"]:
                c["conflicts_with"].append(rb)


# PR #241 (p1.3): family-level capability bindings. Each prefix produces or
# consumes the listed capabilities, turning the validator DAG from a set of
# isolated nodes into a real graph.
#
# Rationale per family:
#   LAB  provides label_index   (collects \label occurrences)
#   REF  consumes label_index   (must resolve references to labels)
#   BIB  provides bib_entries   (parses .bib / \bibitem)
#   CITE consumes bib_entries   (resolves \cite)
#   CMD  consumes post_expansion_commands (L1 expansion output)
#   ENV  consumes environment_events      (L2 AST env begin/end pairs)
#   MATH consumes math_mode_contexts      (L2 AST math regions)
#   FIG  consumes float_contexts          (L2 AST floats)
#   TAB  consumes float_contexts          (L2 AST floats)
#   VERB consumes verbatim_regions        (L0 verbatim lexer state)
#   STYLE consumes language_model         (Class D advisory, ML-informed)
#   STRUCT consumes document_structure    (document-level invariants)
FAMILY_CAPABILITIES: dict[str, dict[str, list[str]]] = {
    "LAB":    {"provides": ["label_index"]},
    "REF":    {"consumes": ["label_index"]},
    "BIB":    {"provides": ["bib_entries"]},
    "CITE":   {"consumes": ["bib_entries"]},
    "CMD":    {"consumes": ["post_expansion_commands"]},
    "ENV":    {"consumes": ["environment_events"]},
    "MATH":   {"consumes": ["math_mode_contexts"]},
    "FIG":    {"consumes": ["float_contexts"]},
    "TAB":    {"consumes": ["float_contexts"]},
    "VERB":   {"consumes": ["verbatim_regions"]},
    "STYLE":  {"consumes": ["language_model"]},
    "STRUCT": {"consumes": ["document_structure"]},
}


def hand_audit_overrides(contracts: list[dict]) -> None:
    """Apply hand-audited overrides for rules with non-trivial edges.

    Additions here should be minimal and well-justified. Every override must
    reference either a spec section or a known runtime dependency.
    """
    by_id = {c["rule_id"]: c for c in contracts}

    # PR #241 (p1.3): real conflict edges derived from pattern overlap.
    # Each pair below has verifiable-from-source conflict: one rule's
    # pattern is a prefix/subset of the other's so both fire on the
    # same span if enabled simultaneously.
    _add_conflict(by_id, "TYPO-002", "TYPO-003")  # `--` vs `---` (en vs em dash)
    _add_conflict(by_id, "TYPO-003", "TYPO-030")  # `---` vs `----+` (em-dash vs 4+ hyphens)
    _add_conflict(by_id, "TYPO-002", "TYPO-030")  # `--` inside `----+`
    _add_conflict(by_id, "TYPO-001", "TYPO-004")  # straight quote vs backtick-apostrophe
    _add_conflict(by_id, "TYPO-013", "TYPO-004")  # lone backtick vs backtick-pair
    # NOTE: ENC-002 and SPC-012 both detect "BOM at non-leading offset" — pre-
    # v27.0.46 both emitted IDENTICAL delete edits.  The redundant fix was
    # removed from SPC-012's runtime in v27.0.46 (it remains diagnostic-only).
    # We deliberately do NOT declare a `conflicts_with` edge here: the
    # diagnostic contract has been "both fire" since v26.3.0, and existing
    # test cases (test_validators_enc_char_spc.ml lines 324, 330, 437)
    # encode that behaviour.  Suppressing SPC-012's diagnostic would be a
    # behavioural regression for downstream consumers.  The conflict is fully
    # resolved at the fix-edit level by removing SPC-012's `~fix` arg.

    # PR #241 (p1.3): family-level capability edges. Every rule whose family
    # is in FAMILY_CAPABILITIES picks up provides/consumes defaults so the
    # DAG has meaningful structure. Per-rule overrides in this function can
    # still layer on top.
    for c in contracts:
        fam = rule_family(c["rule_id"])
        caps = FAMILY_CAPABILITIES.get(fam)
        if not caps:
            continue
        for cap in caps.get("provides", []):
            if cap not in c["provides"]:
                c["provides"].append(cap)
        for cap in caps.get("consumes", []):
            if cap not in c["consumes"]:
                c["consumes"].append(cap)

    # Class C rules consume compile_log_context (produced by Log_parser).
    for rid in CLASS_C_RULE_IDS:
        if rid in by_id:
            if "compile_log_context" not in by_id[rid]["consumes"]:
                by_id[rid]["consumes"].append("compile_log_context")

    # L3 file validators consume binary file metadata.
    for rid in CONSERVATIVE_PROOF_RULE_IDS:
        if rid in by_id:
            c = by_id[rid]
            if rid.startswith(("FIG-", "COL-")):
                cap = "image_metadata"
            elif rid.startswith("PDF-"):
                cap = "pdf_structure"
            elif rid.startswith("TIKZ-"):
                cap = "tikz_compile_times"
            elif rid.startswith("CJK-"):
                cap = "font_glyph_coverage"
            else:
                cap = "external_binary"
            if cap not in c["consumes"]:
                c["consumes"].append(cap)

    # ML-gated rules consume ml_confidence_map.
    for rid in ML_STATISTICAL_RULE_IDS:
        if rid in by_id:
            c = by_id[rid]
            if "ml_confidence_map" not in c["consumes"]:
                c["consumes"].append("ml_confidence_map")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--output",
        default=str(REPO_ROOT / "specs/rules/rule_contracts.yaml"),
    )
    ap.add_argument(
        "--repo",
        default=str(REPO_ROOT),
    )
    ns = ap.parse_args()

    repo = Path(ns.repo)
    rules = load_rules_v3(repo)
    contracts = [build_contract(r) for r in rules]
    hand_audit_overrides(contracts)

    # Stable ordering: by rule_id for deterministic diffs.
    contracts.sort(key=lambda c: c["rule_id"])

    output = {
        "version": "v26.1",
        "source": "scripts/tools/generate_rule_contracts.py",
        "input": "specs/rules/rules_v3.yaml",
        "total_rules": len(contracts),
        "rules": contracts,
    }

    with open(ns.output, "w", encoding="utf-8") as f:
        f.write(
            "# =====================================================================\n"
            "# rule_contracts.yaml — per-rule execution/proof/project metadata\n"
            "# Source of truth: this file. Regenerated by generate_rule_contracts.py.\n"
            "# Consumed by: latex-parse/src/rule_contract_loader.ml (via JSON mirror)\n"
            "# Memo reference: specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md §10\n"
            "# =====================================================================\n"
        )
        yaml.safe_dump(output, f, sort_keys=False, allow_unicode=True, width=120)

    # Also emit JSON mirror next to the YAML for OCaml runtime consumption.
    json_path = Path(ns.output).with_suffix(".json")
    with open(json_path, "w", encoding="utf-8") as jf:
        json.dump(output, jf, ensure_ascii=False, indent=2)
        jf.write("\n")
    print(f"[rule_contracts] wrote JSON mirror to {json_path}", file=sys.stderr)

    print(
        f"[rule_contracts] wrote {len(contracts)} contracts to {ns.output}",
        file=sys.stderr,
    )
    # Summary counts by phase/proof_class for sanity.
    phases = {}
    proofs = {}
    fix_states = {True: 0, False: 0, None: 0}
    for c in contracts:
        phases[c["execution_class"]] = phases.get(c["execution_class"], 0) + 1
        proofs[c["proof_class"]] = proofs.get(c["proof_class"], 0) + 1
        fix_states[c.get("produces_fix")] = fix_states.get(c.get("produces_fix"), 0) + 1
    print(f"[rule_contracts] by execution_class: {phases}", file=sys.stderr)
    print(f"[rule_contracts] by proof_class:     {proofs}", file=sys.stderr)
    print(
        f"[rule_contracts] produces_fix: true={fix_states[True]} "
        f"false={fix_states[False]} pending(null)={fix_states[None]}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
