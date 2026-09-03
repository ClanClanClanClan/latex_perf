(* ══════════════════════════════════════════════════════════════════════
   Texmf_tree_allowlist — OPEN-040 (2026-09-04)

   \input targets that resolve in the PINNED TeX Live tree (pdfTeX
   3.141592653-2.6-1.40.29 / TeX Live 2026) and therefore need no local copy:
   pdflatex compiles a minimal document \input'ing each name with NO local file
   present — every entry verified end-to-end under the pin, BOTH protocols, plus
   a %-catcode-leak probe (no entry changes comment semantics). T2's
   missing-file check must not reject them.

   MEMBERSHIP RULES (each measured, see OPEN-040): - EXACT-BYTE match only.
   kpsewhich misses XY/AMSSYM.DEF and pdflatex FATALS on [\input XY] even with
   texmf_casefold_search=1 — a case-folded match would manufacture false-READYs.
   - [\input] edges ONLY. [\include{xy}] resolves in-tree yet FATALS
   ("\xylet@..." — \include's \clearpage machinery is incompatible). - PREAMBLE
   position only (checked by the caller): body-position [\input xy] / [\input
   xypic] are fatal; all 28 real-frame occurrences sit in the preamble, so the
   gate costs zero rescues. - [pictex] is deliberately ABSENT: kpsewhich
   resolves it but the minimal doc is rc 1,1 ("! Undefined control sequence
   \fiverm") — its one frame paper compiles only via a bespoke \def\fiverm
   preamble, a context-dependent load that fails the doc-independent rule.

   Static data, no runtime kpsewhich: determinism and the proofs' purity are
   preserved. Rolled only with the oracle pin (§5.12). *)

let names =
  [
    "amssym.def";
    "colordvi";
    "epsf";
    "epsf.sty";
    "pdf-trans";
    "pictexwd.tex";
    "postpictex";
    "prepictex";
    "xy";
    "xypic";
  ]

let mem (name : string) : bool = List.mem name names
