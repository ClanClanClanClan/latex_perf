(** Fix guard (R7-3) — withhold fixes that would rewrite LOAD-BEARING bytes.

    A fix producer asks "are these bytes ordinary prose?" via
    {!Validators_common.find_exempt_ranges}. That is a TYPOGRAPHY-SUPPRESSION
    contract and it is not the same question as "would rewriting these bytes
    change what TeX does?". TYPO-002 obeys the existing contract perfectly and
    still turns an include filename into [\input{fig–x}].

    Measured before this module existed (R7-INFRA-4, TL2026):
    - [good_accents_utf8] — the backtick in the grave-accent command IS the
      command; rewritten to U+2018 it becomes an undefined-control-sequence
      error.
    - [good_tikz_simple] — a double hyphen inside a TikZ path is pgf's line-to
      OPERATOR; rewritten to an en dash, tikz gives up on the path and emits a
      fatal error.

    In both cases [--compile-check] reports READY before AND after, so the fixer
    MANUFACTURES a false-READY — the project's cardinal bug, created by the tool
    that was asked to improve the document.

    {2 Error polarity — note the inversion}

    This is a SUBTRACTIVE filter over edits. A protected range that is too WIDE
    withholds a fix: functionality lost, nothing corrupted — safe. A range that
    is too NARROW or misplaced leaves load-bearing bytes exposed — corruption.

    That is the OPPOSITE polarity from the R7-1b feature-detection lesson, where
    blanking too much caused false-READYs. Do not carry that instinct over:
    here, when in doubt, protect MORE. The one exception is a MISPLACED range,
    which is neither wider nor narrower but simply wrong — see the [\lstinline]
    note in the implementation. *)

val protected_ranges : string -> (int * int) list
(** [protected_ranges src] — half-open byte ranges of [src] whose contents are
    syntax rather than prose, so a textual fix must not touch them. Ranges are
    returned in ascending order of start offset and may be adjacent; they are
    not guaranteed disjoint. *)

val filter : src:string -> Cst_edit.t list -> Cst_edit.t list
(** [filter ~src edits] — drop every edit whose half-open span intersects a
    protected range of [src].

    The whole half-open span from [start_offset] to [end_offset] is tested, not
    just the start offset: an edit beginning one byte before a protected region
    and ending inside it would otherwise slip through. A pure insertion
    ([start_offset = end_offset]) is tested as a point.

    Call this against the CURRENT buffer on every pass of the converge loop, not
    once against the original source. Producers cascade: SCRIPT-007 was measured
    firing on pass 2 against a subscript SCRIPT-001 had itself synthesised
    inside a label key. Neither producer is wrong alone, so only re-evaluation
    against the rewritten bytes can catch it. *)
