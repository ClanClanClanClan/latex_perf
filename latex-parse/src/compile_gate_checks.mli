(** Precise structural-fatal compile-gate detectors.

    [structural_fatal_reasons source] returns one human-readable reason string
    per DETECTED hard-fatal condition (empty list ⇒ none detected). Each
    detector fires IFF pdflatex genuinely FAILS with no output PDF on its
    targeted deterministic-structural condition; every boundary was pinned
    empirically (see [test_compile_gate.ml] for the compiling-vs-failing
    counter-examples). Detectors are pure functions of the source bytes and are
    comment/verbatim/math-context aware via [Validators_common], so this is
    cheap and produces identical results on the fast and full readiness paths.

    Detectors in the gate:
    - (1) Double super/subscript in math (`x^a^b`, `x_a_b`, `x^b'`, …), not the
      compiling forms (`x^{a^b}`, `{x^a}^b`, `x^a_b`, `x''^b`). Skips
      comment/verbatim AND moving-argument keys (`\label{a_b}`, `\ref`, …).
    - (3) No `\documentclass` / `\documentstyle` anywhere in the source.
    - (4) `\usepackage` after the first `\begin{document}`.

    Detector (2) — misplaced alignment tab `&` — was DROPPED: although a stray
    `&` outside every alignment context IS fatal, a sound detector cannot avoid
    over-rejecting real compiling papers (custom \begin-less alignment-env
    shortcut macros like \bea/\bal, and `&` inside label/href arguments) without
    full macro expansion. See the implementation for the corpus evidence. *)

val structural_fatal_reasons : string -> string list

(**/**)

(* Exposed for the dedicated unit tests; not part of the stable surface. *)
val double_script_fatal : string -> string option
val no_documentclass_fatal : string -> string option
val usepackage_after_begin_fatal : string -> string option
val find_moving_arg_ranges : ?extra:string list -> string -> (int * int) list
val find_ref_alias_macros : string -> string list
