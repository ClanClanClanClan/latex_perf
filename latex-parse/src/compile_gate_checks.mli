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
(** Detector (1): [Some reason] iff the source contains a fatal un-braced double
    super/subscript in math (e.g. [x^a^b]); [None] otherwise. *)

val no_documentclass_fatal : string -> string option
(** Detector (3): [Some reason] iff the source has no [\documentclass] /
    [\documentstyle]; [None] otherwise. *)

val usepackage_after_begin_fatal : string -> string option
(** Detector (4): [Some reason] iff a [\usepackage] appears after the first
    [\begin{document}]; [None] otherwise. *)

val duplicate_begin_document_fatal : string -> string option
(** Detector (8): [Some reason] iff two real [\begin{document}] anchors appear
    outside comment/verbatim (the second re-executes [\document] → "! LaTeX
    Error: Can be used only in preamble", pdflatex exit 1); [None] otherwise.
    Add-NOT-READY-only: a compiling document has exactly one. *)

val verb_broken_eol_fatal : string -> string option
(** Detector (9): [Some reason] iff a real inline [\verb]/[\verb*] argument is
    not closed by its delimiter before the line ends (pdflatex "! LaTeX Error:
    \verb ended by end of line", exit 1); [None] otherwise. Add-NOT-READY-only. *)

val thmtools_counter_collision_fatal : string -> string option
(** [thmtools_counter_collision_fatal source] — OPEN-002, the largest real-paper
    false-READY class. Fires iff, in the preamble, the first live load of
    [thmtools]/[thm-restate] precedes a shared-counter theorem declaration
    ([\newtheorem{X}[Y]{..}] or [\declaretheorem[..sibling=|numberlike=..]])
    with no [amsthm] load after it — a preamble-time pdflatex fatal under TeX
    Live >= 2025 ("Command \c@<name> already defined"). Held-out validated at FP
    0/30. Expects the CLOSURE-RESOLVED source (the load and the declarations
    routinely live in different files); degrades to root-only coverage on a
    plain string. Comment/verbatim/url ranges are blanked before scanning.
    Add-NOT-READY-only: no blanking behaviour can manufacture a false-READY;
    over-blanking the amsthm-after EXEMPTION conjunct (negative polarity) can
    cost an over-rejection, reachable only via vcu-scanner over-reach — see the
    polarity note in the implementation. *)

type sc_state = { sc_if_depth : int; sc_brace_depth : int }
(** Self-collision family (SC) — the engine-independent false-READY class.
    Per-file segment scanner + verdict, driven by the caller over the closure in
    splice order. [sc_scan_segment] tracks file-local TeX-conditional depth and
    brace-group depth (events only at 0/0 — guarded declarations are the
    measured FP hazard and never count; clamped, so mis-counts degrade to
    under-detection). [self_collision_verdict] fires on a theorem name declared
    twice (SC-A) or a [\newcommand{\theH<x>}] after counter [<x>] exists (SC-B,
    June-2022 kernel mechanism). Validated corpus-wide before implementation:
    fires 10/2,719, all 10 fail, FP 0. *)

val sc_initial : sc_state
(** Fresh per-file scanner state: both depths zero. One per FILE, carried across
    that file's spliced segments — never shared between files. *)

type sc_event =
  | Sc_counter_created of string
  | Sc_theh_defined of string
  | Sc_theorem_declared of string

val sc_scan_segment : sc_state -> string -> sc_state * sc_event list
(** Scan one comment-blanked segment under the given file state; returns the
    carried state and the depth-0 events, in order. The caller concatenates
    event lists across segments in SPLICE order (TeX's reading order) — SC-B's
    "strictly earlier" depends on it. *)

val self_collision_verdict : sc_event list -> string option
(** [Some reason] on the first SC-A duplicate theorem name or SC-B
    [\newcommand{\theH<x>}]-after-counter in the ordered event stream; [None]
    otherwise. Messages are prose with document-derived names lowercased, so
    nothing scrapeable leaks (the #561 lesson). *)

val find_moving_arg_ranges : ?extra:string list -> string -> (int * int) list
(** Byte ranges of moving/name-argument keys ([\label{..}], [\ref], [\href], …,
    plus any [?extra] command names) that must be skipped by the math detectors
    so their [_]/[^] in keys are not read as scripts. *)

val find_ref_alias_macros : string -> string list
(** Names of user-defined [\ref]-alias macros (e.g. [\newcommand{\reff}{\ref}])
    whose argument keys also carry moving-argument (skip) semantics. *)

val unbalanced_open_brace : string -> bool
(** True iff the content has a net-unclosed [{] group (escape- and
    comment/verbatim-aware; extra [}] is clamped, matching TeX's recovery). Used
    on sibling [.aux]/[.bbl] artefacts, whose imbalance is the deterministic "!
    File ended while scanning" fatal. *)

val source_uses_bibliography : string -> bool
(** True iff the source loads a bibliography via [\bibliography{..}] (which
    [\input]s [<jobname>.bbl]) outside any comment/verbatim. Excludes
    [\bibliographystyle]. *)
