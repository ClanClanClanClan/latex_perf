(** The closure-scoped strict-tier boundary scan (ADR-012, milestone M0).

    It reports every construct in the project closure for which the strict
    grammar of docs/v27/STRICT_TIER_DESIGN.md (section A.1.4) has no production:
    the constructs [Unsupported_feature] detects, plus [\expandafter], [\newif],
    [\ifthenelse] and every other [\if]-word except [\iff], the loop words,
    [\ExplSyntaxOn], the xparse definers, [\write], and control sequences
    containing [@]. A local [.sty] or [.cls] file in the closure is reported as
    a vendored style file and is not scanned inside. The [.bbl] is scanned when
    the root uses [\bibliography].

    The scan runs over [Compile_contract.closure_files], not the root string, so
    a construct in an [\input] child is found (OPEN-024's shape). Comments,
    verbatim and url targets are blanked first, keeping line numbers.

    The scan is DIAGNOSTIC in M0. It feeds the why-not-strict lines of the
    verdict and cannot change a READY or NOT-READY verdict or an exit code. *)

type finding = {
  category : string;  (** One of {!categories}. *)
  id : string;
      (** The [Unsupported_feature] id, or this module's own id for an addition
          (for example ["at_name"], ["if_other"], ["xparse"]). *)
  file : string;  (** The path relative to the root's directory. *)
  line : int;  (** 1-indexed line of the first use in [file]. *)
  count : int;  (** Number of uses of this id in [file]. *)
  construct : string;  (** For example ["\\def"]. *)
  nudge : string;  (** A fix-it suggestion for the author. *)
}

val categories : string list
(** Every category, in the priority order used to choose why-not-strict lines:
    foreign, def, let, xparse, atletter, local_style, expl3, conditional, loop,
    csname, expandafter, write. *)

val construct_of_feature_id : string -> string
(** The control sequence an [Unsupported_feature] id stands for. *)

val def_nudge : string -> int -> string option
(** [def_nudge src off] builds the concrete rewrite for a plain [\def] at byte
    [off] of [src], for example [\def\R{\mathbb R}] to
    [\newcommand{\R}{\mathbb R}]. [None] when [off] is not a [\def] followed by
    a control word and a brace. *)

val scan_file : display:string -> string -> finding list
(** Scan one file's contents. One finding per id, at its first use. *)

val scan_files : base_dir:string -> (string * string) list -> finding list
(** Scan [(path, contents)] pairs; style files are reported, not scanned. *)

val scan : Project_model.t -> root_src:string -> finding list
(** Scan the whole project closure of [proj]. *)

val why_not_strict : finding list -> Verdict.boundary list
(** At most [Verdict.max_why_not_strict] reasons: up to two findings of distinct
    categories, chosen by priority, followed by [Verdict.m0_boundary]. *)

val first_foreign : finding list -> finding option
(** The first finding in the foreign category, if any. *)
