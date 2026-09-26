(** The single verdict type of the compile check, and its only renderer.

    ADR-012 (docs/v27/adr/ADR-012-contract-bounded-proven-tier.md) splits every
    compile-check answer into three tiers. The PROVEN tier is an exact decision
    that a Coq theorem ties to a declarative semantics; the HEURISTIC tier is
    everything the pipeline does today; and FOREIGN is a document that uses a
    construct outside every supported tier. See docs/v27/STRICT_TIER_DESIGN.md
    section D.1.

    The one invariant this module exists to keep is: the verdict KIND field of
    the TIER line (its third tab-separated field) is [PROVEN-READY] or
    [PROVEN-NOT-READY] if and only if the verdict is a [Proven_] constructor. It
    is kept by construction. The kind field is produced only by this module's
    renderer, from a fixed token per constructor, and the reserved word is
    written only in the proven branch. User data (a file name, a macro name, a
    nudge built from the author's source) is never rewritten: it is shown
    verbatim inside double-quoted fields by {!quote}, whose only change is to
    show control characters in TeX's ^^ notation, so that a user datum can never
    add a field or a line. A user path may therefore contain the word PROVEN and
    the output will show it; the kind field still cannot. A unit test in
    [test_verdict.ml] checks the invariant on every constructor, including
    adversarial user data containing tabs, newlines and the reserved word.

    In milestone M0 nothing constructs a [Proven_] value: the strict-tier
    membership predicate is a stub that returns false, so the pipeline can only
    produce [Likely_ok], [Likely_fail] and [Foreign]. *)

type loc = { file : string; line : int; col : int }

(** The decided failure modes of the strict tier (design section C.2). Each
    constructor will be tied to a probe family. None is decided in M0. *)
type fatal_reason =
  | E0_no_pdf
  | E1_undefined_cs
  | E2_undefined_env
  | E3_mode_violation
  | E4_double_script
  | E5_stack_discipline
  | E6_par_in_math_or_short_arg
  | E7_missing_argument
  | E8_definer_clash
  | E9_unknown_counter
  | E10_missing_file
  | E11_unicode_undefined
  | E12_configuration_fatal
  | E13_bad_argument
  | E14_capacity_overflow

val e_code : fatal_reason -> string
(** [e_code r] is the stable short code, for example ["E3"]. *)

val all_fatal_reasons : fatal_reason list
(** Every constructor of [fatal_reason], in code order. *)

type boundary = {
  b_kind : string;
  b_where : string option;
  b_construct : string option;
  b_uses : int;
  b_nudge : string;
}
(** One reason why a document is not in the strict tier, with a nudge the author
    can act on. [b_kind] is a stable identifier, for example ["def"] or
    ["strict_unavailable"]. [b_where] is ["file:line"] and [b_construct] the
    construct as written, both user data, rendered verbatim inside {!quote}.
    [b_uses] is the number of uses (shown when above 1). [b_nudge] is the
    producer's text; any user datum inside it must already be {!quote}d. *)

type t =
  | Proven_ready of { contract : string; pin : string; decider : string }
  | Proven_not_ready of {
      reason : fatal_reason;
      message : string;
      loc : loc;
      rule : string;
      probe : string;
      contract : string;
    }
  | Pending of { predicted : [ `Ready | `Not_ready ]; missing : string list }
      (** Heuristic: a prediction from package contracts while the exact
          configuration is being attested. *)
  | Likely_ok of { basis : string; why_not_strict : boundary list }
      (** Heuristic READY. [basis] is, for example, ["premise-certified"]. *)
  | Likely_fail of {
      reasons : Compile_contract.reason list;
      why_not_strict : boundary list;
    }  (** Heuristic NOT-READY with its blocking reasons. *)
  | Foreign of {
      construct : string;
      where : string option;
      legacy_ready : bool;
      why_not_strict : boundary list;
    }
      (** The document uses a construct outside every supported tier, anywhere
          in its closure. [legacy_ready] is true when the unchanged heuristic
          answer is READY (exit code 0): in M0 the exit code is not changed, and
          the headline then says that exit 0 is the legacy READY and does not
          place the document in any tier. *)

val is_proven : t -> bool
(** [is_proven v] is true exactly for the two [Proven_] constructors. *)

val tier_token : t -> string
(** The machine token of the tier: ["proven"], ["heuristic"] or ["foreign"]. *)

val kind_token : t -> string
(** The machine token of the verdict: ["PROVEN-READY"], ["PROVEN-NOT-READY"],
    ["PENDING"], ["LIKELY-OK"], ["LIKELY-FAIL"] or ["FOREIGN"]. It is a fixed
    token per constructor and never contains user data. *)

val headline : t -> string
(** The one human-facing verdict sentence. Every non-proven headline says that
    it is not a proof. *)

val render : t -> string list
(** The full rendering, one string per output line, without newlines. The first
    line is [TIER <tab> tier_token <tab> kind_token <tab> headline]. It is
    followed by at most three indented ["why not strict:"] lines for a
    non-proven verdict. *)

val max_why_not_strict : int
(** At most this many why-not-strict lines are rendered (3). *)

val reserved_word : string
(** The word only a proven verdict's kind field may carry: ["PROVEN"]. The fixed
    text of a non-proven rendering never contains it; user data inside a quoted
    field may. *)

val quote : string -> string
(** [quote s] is [s] between double quotes, byte for byte, except that each
    control character is shown in TeX's ^^ notation (tab = [^^I], newline =
    [^^J], DEL = [^^?]). It never rewrites any other byte. *)

val require_proof_exit : int
(** The exit code of [--require-proof] when the verdict is not proven: 4. *)

val m0_boundary : boundary
(** The why-not-strict reason every document carries in M0: the strict tier does
    not exist yet, so no document can be decided by proof. *)
