(** Bounded user-macro subset: which [\newcommand] / [\renewcommand] /
    [\providecommand] definitions fall inside the v26 supported subset.

    The memo §10.4 (Macro registry) lists this module as a required deliverable
    alongside [User_macro_registry]. The classification logic lives here so that
    downstream consumers — compile-guarantee proofs, Rest_simple_expander, CLI
    warnings — can query subset membership without depending on the full
    registry. *)

type status =
  | In_subset
      (** Definition is within the v26 bounded subset — arity 0..9, body
          contains no forbidden features (no [\def], catcode mutation,
          [\csname…\endcsname], nested unbounded recursion). *)
  | Out_of_subset of string  (** Human-readable reason. *)

val classify : User_macro_registry.user_macro_def -> status
(** Classify a single definition against the v26 subset. *)

val is_in_subset : User_macro_registry.user_macro_def -> bool
(** Convenience: [classify] returned [In_subset]. *)

val reason : status -> string option
(** [Some msg] when [Out_of_subset msg]; [None] when [In_subset]. *)

val unsupported_features : string list
(** Enumerated forbidden body features that exclude a macro from the subset.
    Used by diagnostics to explain rejection. *)
