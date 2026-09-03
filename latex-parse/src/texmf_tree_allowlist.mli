val names : string list
(** The pin-verified tree-file allowlist — see the .ml header for the membership
    rules (exact-byte, \input-only, preamble-gated at the caller, every entry
    compile-verified under the pinned engine with no local copy). *)

val mem : string -> bool
(** [mem name] — exact-byte membership in [names]. *)
