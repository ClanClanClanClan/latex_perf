(** AST → lossless CST conversion (v26.2 PR B1).

    Post-process strategy per ADR-008. Walks the [Parser_l2] output, annotating
    each located AST node with a span and wrapping AST-lossy constructs
    (commands, groups) in [CUnparsed] for byte-losslessness. Environments and
    math are lifted to structural CST variants.

    Byte-losslessness is the v26.2 guarantee:
    [Cst.serialize (of_source src) = src] for arbitrary [src].
    Structure-losslessness is deferred to PR B2 and scoped there. *)

val of_source : string -> Cst.t list
(** [of_source src] parses [src] via [Parser_l2.parse_located] and emits a
    byte-lossless CST. *)

val of_located : string -> Parser_l2.located_node list -> Cst.t list
(** [of_located src nodes] converts an already-parsed located AST into CST
    against [src]. Exposed for tests that want to exercise the builder with a
    synthetic AST. *)
