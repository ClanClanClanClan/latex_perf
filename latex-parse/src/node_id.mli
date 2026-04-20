(** Deterministic stable identifier for AST nodes. PR #241 (memo §6 E3).

    Binds the abstract [Record node_id] from [proofs/StableNodeIds.v] to the
    real [Parser_l2.located_node] values without touching every record literal
    in the parser. Consumers that need node identity outside a span's mutable
    offset (e.g. collaboration anchors, rewrite engine) call [of_located] at the
    use site. *)

type t = { offset : int; length : int; command_hash : int }

val of_located : node_length:int -> command_hash:int -> Parser_l2.loc -> t
(** [of_located ~node_length ~command_hash loc] constructs a stable node_id. The
    [node_length] is the byte length of the node at [loc]; [command_hash] is a
    stable hash of the node's command name (or 0 for non-command nodes).

    Stability: under any edit that is either strictly before [loc] or strictly
    after [loc + node_length], the content pair [(length,
    command_hash)] is
    preserved. The offset may shift; that is proved invariant in
    [proofs/StableNodeIds.v::stable_node_id_under_local_edit]. *)

val content_id : t -> int * int
(** [content_id t] returns the edit-stable component [(length, command_hash)].
    Matches the Coq [content_id] projection. *)

val hash64 : t -> int
(** [hash64 t] mixes the three fields into a single 63-bit OCaml int. Used by
    consumers that want a single-value identifier. Collision resistance is
    best-effort; consumers that need cryptographic uniqueness must layer their
    own scheme. *)

val equal : t -> t -> bool
val compare : t -> t -> int
