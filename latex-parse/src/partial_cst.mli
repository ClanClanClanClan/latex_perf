(** Partial CST: classify document parse state into trust zones.

    Formalizes the distinction between complete, partial, and broken document
    states. Error damage is bounded to the containing paragraph; regions outside
    error paragraphs are trusted. *)

type parse_confidence = Complete | Partial | Broken
type hole = { position : int; reason : string }

type trust_zone = {
  start_pos : int;
  end_pos : int;
  confidence : parse_confidence;
}

type partial_document = {
  confidence : parse_confidence;
  holes : hole list;
  trust_zones : trust_zone list;
  error_regions : (int * int * string) list;
}

val classify : string -> (string * Parser_l2.loc) list -> partial_document
(** [classify source errors] produces a partial document with trust zones.
    Errors are bounded to their containing paragraph. *)

val damage_radius : error_pos:int -> string -> int * int
(** [damage_radius ~error_pos source] returns [(start, end)] of the smallest
    enclosing paragraph boundary. *)

val confidence_to_string : parse_confidence -> string

val zone_conf_tag_complete : int
(** PR #241 (p1.3): numeric confidence tags packed into [Node_id.command_hash]
    so that zones with identical spans but different trust levels hash to
    distinct IDs. The values are stable — persisted consumers (collaboration
    anchors) can rely on them across releases. *)

val zone_conf_tag_partial : int
val zone_conf_tag_broken : int

val zone_id : trust_zone -> Node_id.t
(** PR #241 (p1.2, memo §6 E3): deterministic stable identifier for a trust
    zone. Computed via {!Node_id.of_located} over the zone's
    [(start_pos, end_pos, confidence)]. Consumers (collaboration anchors,
    incremental re-validation) can use these IDs to track a zone across edits.

    Proved stable under local edits in
    {!proofs/StableNodeIds.v::of_located_stable_under_local_edit}. *)
