(** Float/figure position tracking (spec W58). *)

type float_entry = {
  kind : string;
  label : string option;
  position : int;
  line : int;
}

type ref_entry = { key : string; position : int; line : int }

type float_distances = {
  entries : (float_entry * ref_entry * int) list;
  max_distance : int;
  before_first_ref : float_entry list;
}

val extract_floats : string -> float_entry list
val extract_refs : string -> ref_entry list
val compute_distances : string -> float_distances
