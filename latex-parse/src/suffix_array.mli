(** Suffix array with O(log n) search for dirty-region detection (spec W46). *)

type t
type dirty_region = { start_pos : int; end_pos : int }

val build : string -> t
val search : t -> string -> int list
val find_dirty_regions : string -> string -> dirty_region list
