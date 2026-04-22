(** See [stable_spans.mli]. *)

type t = { start_offset : int; end_offset : int }

let make ~start_offset ~end_offset =
  if start_offset < 0 || end_offset < 0 then
    invalid_arg "Stable_spans.make: negative offset";
  if start_offset > end_offset then
    invalid_arg "Stable_spans.make: start_offset > end_offset";
  { start_offset; end_offset }

let zero offset = make ~start_offset:offset ~end_offset:offset
let length s = s.end_offset - s.start_offset
let is_empty s = length s = 0
let contains s p = s.start_offset <= p && p < s.end_offset

let disjoint s1 s2 =
  s1.end_offset <= s2.start_offset || s2.end_offset <= s1.start_offset

let substring src s =
  let src_len = String.length src in
  if s.start_offset < 0 || s.end_offset > src_len then
    invalid_arg "Stable_spans.substring: span exceeds source bounds";
  String.sub src s.start_offset (length s)

type edit = {
  edit_offset : int;
  edit_old_length : int;
  edit_new_length : int;
}

let damaged_by (e : edit) (s : t) : bool =
  let edit_end = e.edit_offset + e.edit_old_length in
  not (s.end_offset <= e.edit_offset || edit_end <= s.start_offset)

let shift_after (e : edit) (s : t) : t =
  let edit_end = e.edit_offset + e.edit_old_length in
  let delta = e.edit_new_length - e.edit_old_length in
  if s.end_offset <= e.edit_offset then s
  else if edit_end <= s.start_offset then
    { start_offset = s.start_offset + delta; end_offset = s.end_offset + delta }
  else
    (* Overlap — caller should not have shifted. Return as-is so we
       don't silently corrupt coordinates; damaged_by predicate lets
       callers detect this up front. *)
    s

let of_located (ln : Parser_l2.located_node) : t =
  make ~start_offset:ln.loc.offset ~end_offset:ln.loc.end_offset

let equal a b = a.start_offset = b.start_offset && a.end_offset = b.end_offset
let compare a b =
  let c = Int.compare a.start_offset b.start_offset in
  if c <> 0 then c else Int.compare a.end_offset b.end_offset

let to_string s = Printf.sprintf "[%d, %d)" s.start_offset s.end_offset
