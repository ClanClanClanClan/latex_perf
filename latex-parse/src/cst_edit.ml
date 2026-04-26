(** See [cst_edit.mli]. *)

type t = { start_offset : int; end_offset : int; replacement : string }

let make ~start_offset ~end_offset ~replacement =
  if start_offset < 0 then invalid_arg "Cst_edit.make: negative start_offset";
  if end_offset < start_offset then
    invalid_arg "Cst_edit.make: end_offset < start_offset";
  { start_offset; end_offset; replacement }

let insert ~at s = make ~start_offset:at ~end_offset:at ~replacement:s

let delete ~start_offset ~end_offset =
  make ~start_offset ~end_offset ~replacement:""

let replace ~start_offset ~end_offset s =
  make ~start_offset ~end_offset ~replacement:s

let span e =
  Stable_spans.make ~start_offset:e.start_offset ~end_offset:e.end_offset

let delta e = String.length e.replacement - (e.end_offset - e.start_offset)
let is_insertion e = e.start_offset = e.end_offset

let conflicts a b =
  if is_insertion a && is_insertion b then false
  else
    (* Overlap on pre-edit ranges. Two edits [s1,e1) and [s2,e2) overlap iff s1
       < e2 && s2 < e1. Insertions at a position touch [p,p); they don't
       conflict with each other, but they DO conflict with a replacement whose
       range strictly contains the insertion point (s < p < e). Treat insertions
       as zero-width: they conflict if strictly inside another edit's range. *)
    let sa, ea = (a.start_offset, a.end_offset) in
    let sb, eb = (b.start_offset, b.end_offset) in
    if is_insertion a then sb < sa && sa < eb
    else if is_insertion b then sa < sb && sb < ea
    else sa < eb && sb < ea

let rec validate_non_overlapping = function
  | [] | [ _ ] -> Ok ()
  | e :: rest -> (
      let conflict = List.find_opt (fun f -> conflicts e f) rest in
      match conflict with
      | Some f -> Error (e, f)
      | None -> validate_non_overlapping rest)

let apply_single src e =
  let n = String.length src in
  if e.start_offset < 0 || e.end_offset > n then
    invalid_arg "Cst_edit.apply_single: edit out of source bounds";
  let buf = Buffer.create (n + String.length e.replacement) in
  Buffer.add_substring buf src 0 e.start_offset;
  Buffer.add_string buf e.replacement;
  Buffer.add_substring buf src e.end_offset (n - e.end_offset);
  Buffer.contents buf

(* Apply multiple edits in one pass, over the pre-edit source. The edits are
   sorted ascending by start_offset, disjoint (validated upstream), and emitted
   in order so the resulting string contains each replacement at the correct
   spot. *)
let apply_all src edits =
  match validate_non_overlapping edits with
  | Error (a, b) -> Error (`Overlap (a, b))
  | Ok () ->
      let n = String.length src in
      let sorted =
        List.sort (fun a b -> Int.compare a.start_offset b.start_offset) edits
      in
      let buf = Buffer.create (n + 16) in
      let cursor = ref 0 in
      List.iter
        (fun e ->
          if e.end_offset > n then
            invalid_arg "Cst_edit.apply_all: edit exceeds source length";
          if !cursor < e.start_offset then
            Buffer.add_substring buf src !cursor (e.start_offset - !cursor);
          Buffer.add_string buf e.replacement;
          cursor := e.end_offset)
        sorted;
      if !cursor < n then Buffer.add_substring buf src !cursor (n - !cursor);
      Ok (Buffer.contents buf)

(* v26.4 §1.1: conflict-aware merging. Walk the input edit list in order; an
   edit lands in [applied] iff it doesn't conflict with anything already in
   [applied]; otherwise it lands in [skipped]. The output is [apply_all src
   applied] — guaranteed to succeed because applied was built to be pairwise
   non-conflicting. *)
let apply_best_effort src edits =
  let rec partition acc_applied acc_skipped = function
    | [] -> (List.rev acc_applied, List.rev acc_skipped)
    | e :: rest ->
        if List.exists (fun a -> conflicts e a) acc_applied then
          partition acc_applied (e :: acc_skipped) rest
        else partition (e :: acc_applied) acc_skipped rest
  in
  let applied, skipped = partition [] [] edits in
  match apply_all src applied with
  | Ok out -> (out, applied, skipped)
  | Error _ ->
      (* Internal invariant: [applied] is pairwise non-conflicting by
         construction, so [apply_all] cannot return Overlap here. *)
      invalid_arg
        "Cst_edit.apply_best_effort: applied subset has conflicts (BUG)"

let apply_with_priority src priority edits =
  (* Stable sort by descending priority so equal-priority edits keep input
     order. *)
  let prioritised =
    List.stable_sort (fun a b -> Int.compare (priority b) (priority a)) edits
  in
  apply_best_effort src prioritised

let shift_after ~by ~at_or_after e =
  let shift x = if x >= at_or_after then x + by else x in
  {
    e with
    start_offset = shift e.start_offset;
    end_offset = shift e.end_offset;
  }

let equal a b =
  a.start_offset = b.start_offset
  && a.end_offset = b.end_offset
  && a.replacement = b.replacement

let compare a b =
  let c = Int.compare a.start_offset b.start_offset in
  if c <> 0 then c
  else
    let c = Int.compare a.end_offset b.end_offset in
    if c <> 0 then c else String.compare a.replacement b.replacement

let to_string e =
  Printf.sprintf "replace[%d, %d) with %S" e.start_offset e.end_offset
    e.replacement
