type t = { byte_start : int; byte_end : int }

let length { byte_start; byte_end } = byte_end - byte_start

let merge a b =
  if a.byte_end < b.byte_start || b.byte_end < a.byte_start then None
  else
    Some
      {
        byte_start = Int.min a.byte_start b.byte_start;
        byte_end   = Int.max a.byte_end   b.byte_end;
      }

let pp fmt { byte_start; byte_end } =
  Format.fprintf fmt "(%d,%d)" byte_start byte_end

(* Additional utility functions for DSL integration *)
let make start_pos end_pos = 
  { byte_start = start_pos; byte_end = end_pos }

let make_single pos = 
  { byte_start = pos; byte_end = pos + 1 }

let make_span start len = 
  { byte_start = start; byte_end = start + len }