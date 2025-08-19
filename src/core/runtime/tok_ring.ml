(* Token Ring Buffer - Phase 1 of L0 Lexer Track A Optimization *)
(* Eliminates List.rev_append overhead (33% of runtime) *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist

type t = {
  mutable buf : Lexer_v25.token array;
  mutable len : int;
  mask        : int;  (* power-of-two capacity - 1 for fast modulo *)
}

let create cap =
  (* Find next power of 2 >= cap *)
  let rec next_pow2 n = if n >= cap then n else next_pow2 (n * 2) in
  let n = next_pow2 1 in
  { buf = Array.make n (Lexer_v25.TChar (Uchar.of_int 0, Catcode.Escape));
    len = 0; 
    mask = n - 1 }

let[@inline] push r tok =
  if r.len >= Array.length r.buf then
    failwith "TokRing overflow - increase capacity";
  let i = r.len land r.mask in
  Array.unsafe_set r.buf i tok;
  r.len <- r.len + 1

let[@inline] unsafe_get r i = 
  Array.unsafe_get r.buf (i land r.mask)

let[@inline] length r = r.len

(* Convert ring to list - called once at end *)
let to_list r =
  let out = Array.make r.len (Lexer_v25.TEOF) in
  for i = 0 to r.len - 1 do
    Array.unsafe_set out i (unsafe_get r i)
  done;
  Array.to_list out