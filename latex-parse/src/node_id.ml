(** Stable node identifier. See [node_id.mli]. *)

type t = { offset : int; length : int; command_hash : int }

let of_located ~node_length ~command_hash (loc : Parser_l2.loc) : t =
  { offset = loc.offset; length = node_length; command_hash }

let content_id (t : t) : int * int = (t.length, t.command_hash)

(* Mix via FNV-1a-style deterministic fold; stays within OCaml's native 63-bit
   int range on 64-bit systems. Platform-agnostic; consumers that need
   cryptographic uniqueness must layer their own scheme. *)
let mix_step a b =
  let a = a lxor b land max_int in
  let a = a * 16777619 land max_int in
  a lxor (a lsr 31)

let hash64 (t : t) : int =
  (* Seed with FNV offset basis truncated to 63 bits. *)
  let h = 0x27D4EB2F165667B1 land max_int in
  let h = mix_step h t.offset in
  let h = mix_step h t.length in
  mix_step h t.command_hash

let equal (a : t) (b : t) : bool =
  a.offset = b.offset && a.length = b.length && a.command_hash = b.command_hash

let compare (a : t) (b : t) : int =
  let c = Int.compare a.offset b.offset in
  if c <> 0 then c
  else
    let c = Int.compare a.length b.length in
    if c <> 0 then c else Int.compare a.command_hash b.command_hash
