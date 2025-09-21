open Bigarray
type kinds_t = (int32, int32_elt, c_layout) Array1.t
type offs_t  = (int32, int32_elt, c_layout) Array1.t
type codes_t = (int32, int32_elt, c_layout) Array1.t
type issues_t= (int32, int32_elt, c_layout) Array1.t

type buffers = { kinds:kinds_t; offs:offs_t; codes:codes_t; issues:issues_t; lines:offs_t; cols:offs_t; mutable next_ix:int }
type t = { a:buffers; b:buffers; mutable current:buffers; cap:int }

let create_buffers cap =
  let mk () = Array1.create Int32 c_layout cap in
  { kinds=mk (); offs=mk (); codes=mk (); issues=mk (); lines=mk (); cols=mk (); next_ix=0 }

let create ~cap =
  let a = create_buffers cap and b = create_buffers cap in
  { a; b; current=a; cap }

let swap t = t.current <- (if t.current==t.a then t.b else t.a); t.current.next_ix <- 0
let current t = t.current