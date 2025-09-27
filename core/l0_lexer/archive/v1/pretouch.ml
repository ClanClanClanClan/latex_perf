external mlock_all : unit -> unit = "ocaml_mlock_all"

let touch_memory (ba : ('a, 'b, 'c) Bigarray.Array1.t) ~len =
  let page_size = 4096 in
  let rec loop offset =
    if offset < len then
      let _dummy = Bigarray.Array1.unsafe_get ba offset in
      loop
        (offset
        + (page_size / Bigarray.kind_size_in_bytes (Bigarray.Array1.kind ba)))
  in
  loop 0

let pre_touch_ba_prefix
    (ba :
      (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t)
    ~est_tokens =
  let bytes_per_token = 12 in
  let len = min (est_tokens * bytes_per_token) (Bigarray.Array1.dim ba) in
  touch_memory ba ~len

let enable_memory_locking () = try mlock_all () with _ -> ()
