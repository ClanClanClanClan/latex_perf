let pre_touch_bytes (b : bytes) ~page =
  let n = Bytes.length b in
  let step = min page 8192 in
  (* Cap step size to reduce variance *)
  let rec loop i =
    if i < n then (
      ignore (Bytes.unsafe_get b i);
      loop (i + step))
  in
  loop 0

let pre_touch_ba_1 (type a b) (ba : (a, b, Bigarray.c_layout) Bigarray.Array1.t)
    ~(elem_bytes : int) ~(elems : int) ~(page : int) =
  let open Bigarray in
  let dim = Array1.dim ba in
  let n = min elems dim in
  let step = max 1 (page / elem_bytes) in
  let rec loop i =
    if i < n then (
      ignore (Array1.unsafe_get ba i);
      loop (i + step))
  in
  loop 0
