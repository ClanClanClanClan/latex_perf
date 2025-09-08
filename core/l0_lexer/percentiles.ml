let exact (arr: float array) (q: float) =
  let n = Array.length arr in
  let a = Array.copy arr in
  Array.sort compare a;
  let idx = max 0 (min (n-1) (int_of_float (ceil (float n *. q)) - 1)) in
  a.(idx)

type tail_trace = (float * string) list  (* (ms, meta) *)
let keep_slowest n (xs:tail_trace) =
  let sorted = List.sort (fun (a,_) (b,_) -> compare b a) xs in
  let rec take n lst acc =
    match n, lst with
    | 0, _ | _, [] -> List.rev acc
    | n, h::t -> take (n-1) t (h::acc)
  in
  if List.length sorted <= n then sorted else take n sorted []
