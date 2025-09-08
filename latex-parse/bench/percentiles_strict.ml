let exact_with_index (arr: float array) (q: float) =
  let n = Array.length arr in
  if n=0 then invalid_arg "empty";
  let a = Array.copy arr in
  Array.sort compare a;
  let idx = max 0 (min (n-1) (int_of_float (ceil (float n *. q)) - 1)) in
  (idx, a.(idx))

let dump name samples =
  let n = Array.length samples in
  let pr q =
    let (idx, v) = exact_with_index samples q in
    Printf.printf "%s P%.3f idx=%d/%d val=%.3f ms\n%!" name (100.0*.q) idx n v
  in
  pr 0.50; pr 0.90; pr 0.95; pr 0.99; if n>=100_000 then pr 0.999