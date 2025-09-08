(* src/metrics.ml *)
type hist = { buckets:int array; max_ms:int; bucket_ms:int; mutable count:int }

let create ~max_ms ~bucket_ms =
  { buckets = Array.make ((max_ms / bucket_ms) + 1) 0; max_ms; bucket_ms; count=0 }

let observe_ms h (ms:float) =
  let ix = int_of_float (ms /. float h.bucket_ms) in
  let ix = min ix (Array.length h.buckets - 1) in
  h.buckets.(ix) <- h.buckets.(ix) + 1; h.count <- h.count + 1

let percentile h p =
  let target = int_of_float (ceil (p *. float h.count)) in
  let rec loop acc i =
    if i >= Array.length h.buckets then float h.max_ms
    else
      let acc = acc + h.buckets.(i) in
      if acc >= target then float (i * h.bucket_ms) else loop acc (i+1)
  in loop 0 0