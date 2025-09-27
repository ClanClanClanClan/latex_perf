let enabled = ref false

let words () =
  let s = Gc.quick_stat () in
  s.minor_words +. s.major_words -. s.promoted_words

let with_no_alloc f =
  if not !enabled then f ()
  else
    let w0 = words () in
    let r = f () in
    let w1 = words () in
    if w1 -. w0 > 1.0 then
      prerr_endline
        (Printf.sprintf "⚠︎ alloc on hot path: +%.0f words" (w1 -. w0));
    r
