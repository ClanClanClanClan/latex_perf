let prepare_gc () =
  let s0 = Gc.quick_stat () in
  Gc.compact ();
  let s1 = Gc.quick_stat () in
  (s0, s1)

let drain_major () = 
  let rec loop i =
    let s = Gc.quick_stat () in
    if s.major_words > 0.0 && i < 50 then (Gc.minor (); loop (i+1))
  in loop 0

let with_gc_cleaned f =
  drain_major ();
  Gc.minor ();
  f ()
