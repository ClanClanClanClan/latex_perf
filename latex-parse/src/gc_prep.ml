let words_total () =
  let s = Gc.quick_stat () in
  s.minor_words +. s.major_words

let last_full = ref 0.0

let drain_major ?(slice = 2_048) () =
  let rec loop () = if Gc.major_slice slice <> 0 then loop () in
  loop ()

let prepay () =
  let delta_words = words_total () -. !last_full in
  let delta_mb = delta_words *. (float Sys.word_size /. 8.0) /. 1_048_576.0 in
  if delta_mb >= float Config.gc_full_major_budget_mb then (
    Gc.minor ();
    drain_major ();
    last_full := words_total ())

let init_gc () =
  let g = Gc.get () in
  Gc.set
    {
      g with
      minor_heap_size = Config.minor_heap_bytes;
      space_overhead = Config.gc_space_overhead;
      max_overhead = Config.gc_max_overhead;
      allocation_policy = 1;
    };
  drain_major ();
  last_full := words_total ()
