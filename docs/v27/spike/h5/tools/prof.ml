(* PROFILING ONLY (spike H.5 stage 1): samples the GC at the C boundary.
   PS_PROBE=S: a line every S seconds of wall time (checked every 256 external calls).
   PS_PROBE_DEEP=1: each line also forces a full major GC and measures the live words, the
   words reachable from the CURRENT state, and the stdin bytes not yet read. *)
let period = match Sys.getenv_opt "PS_PROBE" with Some s -> float_of_string s | None -> 0.
let deep = Sys.getenv_opt "PS_PROBE_DEEP" <> None
let calls = ref 0
let t0 = Unix.gettimeofday ()
let last = ref t0
let static_words = ref 0
let probe_cpu = ref 0.
let probe (st : Values.state) =
  let now = Unix.gettimeofday () in
  let c0 = Sys.time () in
  let extra =
    if deep then begin
      Gc.full_major ();
      let s = Gc.stat () in
      let r = Obj.reachable_words (Obj.repr st) in
      Printf.sprintf " live %d reach_state %d static %d other %d stdin_left %d"
        s.Gc.live_words r !static_words (s.Gc.live_words - r - !static_words)
        (Stdlib.List.length st.Values.st_io.Values.io_stdin)
    end else "" in
  let q = Gc.quick_stat () in
  Printf.eprintf "PROBE wall %.1f cpu %.2f ext %d minor %.0f promoted %.0f major %.0f minc %d majc %d heap %d top %d %s%s\n%!"
    (now -. t0) (Sys.time ()) !calls q.Gc.minor_words q.Gc.promoted_words q.Gc.major_words
    q.Gc.minor_collections q.Gc.major_collections q.Gc.heap_words q.Gc.top_heap_words
    (Parrayc.counters ()) extra;
  probe_cpu := !probe_cpu +. (Sys.time () -. c0);
  Printf.eprintf "PROBECOST %.2f\n%!" !probe_cpu;
  last := Unix.gettimeofday ()
let ext callp x args st =
  incr calls;
  if period > 0. && !calls land 255 = 0 && Unix.gettimeofday () -. !last >= period then probe st;
  Boundary.ext callp x args st
