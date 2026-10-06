(* STANDING RETENTION PROBE (spike H.5 stage 2; H5-heap-design.md §2.1, §5 B). A test
   instrument, never linked into the model build: retention_probe.sh links it into a COPY of an
   extracted tree, around the C boundary (Main0's `ext` argument), with nothing else changed.

   Every PS_RETPROBE_CPU seconds of CPU (checked every 256 external calls) it forces a full
   major GC and splits the live words into
     reach_state  the words reachable from the state the program is computing with now,
     static       the words reachable from the procedure table (the program's constants),
     other        live - reach_state - static: data that is live, but NOT reachable from the
                  current state. Before B2 this was 211-245 M words at the end of the format
                  load: old states kept alive by the fuel closures (§2.1).
   A probe whose `other` exceeds PS_RETPROBE_LIMIT words (default 1,000,000 = 8 MB) stops the
   run with exit 6 and the line RETPROBE FAIL. (static and reach_state can overlap, so a small
   negative `other` means nothing is retained: B2 measured -0.28 M at every probe.) *)
let period = match Sys.getenv_opt "PS_RETPROBE_CPU" with Some s -> float_of_string s | None -> 0.
let limit = match Sys.getenv_opt "PS_RETPROBE_LIMIT" with Some s -> int_of_string s | None -> 1_000_000
let static_words = ref 0
let calls = ref 0
let probes = ref 0
let next = ref period

let probe ?(final = false) (st : Values.state) =
  Gc.full_major ();
  let s = Gc.stat () in
  let r = Obj.reachable_words (Obj.repr st) in
  let other = s.Gc.live_words - r - !static_words in
  if not final then incr probes;
  Printf.eprintf "RETPROBE %s n %d cpu %.2f ext %d live %d reach_state %d static %d other %d limit %d top %d\n%!"
    (if final then "final" else "run") !probes (Sys.time ()) !calls s.Gc.live_words r !static_words other
    limit s.Gc.top_heap_words;
  if (not final) && other > limit then begin
    Printf.eprintf "RETPROBE FAIL: %d words live but not reachable from the current state (limit %d)\n%!"
      other limit;
    exit 6
  end

let ext callp x args st =
  incr calls;
  if period > 0. && !calls land 255 = 0 && Sys.time () >= !next then begin
    probe st;
    next := Sys.time () +. period
  end;
  Boundary.ext callp x args st
