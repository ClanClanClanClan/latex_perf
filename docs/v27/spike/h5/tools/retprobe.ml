(* STANDING RETENTION PROBE (spike H.5 stage 2; H5-heap-design.md §2.1, §5 B, §8.2). A test
   instrument, never linked into the model build: retention_probe.sh links it into a COPY of an
   extracted tree, around the C boundary (Main0's `ext` argument), with nothing else changed.

   WHERE IT PROBES is a function of the program's own sequence of external calls, which is the
   same on every machine, so the number of probes and the program points they sample do not
   depend on CPU speed or load (C-150: the first version probed every 5 s of CPU, and a faster
   machine could have got too few probes for a verdict). The run is cut into three phases by the
   external calls that open and close the format file:
     init  every external call before the first `wopenin`;
     load  from that `wopenin` to the first `wclose` after it (the format load, undump);
     dump  every external call after that `wclose` (here, the meaning dump).
   Within each phase it probes at the external calls whose ordinal in the phase is 1, 4, 16, 64,
   ... (powers of 4), and once more at the `wclose` that ends the load; then once at the end of
   the run (`final`). retention_probe.sh requires both load and dump to be reached, with at least
   3 probes in each.

   Each probe forces a full major GC and splits the live words into
     reach_state  the words reachable from the state the program is computing with now,
     static       the words reachable from the procedure table (the program's constants),
     other        live - reach_state - static: data that is live, but NOT reachable from the
                  current state. Before B2 this was 211-245 M words at the end of the format
                  load: old states kept alive by the fuel closures (§2.1).
   A probe whose `other` exceeds PS_RETPROBE_LIMIT words (default 1,000,000 = 8 MB) stops the
   run with exit 6 and the line RETPROBE FAIL. (static and reach_state can overlap, so a small
   negative `other` means nothing is retained: B2 measured -0.28 M at every probe.)
   PS_RETPROBE=1 enables it; without it the copy runs as the model does. *)
let enabled = Sys.getenv_opt "PS_RETPROBE" = Some "1"
let limit = match Sys.getenv_opt "PS_RETPROBE_LIMIT" with Some s -> int_of_string s | None -> 1_000_000
let static_words = ref 0
let calls = ref 0
let probes = ref 0
let phase = ref "init"
let k = ref 0 (* ordinal of the current external call within its phase *)

let probe ?(final = false) ?(at = "") (st : Values.state) =
  Gc.full_major ();
  let s = Gc.stat () in
  let r = Obj.reachable_words (Obj.repr st) in
  let other = s.Gc.live_words - r - !static_words in
  if not final then incr probes;
  Printf.eprintf
    "RETPROBE %s n %d phase %s k %d%s ext %d cpu %.2f live %d reach_state %d static %d other %d limit %d top %d\n%!"
    (if final then "final" else "run") !probes !phase !k at !calls (Sys.time ()) s.Gc.live_words r !static_words
    other limit s.Gc.top_heap_words;
  if (not final) && other > limit then begin
    Printf.eprintf "RETPROBE FAIL: %d words live but not reachable from the current state (limit %d)\n%!" other
      limit;
    exit 6
  end

let rec power_of_4 n = n = 1 || (n > 1 && n mod 4 = 0 && power_of_4 (n / 4))

let ext callp x args st =
  incr calls;
  if enabled then begin
    let name = Stdlib.String.of_seq (Stdlib.List.to_seq (Boundary.ext_name x)) in
    if !phase = "init" && name = "wopenin" then begin
      phase := "load";
      k := 0
    end
    else if !phase = "load" && name = "wclose" then begin
      incr k;
      probe ~at:" end-of-load" st;
      phase := "dump";
      k := 0
    end
    else begin
      incr k;
      if power_of_4 !k then probe st
    end
  end;
  Boundary.ext callp x args st
