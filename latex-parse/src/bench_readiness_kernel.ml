(* bench_readiness_kernel — in-process microbench isolating the components of
   the compile-readiness kernel, so the numbers exclude OS process-startup and
   rule-registry construction (both are one-time, amortised in a long-running
   editor session). Reports, per input file: parse_ms : one
   Parser_l2.parse_located fastrun_ms : run_compile_blocking (shared parse) —
   the compile-blocking belt INCLUDING the shared parse, i.e. the true
   fast-kernel compute rules_ms : fastrun_ms - parse_ms — the rule execution
   alone

   ⚠ EVERY REP MUST GET ITS OWN PHYSICAL STRING. OPEN-021.

   This bench used to read the file once and hand the SAME physical string to
   every repetition. The scanners it measures are memoised on PHYSICAL equality
   — [validators_common.ml:2987] is `Some (s', r) when s' == s`, and the
   verbatim/comment/url range cache at :849 is the same shape — so reps 2..N
   were cache HITS. The bench was therefore measuring the memo, not the kernel,
   and it kept hot precisely the cache that #525 had just added. Every real-time
   number taken with it is optimistic by an unknown factor, which is why
   OPEN-021 says to re-record the ratchet only AFTER this fix.

   The copies are allocated BEFORE the timed region, so the memcpy is not
   charged to the measurement. A physical copy is the right defeat here and a
   content hash would not be: the cache tests `==`, not equality of contents.

   run_all is still intentionally NOT benched in-process: it memoises on
   Cache_key, which is a different mechanism from these physical-identity
   caches, and defeating it needs more than a fresh copy. The full-path numbers
   come from the fresh-process CLI benchmark (bench_compile_check.sh).

   ⚠ Do NOT record a latency threshold from a run on a developer laptop (process
   invariant 5): load has been observed at 158-230 here, and the same code has
   measured 7.477 ms and 1.454 ms for the same input under different load.
   Re-baseline on an idle CI runner only.

   Usage: bench_readiness_kernel <reps> <file.tex>... bench_readiness_kernel
   --shared-string-lie <reps> <file.tex>... The second form reproduces the OLD,
   WRONG behaviour on purpose, so the size of the error can be measured rather
   than asserted. *)

let read_file p =
  let ic = open_in_bin p in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* A distinct physical string with identical contents. Bytes.of_string copies
   and Bytes.to_string copies again, so the result cannot be shared with [s] by
   the compiler. *)
let fresh_copy s = Bytes.to_string (Bytes.of_string s)

let median xs =
  let a = Array.of_list xs in
  Array.sort compare a;
  let n = Array.length a in
  if n = 0 then 0.0
  else if n mod 2 = 1 then a.(n / 2)
  else (a.((n / 2) - 1) +. a.(n / 2)) /. 2.0

let time_ms f =
  let t0 = Unix.gettimeofday () in
  ignore (f ());
  (Unix.gettimeofday () -. t0) *. 1000.0

(* [f] takes the rep index so it can pick its own pre-allocated copy. *)
let bench reps f = median (List.init reps (fun i -> time_ms (fun () -> f i)))

let () =
  let argv = Array.to_list Sys.argv in
  let shared_lie, argv =
    match argv with
    | exe :: "--shared-string-lie" :: rest -> (true, exe :: rest)
    | _ -> (false, argv)
  in
  let argv = Array.of_list argv in
  let reps = int_of_string argv.(1) in
  if shared_lie then
    prerr_endline
      "[bench] --shared-string-lie: reusing ONE physical string across reps, \
       which is the OPEN-021 defect. These numbers are memo hits, not kernel \
       time. For comparison only.";
  Printf.printf "%-10s %-12s %-12s %-12s\n" "size" "parse_ms" "fastrun_ms"
    "rules_ms";
  for i = 1 to Array.length argv - 1 do
    if i >= 2 then (
      let path = argv.(i) in
      let src = read_file path in
      (* Pre-allocate one distinct physical string per rep, OUTSIDE the timed
         region. In --shared-string-lie mode every slot aliases [src], which is
         exactly what the old bench did. *)
      let inputs =
        Array.init reps (fun _ -> if shared_lie then src else fresh_copy src)
      in
      (* Warm code paths and the rule registry on a string that is NOT one of
         the timed inputs, so no timed rep starts with a populated memo. *)
      let warm = fresh_copy src in
      ignore (Latex_parse_lib.Parser_l2.parse_located warm);
      ignore (Latex_parse_lib.Validators.run_compile_blocking warm);
      let parse =
        bench reps (fun k -> Latex_parse_lib.Parser_l2.parse_located inputs.(k))
      in
      let fastrun =
        bench reps (fun k ->
            let s = inputs.(k) in
            let _n, errs = Latex_parse_lib.Parser_l2.parse_located s in
            Latex_parse_lib.Validators.run_compile_blocking ~parse_errors:errs s)
      in
      Printf.printf "%-10d %-12.1f %-12.1f %-12.1f\n" (String.length src) parse
        fastrun (fastrun -. parse))
  done
