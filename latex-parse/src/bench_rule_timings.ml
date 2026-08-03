(* bench_rule_timings — PER-RULE attribution for the rules stage.

   R-BUDGET measured the warm readiness kernel spending ~329 ms of ~344 ms at
   300 KB inside RULE EXECUTION, linear at ~1.1 ms/KB. That says the cost is
   spread over rules, but not WHICH rules, and #521 already showed that guessing
   from call-site counts is unreliable — memoising the 91-call-site math scan
   bought 5-9%, not the order of magnitude it looked like. This bench answers
   the question with data instead.

   [Validators.run_all_with_timings] already computes exactly this and has never
   been reachable from any executable. It returns a duration for EVERY rule,
   fired or not, so a rule that costs a lot and finds nothing is visible — those
   are the ones inspection misses.

   TWO CACHING HAZARDS, both deliberately defeated:

   1. [run_all] memoises whole-document results through [Cache_key], so
   benchmarking it in-process makes reps 2..N cache hits (bench_readiness_
   kernel's own header says so). [run_all_with_timings] does NOT consult that
   cache — it executes the rule list directly — which is why it is the right
   entry point here.

   2. The shared range scanners ([find_exempt_ranges],
   [find_verbatim_comment_url_ranges], [find_math_ranges]) memoise on the
   buffer's PHYSICAL identity. Handing the same string object to every rep would
   leave those caches warm from rep 1, so the first rule to need a scanner would
   be charged nothing and the attribution would be wrong. Each rep therefore
   gets a FRESH copy of the source, which is what a new document in an editor
   session looks like. Within a rep the caches behave normally, because that IS
   the real behaviour of one pass.

   Usage: bench_rule_timings <reps> <file.tex> [--top N] *)

let read_file p =
  let ic = open_in_bin p in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let median xs =
  let a = Array.of_list xs in
  Array.sort compare a;
  let n = Array.length a in
  if n = 0 then 0.0
  else if n mod 2 = 1 then a.(n / 2)
  else (a.((n / 2) - 1) +. a.(n / 2)) /. 2.0

(* The shipped compile-gate surface is exactly the DELIM-/ENC-/PRT- prefixes, so
   tagging by prefix mirrors [Validators.is_compile_blocking] without exporting
   it. These are the rules on the KEYSTROKE path; everything else is
   batch-only. *)
let is_blocking id =
  let p s =
    String.length id >= String.length s && String.sub id 0 (String.length s) = s
  in
  p "DELIM-" || p "ENC-" || p "PRT-"

let () =
  if Array.length Sys.argv < 3 then (
    prerr_endline "usage: bench_rule_timings <reps> <file.tex> [--top N]";
    exit 2);
  let reps = int_of_string Sys.argv.(1) in
  let path = Sys.argv.(2) in
  let top =
    let rec find i =
      if i + 1 >= Array.length Sys.argv then 25
      else if Sys.argv.(i) = "--top" then int_of_string Sys.argv.(i + 1)
      else find (i + 1)
    in
    find 3
  in
  let src = read_file path in
  let n = String.length src in
  (* Fresh object per rep: see hazard 2 above. String.init defeats any sharing
     the compiler might apply to a literal or a previously-read buffer. *)
  let fresh () = String.init n (fun i -> String.unsafe_get src i) in
  ignore (Latex_parse_lib.Validators.run_all_with_timings (fresh ()));
  let acc : (string, float list) Hashtbl.t = Hashtbl.create 1024 in
  let totals = ref [] in
  for _ = 1 to reps do
    let _res, total_ms, timings =
      Latex_parse_lib.Validators.run_all_with_timings (fresh ())
    in
    totals := total_ms :: !totals;
    List.iter
      (fun (id, ms) ->
        let prev = try Hashtbl.find acc id with Not_found -> [] in
        Hashtbl.replace acc id (ms :: prev))
      timings
  done;
  let rows =
    Hashtbl.fold (fun id xs a -> (id, median xs) :: a) acc []
    |> List.sort (fun (_, a) (_, b) -> compare b a)
  in
  let grand = List.fold_left (fun a (_, ms) -> a +. ms) 0.0 rows in
  let blocking =
    List.fold_left
      (fun a (id, ms) -> if is_blocking id then a +. ms else a)
      0.0 rows
  in
  Printf.printf "# %s — %d bytes, %d reps, %d rules\n" path n reps
    (List.length rows);
  Printf.printf "# summed per-rule median: %.1f ms   (wall median %.1f ms)\n"
    grand (median !totals);
  Printf.printf
    "# of that, the %d compile-blocking rules (keystroke path): %.1f ms (%.1f%%)\n"
    (List.length (List.filter (fun (id, _) -> is_blocking id) rows))
    blocking
    (if grand > 0.0 then 100.0 *. blocking /. grand else 0.0);
  Printf.printf "%-14s %10s %8s %8s  %s\n" "rule" "median_ms" "share%" "cum%"
    "keystroke?";
  let cum = ref 0.0 in
  List.iteri
    (fun i (id, ms) ->
      if i < top then (
        cum := !cum +. ms;
        Printf.printf "%-14s %10.2f %7.1f%% %7.1f%%  %s\n" id ms
          (if grand > 0.0 then 100.0 *. ms /. grand else 0.0)
          (if grand > 0.0 then 100.0 *. !cum /. grand else 0.0)
          (if is_blocking id then "YES" else "")))
    rows
