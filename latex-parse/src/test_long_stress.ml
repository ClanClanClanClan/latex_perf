(** Long-run stress test with GC tracking.

    Runs many iterations of randomized validator invocations, tracks Gc.stat to
    detect memory leaks or unbounded allocator growth. Excluded from dune
    runtest via enabled_if false. *)

let seed =
  match Sys.getenv_opt "TEST_SEED" with
  | Some s -> int_of_string s
  | None -> 99999

let iterations =
  match Sys.getenv_opt "STRESS_ITERS" with
  | Some s -> int_of_string s
  | None -> 10_000

let () = Random.init seed
let random_char () = Char.chr (32 + Random.int 95)
let random_string n = String.init n (fun _ -> random_char ())

let gen_latex () =
  let parts =
    List.init
      (3 + Random.int 5)
      (fun _ ->
        match Random.int 5 with
        | 0 -> "\\textbf{" ^ random_string (1 + Random.int 15) ^ "}"
        | 1 -> "$" ^ random_string (1 + Random.int 10) ^ "$"
        | 2 -> "\\label{" ^ random_string (1 + Random.int 5) ^ "}"
        | 3 -> "\\ref{" ^ random_string (1 + Random.int 5) ^ "}"
        | _ -> random_string (5 + Random.int 30))
  in
  String.concat "\n" parts

let () =
  Printf.printf "[long-stress] seed=%d iters=%d\n%!" seed iterations;
  let gc0 = Gc.stat () in
  let crashes = ref 0 in
  for i = 1 to iterations do
    let src = gen_latex () in
    (try ignore (Latex_parse_lib.Validators.run_all src)
     with exn ->
       incr crashes;
       if !crashes <= 5 then
         Printf.eprintf "[long-stress] CRASH at iter %d: %s\n%!" i
           (Printexc.to_string exn));
    if i mod 1000 = 0 then
      let gc = Gc.stat () in
      let major_delta = gc.Gc.major_collections - gc0.Gc.major_collections in
      Printf.printf "[long-stress] iter %d: major_gc=%d heap=%d words\n%!" i
        major_delta gc.Gc.live_words
  done;
  let gc_final = Gc.stat () in
  let total_major = gc_final.Gc.major_collections - gc0.Gc.major_collections in
  Printf.printf "[long-stress] final: %d major GCs over %d iterations\n%!"
    total_major iterations;
  if !crashes > 0 then (
    Printf.eprintf "[long-stress] FAIL: %d crashes\n%!" !crashes;
    exit 1)
  else
    Printf.printf "[long-stress] PASS %d iterations (seed=%d)\n%!" iterations
      seed
