open Latex_parse_lib

type cli_opts = {
  mutable file : string option;
  mutable iters : int option;
  mutable warmup : int;
  mutable csv : string option;
}

let default_opts () = { file=None; iters=None; warmup=512; csv=None }

let usage () =
  prerr_endline "usage: ab_microbench FILE ITERS [--warmup N] [--csv PATH]";
  prerr_endline "       FILE         path to input .tex";
  prerr_endline "       ITERS        number of measured iterations";
  prerr_endline "       --warmup N   (optional) warmup iterations, default 512";
  prerr_endline "       --csv PATH   (optional) write summary CSV";
  exit 2

let parse_int flag s =
  try int_of_string s with Failure _ ->
    Printf.eprintf "[ab] invalid integer for %s: %s\n" flag s;
    usage ()

let parse_cli () =
  let opts = default_opts () in
  let rec loop i =
    if i >= Array.length Sys.argv then () else
      match Sys.argv.(i) with
      | "--warmup" ->
          if i+1 >= Array.length Sys.argv then usage ();
          opts.warmup <- parse_int "--warmup" Sys.argv.(i+1);
          loop (i+2)
      | "--csv" ->
          if i+1 >= Array.length Sys.argv then usage ();
          opts.csv <- Some Sys.argv.(i+1);
          loop (i+2)
      | "--help" | "-h" -> usage ()
      | arg ->
          (match opts.file, opts.iters with
           | None, _ -> opts.file <- Some arg
           | Some _, None -> opts.iters <- Some (parse_int "ITERS" arg)
           | Some _, Some _ ->
               Printf.eprintf "[ab] unexpected argument: %s\n" arg;
               usage ());
          loop (i+1)
  in
  loop 1;
  match opts.file, opts.iters with
  | Some file, Some iters -> (file, iters, opts.warmup, opts.csv)
  | _ -> usage ()

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
    let len = in_channel_length ic in
    really_input_string ic len |> Bytes.unsafe_of_string

let idx_q n q = max 0 (min (n-1) (int_of_float (ceil (float n *. q)) - 1))

let write_csv path stats =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
    output_string oc "label,min_ms,p50_ms,p95_ms,p99_ms,p999_ms,max_ms\n";
    Printf.fprintf oc "A+B,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f\n"
      stats.(0) stats.(1) stats.(2) stats.(3) stats.(4) stats.(5)

let () =
  let (file, total, warmup, csv_path) = parse_cli () in
  if total <= 0 then (prerr_endline "[ab] iterations must be > 0"; exit 2);
  let input  = read_file file in
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  Gc_prep.init_gc ();
  let samples = Array.make total 0.0 in

  (* SIMD guard (same rule as service) *)
  (try
     Simd_guard.require ()
   with Failure msg ->
     prerr_endline ("[ab] FATAL: "^msg); exit 2
  );

  (* Warmup *)
  for _=1 to warmup do
    Gc_prep.prepay (); Arena.swap arenas;
    Pretouch.pre_touch_bytes input ~page:Config.page_bytes;
    let cur = Arena.current arenas in
    ignore (Real_processor.run input cur)
  done;

  (* Measured *)
  for i=0 to total-1 do
    let t0 = Clock.now () in
    Gc_prep.prepay (); Arena.swap arenas;
    Pretouch.pre_touch_bytes input ~page:Config.page_bytes;
    let cur = Arena.current arenas in
    let (_status, tok, _iss) = Real_processor.run input cur in
    let dt_ms = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
    samples.(i) <- dt_ms;
    if (i land 4095) = 0 then
      if tok < Config.ab_expected_tokens_min || tok > Config.ab_expected_tokens_max
      then (Printf.eprintf "[ab] token count out of expected range: %d\n%!" tok; exit 3)
  done;

  (* Percentiles *)
  let n = Array.length samples in
  let sorted = Array.copy samples in
  Array.sort compare sorted;
  let percentile q = sorted.(idx_q n q) in
  let min_ms = sorted.(0) in
  let p50 = percentile 0.50 in
  let p95 = percentile 0.95 in
  let p99 = percentile 0.99 in
  let p999 = percentile (if n >= 1000 then 0.999 else 0.99) in
  let max_ms = sorted.(n-1) in

  Printf.printf "A+B N=%d\n%!" n;
  Bench_utils.Percentiles_strict.dump "A+B" samples;
  Printf.printf "[ab] stats min=%.3f p50=%.3f p95=%.3f p99=%.3f p999=%.3f max=%.3f (ms)\n%!"
    min_ms p50 p95 p99 p999 max_ms;

  (match csv_path with
  | Some path -> write_csv path [|min_ms; p50; p95; p99; p999; max_ms|]
  | None -> ());

  if n >= 100_000 then begin
    if p999 > Config.ab_p999_target_ms then begin
      Printf.eprintf "[ab] FAIL: P99.9 = %.3f ms > %.3f ms target\n%!" p999 Config.ab_p999_target_ms;
      exit 3
    end else
      Printf.printf "[ab] PASS: P99.9 = %.3f ms ≤ %.3f ms\n%!" p999 Config.ab_p999_target_ms
  end
  else
    Printf.printf "[ab] NOTE: N<100k, skipped strict P99.9 gate\n%!"
