open Latex_parse_lib

type opts = { file : string; iters : int; window : int; csv : string option }

let usage () =
  prerr_endline
    "usage: first_token_latency FILE ITERS [--window BYTES] [--csv PATH]";
  exit 2

let parse_int flag s =
  try int_of_string s
  with Failure _ ->
    Printf.eprintf "[ft] invalid integer for %s: %s\n" flag s;
    usage ()

let parse_cli () =
  if Array.length Sys.argv < 3 then usage ();
  let file = Sys.argv.(1) in
  let iters = parse_int "ITERS" Sys.argv.(2) in
  let window = ref 4096 in
  let csv = ref None in
  let i = ref 3 in
  while !i < Array.length Sys.argv do
    match Sys.argv.(!i) with
    | "--window" ->
        if !i + 1 >= Array.length Sys.argv then usage ();
        window := parse_int "--window" Sys.argv.(!i + 1);
        i := !i + 2
    | "--csv" ->
        if !i + 1 >= Array.length Sys.argv then usage ();
        csv := Some Sys.argv.(!i + 1);
        i := !i + 2
    | _ -> usage ()
  done;
  { file; iters; window = !window; csv = !csv }

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
  let len = in_channel_length ic in
  really_input_string ic len |> Bytes.unsafe_of_string

let slice b n =
  let n = min n (Bytes.length b) in
  Bytes.sub b 0 n

let idx_q n q = max 0 (min (n - 1) (int_of_float (ceil (float n *. q)) - 1))

let write_csv path stats =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
  output_string oc "label,min_us,p50_us,p95_us,p99_us,p999_us,max_us\n";
  Printf.fprintf oc "first-token,%.1f,%.1f,%.1f,%.1f,%.1f,%.1f\n" stats.(0)
    stats.(1) stats.(2) stats.(3) stats.(4) stats.(5)

let () =
  let { file; iters; window; csv } = parse_cli () in
  if iters <= 0 then (
    prerr_endline "[ft] iterations must be > 0";
    exit 2);
  let input = read_file file in
  if Bytes.length input = 0 then (
    prerr_endline "[ft] empty input";
    exit 2);
  let view = slice input window in
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  (try Simd_guard.require ()
   with Failure msg ->
     prerr_endline ("[ft] FATAL: " ^ msg);
     exit 2);
  Gc_prep.init_gc ();

  (* Warmup *)
  for _ = 1 to 64 do
    Gc_prep.prepay ();
    Arena.swap arenas;
    Pretouch.pre_touch_bytes view ~page:Config.page_bytes;
    ignore (Real_processor.run view (Arena.current arenas))
  done;

  let samples = Array.make iters 0.0 in
  for i = 0 to iters - 1 do
    Gc_prep.prepay ();
    Arena.swap arenas;
    let t0 = Clock.now () in
    Pretouch.pre_touch_bytes view ~page:Config.page_bytes;
    let cur = Arena.current arenas in
    ignore (Real_processor.run view cur);
    let dt_ms = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
    samples.(i) <- dt_ms *. 1000.0 (* us *)
  done;

  let n = Array.length samples in
  let sorted = Array.copy samples in
  Array.sort compare sorted;
  let percentile q = sorted.(idx_q n q) in
  let min_us = sorted.(0) in
  let p50 = percentile 0.50 in
  let p95 = percentile 0.95 in
  let p99 = percentile 0.99 in
  let p999 = percentile (if n >= 1000 then 0.999 else 0.99) in
  let max_us = sorted.(n - 1) in

  Printf.printf "first-token N=%d window=%dB\n%!" n window;
  Printf.printf
    "[ft] stats min=%.1f p50=%.1f p95=%.1f p99=%.1f p999=%.1f max=%.1f (us)\n%!"
    min_us p50 p95 p99 p999 max_us;

  (match csv with
  | Some path -> write_csv path [| min_us; p50; p95; p99; p999; max_us |]
  | None -> ());

  if p95 > 350.0 then (
    Printf.eprintf "[ft] FAIL: P95 = %.1f us > 350 us target\n%!" p95;
    exit 3)
  else Printf.printf "[ft] PASS: P95 = %.1f us ≤ 350 us\n%!" p95
