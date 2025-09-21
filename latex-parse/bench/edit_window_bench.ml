open Latex_parse_lib

let default_window_bytes = 4096

let usage () =
  prerr_endline "usage: edit_window_bench FILE ITERS [--warmup N] [--window BYTES] [--csv PATH]";
  prerr_endline "       FILE         path to input .tex";
  prerr_endline "       ITERS        number of measured iterations";
  exit 2

let parse_int flag s =
  try int_of_string s with Failure _ ->
    Printf.eprintf "[edit] invalid integer for %s: %s\n" flag s;
    usage ()

let parse_cli () =
  let file = ref None and iters = ref None in
  let warmup = ref 256 in
  let csv = ref None and windows = ref [] in
  let rec loop i =
    if i >= Array.length Sys.argv then () else
      match Sys.argv.(i) with
      | "--warmup" ->
          if i+1 >= Array.length Sys.argv then usage ();
          warmup := parse_int "--warmup" Sys.argv.(i+1);
          loop (i+2)
      | "--window" ->
          if i+1 >= Array.length Sys.argv then usage ();
          windows := parse_int "--window" Sys.argv.(i+1) :: !windows;
          loop (i+2)
      | "--csv" ->
          if i+1 >= Array.length Sys.argv then usage ();
          csv := Some Sys.argv.(i+1);
          loop (i+2)
      | "--help" | "-h" -> usage ()
      | arg ->
          if !file = None then file := Some arg
          else if !iters = None then iters := Some (parse_int "ITERS" arg)
          else (Printf.eprintf "[edit] unexpected argument: %s\n" arg; usage ());
          loop (i+1)
  in
  loop 1;
  let win_list = if !windows = [] then [default_window_bytes] else List.rev !windows in
  match !file, !iters with
  | Some f, Some n -> (f, n, !warmup, win_list, !csv)
  | _ -> usage ()

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
    let len = in_channel_length ic in
    really_input_string ic len |> Bytes.unsafe_of_string

let slice input offset len =
  let len = min len (Bytes.length input - offset) in
  Bytes.sub input offset len

let idx_q n q =
  max 0 (min (n-1) (int_of_float (ceil (float n *. q)) - 1))

let write_csv path label stats ~append =
  let mode =
    if append then [Open_creat; Open_wronly; Open_text; Open_append]
    else [Open_creat; Open_wronly; Open_text; Open_trunc]
  in
  let oc = open_out_gen mode 0o644 path in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
    if not append then output_string oc "label,min_ms,p50_ms,p95_ms,p99_ms,p999_ms,max_ms\n";
    Printf.fprintf oc "%s,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f\n"
      label stats.(0) stats.(1) stats.(2) stats.(3) stats.(4) stats.(5)

let () =
  let (file, total, warmup, window_bytes_list, csv_path) = parse_cli () in
  if total <= 0 then (prerr_endline "[edit] iterations must be > 0"; exit 2);
  let input = read_file file in
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  Gc_prep.init_gc ();
  (try Simd_guard.require () with Failure msg -> prerr_endline ("[edit] FATAL: "^msg); exit 2);
  let samples = Array.make total 0.0 in
  let rng = Random.State.make [|0xC0DE; 0xBEEF|] in
  let first = ref true in
  List.iter (fun window_bytes ->
    if window_bytes <= 0 then (Printf.eprintf "[edit] window must be > 0 (got %d)\n" window_bytes; exit 2);
    if Bytes.length input < window_bytes then begin
      Printf.printf "[edit] SKIP (%dB): input smaller than window (%d < %d)\n%!" window_bytes (Bytes.length input) window_bytes
    end else begin
    let pick_slice () =
      let max_offset = Bytes.length input - window_bytes in
      let offset = if max_offset = 0 then 0 else Random.State.int rng (max_offset + 1) in
      slice input offset window_bytes
    in

    for _ = 1 to warmup do
      Gc_prep.prepay (); Arena.swap arenas;
      let chunk = pick_slice () in
      Pretouch.pre_touch_bytes chunk ~page:Config.page_bytes;
      let cur = Arena.current arenas in
      ignore (Real_processor.run chunk cur)
    done;

    for i = 0 to total - 1 do
      let chunk = pick_slice () in
      let t0 = Clock.now () in
      Gc_prep.prepay (); Arena.swap arenas;
      Pretouch.pre_touch_bytes chunk ~page:Config.page_bytes;
      let cur = Arena.current arenas in
      let (_status, _tok, _iss) = Real_processor.run chunk cur in
      let dt_ms = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
      samples.(i) <- dt_ms
    done;

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

    Printf.printf "edit-window[%dB] N=%d\n%!" window_bytes n;
    Bench_utils.Percentiles_strict.dump (Printf.sprintf "edit-window-%d" window_bytes) samples;
    Printf.printf "[edit] %dB stats min=%.3f p50=%.3f p95=%.3f p99=%.3f p999=%.3f max=%.3f (ms)\n%!"
      window_bytes min_ms p50 p95 p99 p999 max_ms;

    (match csv_path with
     | Some path ->
         write_csv path (Printf.sprintf "edit-window-%d" window_bytes)
           [|min_ms; p50; p95; p99; p999; max_ms|] ~append:(not !first)
     | None -> ());

    first := false;

    if n >= 1_000 then begin
      if p95 > 1.2 then begin
        Printf.eprintf "[edit] FAIL (%dB): P95 = %.3f ms > 1.2 ms target\n%!" window_bytes p95;
        exit 3
      end else
        Printf.printf "[edit] PASS (%dB): P95 = %.3f ms ≤ 1.2 ms\n%!" window_bytes p95
    end else
      Printf.printf "[edit] NOTE (%dB): N<1000, informational run only\n%!" window_bytes
    end

  ) window_bytes_list
