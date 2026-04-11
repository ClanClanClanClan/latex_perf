(* ══════════════════════════════════════════════════════════════════════
   simd_vs_scalar_bench — isolated timing benchmark
   ══════════════════════════════════════════════════════════════════════

   Measures tokenizer_lite (pure OCaml scalar) vs real_processor (SIMD FFI)
   on the same corpus and reports per-path latency percentiles plus the
   speedup ratio.  Spec target: ≥ 6× at the tokeniser level.

   Usage:
     dune exec latex-parse/bench/simd_vs_scalar_bench.exe -- FILE ITERS \
       [--warmup N] [--csv PATH]
   ══════════════════════════════════════════════════════════════════════ *)

open Latex_parse_lib

(* ── CLI ──────────────────────────────────────────────────────────── *)

type cli_opts = {
  mutable file : string option;
  mutable iters : int option;
  mutable warmup : int;
  mutable csv : string option;
}

let default_opts () = { file = None; iters = None; warmup = 256; csv = None }

let usage () =
  prerr_endline
    "usage: simd_vs_scalar_bench FILE ITERS [--warmup N] [--csv PATH]";
  exit 2

let parse_int flag s =
  try int_of_string s
  with Failure _ ->
    Printf.eprintf "[bench] invalid integer for %s: %s\n" flag s;
    usage ()

let parse_cli () =
  let opts = default_opts () in
  let rec loop i =
    if i >= Array.length Sys.argv then ()
    else
      match Sys.argv.(i) with
      | "--warmup" ->
          if i + 1 >= Array.length Sys.argv then usage ();
          opts.warmup <- parse_int "--warmup" Sys.argv.(i + 1);
          loop (i + 2)
      | "--csv" ->
          if i + 1 >= Array.length Sys.argv then usage ();
          opts.csv <- Some Sys.argv.(i + 1);
          loop (i + 2)
      | "--help" | "-h" -> usage ()
      | arg ->
          (match (opts.file, opts.iters) with
          | None, _ -> opts.file <- Some arg
          | Some _, None -> opts.iters <- Some (parse_int "ITERS" arg)
          | Some _, Some _ ->
              Printf.eprintf "[bench] unexpected argument: %s\n" arg;
              usage ());
          loop (i + 1)
  in
  loop 1;
  match (opts.file, opts.iters) with
  | Some file, Some iters -> (file, iters, opts.warmup, opts.csv)
  | _ -> usage ()

(* ── Helpers ──────────────────────────────────────────────────────── *)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
  really_input_string ic (in_channel_length ic)

let percentile (sorted : float array) (q : float) : float =
  let n = Array.length sorted in
  let idx = max 0 (min (n - 1) (int_of_float (ceil (float n *. q)) - 1)) in
  sorted.(idx)

let sort_copy a =
  let b = Array.copy a in
  Array.sort compare b;
  b

let write_csv path scalar_stats simd_stats ratio =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
  output_string oc
    "path,min_ms,p50_ms,p95_ms,p99_ms,max_ms,throughput_MBps\n";
  let row label (s : float array) tp =
    Printf.fprintf oc "%s,%.4f,%.4f,%.4f,%.4f,%.4f,%.1f\n" label s.(0) s.(1)
      s.(2) s.(3) s.(4) tp
  in
  row "scalar" scalar_stats 0.0;
  row "simd" simd_stats 0.0;
  Printf.fprintf oc "speedup_ratio,%.2f\n" ratio

(* ── Benchmark loops ──────────────────────────────────────────────── *)

(** Time N iterations of [Tokenizer_lite.tokenize] on [src]. *)
let bench_scalar (src : string) ~(warmup : int) ~(iters : int) : float array =
  (* warmup *)
  for _ = 1 to warmup do
    ignore (Tokenizer_lite.tokenize src)
  done;
  Gc.compact ();
  (* measured *)
  let samples = Array.make iters 0.0 in
  for i = 0 to iters - 1 do
    let t0 = Clock.now () in
    let _toks = Tokenizer_lite.tokenize src in
    let t1 = Clock.now () in
    samples.(i) <- Clock.ms_of_ns Int64.(sub t1 t0)
  done;
  samples

(** Time N iterations of [Real_processor.run] on the same input. *)
let bench_simd (input_bytes : bytes) ~(warmup : int) ~(iters : int) :
    float array =
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  Gc_prep.init_gc ();
  (* SIMD guard *)
  (try Simd_guard.require ()
   with Failure msg ->
     Printf.eprintf "[bench] FATAL: %s\n" msg;
     exit 2);
  (* warmup *)
  for _ = 1 to warmup do
    Arena.swap arenas;
    Pretouch.pre_touch_bytes input_bytes ~page:Config.page_bytes;
    ignore (Real_processor.run input_bytes (Arena.current arenas))
  done;
  Gc.compact ();
  (* measured *)
  let samples = Array.make iters 0.0 in
  for i = 0 to iters - 1 do
    Gc_prep.prepay ();
    Arena.swap arenas;
    Pretouch.pre_touch_bytes input_bytes ~page:Config.page_bytes;
    let cur = Arena.current arenas in
    let t0 = Clock.now () in
    let _status, _tok, _iss = Real_processor.run input_bytes cur in
    let t1 = Clock.now () in
    samples.(i) <- Clock.ms_of_ns Int64.(sub t1 t0)
  done;
  samples

(* ── Report ───────────────────────────────────────────────────────── *)

let report_path label sorted input_size_bytes =
  let p50 = percentile sorted 0.50 in
  let p95 = percentile sorted 0.95 in
  let p99 = percentile sorted 0.99 in
  let min_ms = sorted.(0) in
  let max_ms = sorted.(Array.length sorted - 1) in
  let mb = float input_size_bytes /. (1024.0 *. 1024.0) in
  let tp_p50 = if p50 > 0.0 then mb /. (p50 /. 1000.0) else 0.0 in
  Printf.printf
    "[%s] N=%d  min=%.4f  p50=%.4f  p95=%.4f  p99=%.4f  max=%.4f ms  \
     throughput(p50)=%.1f MB/s\n\
     %!"
    label (Array.length sorted) min_ms p50 p95 p99 max_ms tp_p50;
  [| min_ms; p50; p95; p99; max_ms |]

(* ── Main ─────────────────────────────────────────────────────────── *)

let () =
  let file, iters, warmup, csv_path = parse_cli () in
  if iters <= 0 then (
    prerr_endline "[bench] iterations must be > 0";
    exit 2);
  let src = read_file file in
  let input_bytes = Bytes.unsafe_of_string src in
  let input_size = String.length src in
  Printf.printf "═══ SIMD vs Scalar benchmark ═══\n%!";
  Printf.printf "Input: %s (%d bytes, %.2f KB)\n%!" file input_size
    (float input_size /. 1024.0);
  Printf.printf "Iterations: %d (warmup: %d)\n\n%!" iters warmup;

  (* Run scalar first, then SIMD *)
  Printf.printf "── Scalar (Tokenizer_lite.tokenize) ──\n%!";
  let scalar_raw = bench_scalar src ~warmup ~iters in
  let scalar_sorted = sort_copy scalar_raw in
  let scalar_stats = report_path "scalar" scalar_sorted input_size in

  Printf.printf "\n── SIMD (Real_processor.run) ──\n%!";
  let simd_raw = bench_simd input_bytes ~warmup ~iters in
  let simd_sorted = sort_copy simd_raw in
  let simd_stats = report_path "simd" simd_sorted input_size in

  (* Speedup ratio at p50 *)
  let scalar_p50 = scalar_stats.(1) in
  let simd_p50 = simd_stats.(1) in
  let ratio =
    if simd_p50 > 0.0 then scalar_p50 /. simd_p50 else Float.infinity
  in
  Printf.printf "\n═══ Speedup (scalar_p50 / simd_p50) = %.2f× ═══\n%!" ratio;
  let target = 6.0 in
  if ratio >= target then
    Printf.printf "[bench] PASS: %.2f× ≥ %.1f× target\n%!" ratio target
  else
    Printf.printf "[bench] INFO: %.2f× < %.1f× target (see SIMD_v2.md §4)\n%!"
      ratio target;

  (* Optional CSV *)
  (match csv_path with
  | Some path -> write_csv path scalar_stats simd_stats ratio
  | None -> ())
