open Latex_parse_lib

type mode = Balance | InsertOnly | DeleteOnly | Cluster
type edit = Insert of int * char | Delete of int

let usage () =
  prerr_endline "usage: edit_replay_bench FILE EDITS [--warmup N] [--window BYTES] [--csv PATH]";
  prerr_endline "       FILE         path to input .tex";
  prerr_endline "       EDITS        number of incremental edits to simulate";
  exit 2

let parse_int flag s =
  try int_of_string s with Failure _ ->
    Printf.eprintf "[replay] invalid integer for %s: %s\n" flag s; usage ()

let parse_cli () =
  let file = ref None and edits = ref None in
  let warmup = ref 128 in
  let window = ref 4096 in
  let csv = ref None in
  let mode = ref Balance in
  let cluster_span = ref 256 in
  let rec loop i =
    if i >= Array.length Sys.argv then () else
      match Sys.argv.(i) with
      | "--warmup" -> if i+1 >= Array.length Sys.argv then usage (); warmup := parse_int "--warmup" Sys.argv.(i+1); loop (i+2)
      | "--window" -> if i+1 >= Array.length Sys.argv then usage (); window := parse_int "--window" Sys.argv.(i+1); loop (i+2)
      | "--csv"    -> if i+1 >= Array.length Sys.argv then usage (); csv := Some Sys.argv.(i+1); loop (i+2)
      | "--mode"   -> if i+1 >= Array.length Sys.argv then usage (); begin
                         match String.lowercase_ascii Sys.argv.(i+1) with
                         | "balance" | "balanced" -> mode := Balance
                         | "insert" | "insert-only" -> mode := InsertOnly
                         | "delete" | "delete-only" -> mode := DeleteOnly
                         | "cluster" -> mode := Cluster
                         | _ -> prerr_endline "[replay] invalid --mode"; usage ()
                       end; loop (i+2)
      | "--cluster-span" -> if i+1 >= Array.length Sys.argv then usage (); cluster_span := parse_int "--cluster-span" Sys.argv.(i+1); loop (i+2)
      | "--help" | "-h" -> usage ()
      | arg ->
         if !file = None then file := Some arg
         else if !edits = None then edits := Some (parse_int "EDITS" arg)
         else (Printf.eprintf "[replay] unexpected argument: %s\n" arg; usage ());
         loop (i+1)
  in
  loop 1;
  match !file, !edits with
  | Some f, Some n -> (f, n, !warmup, !window, !mode, !cluster_span, !csv)
  | _ -> usage ()

let read_file p =
  let ic = open_in_bin p in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
    let len = in_channel_length ic in really_input_string ic len

let clamp a x b = max a (min b x)

let window_slice s center w =
  let n = String.length s in
  let half = w / 2 in
  let start = clamp 0 (center - half) (max 0 (n - w)) in
  let len = min w (n - start) in
  (start, String.sub s start len)

let apply_edit s = function
  | Insert (i, c) ->
      let i = clamp 0 i (String.length s) in
      (String.sub s 0 i) ^ (String.make 1 c) ^ (String.sub s i (String.length s - i))
  | Delete i ->
      if String.length s = 0 then s
      else
        let i = clamp 0 i (String.length s - 1) in
        (String.sub s 0 i) ^ (String.sub s (i+1) (String.length s - i - 1))

let idx_q n q = max 0 (min (n-1) (int_of_float (ceil (float n *. q)) - 1))

let write_csv path stats =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
    output_string oc "label,min_ms,p50_ms,p95_ms,p99_ms,p999_ms,max_ms\n";
    Printf.fprintf oc "edit-replay,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f\n"
      stats.(0) stats.(1) stats.(2) stats.(3) stats.(4) stats.(5)

let () =
  let (file, n_edits, warmup, window_bytes, mode, cluster_span, csv) = parse_cli () in
  if window_bytes <= 0 then (prerr_endline "[replay] window must be > 0"; exit 2);
  let base = read_file file in
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  Gc_prep.init_gc (); (try Simd_guard.require () with Failure m -> prerr_endline ("[replay] FATAL: "^m); exit 2);
  let rng = Random.State.make [|0x5A17; 0xB00B|] in

  let edits =
    let hotspot = ref (String.length base / 2) in
    Array.init n_edits (fun _ ->
      match mode with
      | InsertOnly -> Insert (Random.State.int rng (max 1 (String.length base)), Char.chr (97 + Random.State.int rng 26))
      | DeleteOnly -> if String.length base > 0 then Delete (Random.State.int rng (String.length base)) else Insert (0,'a')
      | Balance -> if Random.State.bool rng then
                      Insert (Random.State.int rng (max 1 (String.length base)), Char.chr (97 + Random.State.int rng 26))
                   else if String.length base > 0 then Delete (Random.State.int rng (String.length base)) else Insert (0,'a')
      | Cluster ->
          let center = !hotspot in
          let pos = clamp 0 (center + (Random.State.int rng (2*cluster_span+1) - cluster_span)) (max 0 (String.length base)) in
          hotspot := pos;
          if Random.State.bool rng then Insert (pos, Char.chr (97 + Random.State.int rng 26))
          else if String.length base > 0 then Delete (clamp 0 pos (max 0 (String.length base - 1))) else Insert (pos,'a')
    )
  in

  let mutable_doc = ref base in

  (* Warmup on random windows *)
  for _=1 to warmup do
    Gc_prep.prepay (); Arena.swap arenas;
    let pos = Random.State.int rng (max 1 (String.length !mutable_doc)) in
    let (_start, slice) = window_slice !mutable_doc pos window_bytes in
    Pretouch.pre_touch_bytes (Bytes.unsafe_of_string slice) ~page:Config.page_bytes;
    ignore (Real_processor.run (Bytes.unsafe_of_string slice) (Arena.current arenas))
  done;

  let samples = Array.make n_edits 0.0 in
  for i=0 to n_edits-1 do
    let e = edits.(i) in
    (* choose center near edit position when possible *)
    let pos = match e with Insert (p, _) -> p | Delete p -> p in
    let t0 = Clock.now () in
    Gc_prep.prepay (); Arena.swap arenas;
    let (_start, slice) = window_slice !mutable_doc pos window_bytes in
    Pretouch.pre_touch_bytes (Bytes.unsafe_of_string slice) ~page:Config.page_bytes;
    let cur = Arena.current arenas in
    ignore (Real_processor.run (Bytes.unsafe_of_string slice) cur);
    let dt_ms = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
    samples.(i) <- dt_ms;
    mutable_doc := apply_edit !mutable_doc e
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

  let mode_s = match mode with Balance->"balance" | InsertOnly->"insert" | DeleteOnly->"delete" | Cluster->"cluster" in
  Printf.printf "edit-replay N=%d window=%dB mode=%s\n%!" n window_bytes mode_s;
  Bench_utils.Percentiles_strict.dump "edit-replay" samples;
  Printf.printf "[replay] %s stats min=%.3f p50=%.3f p95=%.3f p99=%.3f p999=%.3f max=%.3f (ms)\n%!"
    mode_s min_ms p50 p95 p99 p999 max_ms;

  (match csv with Some p -> write_csv p [|min_ms;p50;p95;p99;p999;max_ms|] | None -> ())
