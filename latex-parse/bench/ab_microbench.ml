open Latex_parse_lib

let read_file path =
  let ic = open_in_bin path in let len = in_channel_length ic in
  let s = really_input_string ic len in close_in ic; Bytes.unsafe_of_string s

let idx_q n q = max 0 (min (n-1) (int_of_float (ceil (float n *. q)) - 1))

let () =
  if Array.length Sys.argv < 3 then (prerr_endline "usage: ab_microbench FILE ITERS [WARMUP]"; exit 2);
  let file   = Sys.argv.(1) in
  let total  = int_of_string Sys.argv.(2) in
  let warmup = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 512 in
  let input  = read_file file in
  let arenas = Arena.create ~cap:Config.arenas_tokens_cap in
  Gc_prep.init_gc ();
  let samples = Array.make total 0.0 in

  (* SIMD guard (same rule as service) *)
  (try
     let (_cpu_ok, _sym_ok, _allow_scalar) = Simd_guard.require () in ()
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
  Printf.printf "A+B N=%d\n%!" n;
  Percentiles_strict.dump "A+B" samples;

  if n >= 100_000 then begin
    let idx = idx_q n 0.999 in
    let p999 = (Array.copy samples |> fun a -> Array.sort compare a; a.(idx)) in
    if p999 > Config.ab_p999_target_ms then begin
      Printf.eprintf "[ab] FAIL: P99.9 = %.3f ms > %.3f ms target\n%!" p999 Config.ab_p999_target_ms;
      exit 3
    end else
      Printf.printf "[ab] PASS: P99.9 = %.3f ms ≤ %.3f ms\n%!" p999 Config.ab_p999_target_ms
  end
  else
    Printf.printf "[ab] NOTE: N<100k, skipped strict P99.9 gate\n%!"