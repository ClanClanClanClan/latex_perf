open Latex_parse_lib

let usage () =
  prerr_endline "usage: hash_throughput FILE ITERS [--csv PATH]";
  exit 2

let parse_int flag s =
  try int_of_string s
  with Failure _ ->
    Printf.eprintf "[hash] bad int for %s: %s\n" flag s;
    usage ()

let parse_cli () =
  if Array.length Sys.argv < 3 then usage ();
  let file = Sys.argv.(1) in
  let iters = parse_int "ITERS" Sys.argv.(2) in
  let csv = ref None in
  let i = ref 3 in
  while !i < Array.length Sys.argv do
    match Sys.argv.(!i) with
    | "--csv" ->
        if !i + 1 >= Array.length Sys.argv then usage ();
        csv := Some Sys.argv.(!i + 1);
        i := !i + 2
    | _ -> usage ()
  done;
  (file, iters, !csv)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
  let len = in_channel_length ic in
  really_input_string ic len |> Bytes.unsafe_of_string

let write_csv_header oc = output_string oc "label,mb_per_s\n"
let append_csv oc label mbps = Printf.fprintf oc "%s,%.2f\n" label mbps

let () =
  let file, iters, csv = parse_cli () in
  if iters <= 0 then (
    prerr_endline "[hash] iters must be > 0";
    exit 2);
  let b = read_file file in
  let nbytes = float (Bytes.length b) in
  let t0 = Clock.now () in
  let _acc = ref 0L in
  (* Run both FNV and XXH-like to provide two lanes (scalar). *)
  for _ = 1 to iters do
    _acc := Latex_parse_lib.Fast_hash.hash64_bytes b
  done;
  let dt_s = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) /. 1000.0 in
  let total_mb = nbytes *. float iters /. (1024.0 *. 1024.0) in
  let mbps = total_mb /. dt_s in
  Printf.printf "[hash] size=%.0fB iters=%d time=%.3fs throughput=%.2f MB/s\n%!"
    nbytes iters dt_s mbps;
  (match csv with
  | Some p ->
      let fresh = not (Sys.file_exists p) in
      let oc =
        open_out_gen [ Open_creat; Open_text; Open_wronly; Open_append ] 0o644 p
      in
      Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
      if fresh then write_csv_header oc;
      append_csv oc "fnv64" mbps
  | None -> ());

  let t1 = Clock.now () in
  for _ = 1 to iters do
    _acc := Latex_parse_lib.Xxh64.hash64_bytes b
  done;
  let dt2 = Clock.ms_of_ns Int64.(sub (Clock.now ()) t1) /. 1000.0 in
  let mbps2 = total_mb /. dt2 in
  Printf.printf
    "[hash-xxh] size=%.0fB iters=%d time=%.3fs throughput=%.2f MB/s\n%!" nbytes
    iters dt2 mbps2;
  match csv with
  | Some p ->
      let oc =
        open_out_gen [ Open_creat; Open_text; Open_wronly; Open_append ] 0o644 p
      in
      Fun.protect ~finally:(fun () -> close_out_noerr oc) @@ fun () ->
      append_csv oc "xxh64" mbps2
  | None -> ()
