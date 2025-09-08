open Unix
module Config = Latex_parse_lib.Config
module Clock = Latex_parse_lib.Clock

let read_file path =
  let ic = open_in_bin path in let len = in_channel_length ic in
  let s = really_input_string ic len in close_in ic; Bytes.unsafe_of_string s

let rec write_all fd b o l =
  if l=0 then () else let n=Unix.write fd b o l in if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)
let rec read_exact fd b o l =
  if l=0 then () else let n=Unix.read fd b o l in if n=0 then failwith "eof" else read_exact fd b (o+n) (l-n)

let send_once payload =
  try
    let c = Unix.socket PF_UNIX SOCK_STREAM 0 in
    Unix.connect c (ADDR_UNIX Config.service_sock_path);
    let len = Bytes.length payload in
    let hdr = Bytes.create 4 in
    Bytes.set hdr 0 (Char.chr ((len lsr 24) land 0xFF));
    Bytes.set hdr 1 (Char.chr ((len lsr 16) land 0xFF));
    Bytes.set hdr 2 (Char.chr ((len lsr  8) land 0xFF));
    Bytes.set hdr 3 (Char.chr ( len        land 0xFF));
    let t0 = Clock.now () in
    write_all c hdr 0 4; write_all c payload 0 len;
    let rhdr = Bytes.create 4 in read_exact c rhdr 0 4;
    let rlen =
      ((Char.code (Bytes.get rhdr 0)) lsl 24)
      lor ((Char.code (Bytes.get rhdr 1)) lsl 16)
      lor ((Char.code (Bytes.get rhdr 2)) lsl 8)
      lor (Char.code (Bytes.get rhdr 3))
    in
    let rb = Bytes.create rlen in read_exact c rb 0 rlen;
    Unix.close c;
    Clock.ms_of_ns Int64.(sub (Clock.now ()) t0)
  with _ ->
    (* On error, return a large value to signal failure *)
    999999.0

let () =
  if Array.length Sys.argv < 4 then (prerr_endline "usage: run_service_bench_concurrent FILE ITERS THREADS"; exit 2);
  let file = Sys.argv.(1) in
  let total = int_of_string Sys.argv.(2) in
  let threads = int_of_string Sys.argv.(3) in
  let payload = read_file file in
  let samples = Array.make total 0.0 in
  let idx = ref 0 in
  let m = Mutex.create () in
  let worker () =
    while true do
      Mutex.lock m;
      if !idx >= total then (Mutex.unlock m; raise Thread.Exit);
      let i = !idx in incr idx; Mutex.unlock m;
      samples.(i) <- send_once payload
    done
  in
  let ths = Array.init threads (fun _ -> Thread.create worker ()) in
  Array.iter Thread.join ths;
  
  (* Filter out error values (999999.0) *)
  let valid_samples = Array.to_list samples |> 
    List.filter (fun x -> x < 1000.0) |> 
    Array.of_list in
  let n_valid = Array.length valid_samples in
  let n_errors = total - n_valid in
  
  Printf.printf "RTT N=%d (success=%d, errors=%d)\n%!" total n_valid n_errors;
  
  if n_valid > 0 then begin
    Array.sort compare valid_samples;
    let p50 = valid_samples.(n_valid/2) in
    let p99 = valid_samples.(min (n_valid-1) (int_of_float (ceil (float n_valid *. 0.99)) - 1)) in
    let p999 = valid_samples.(min (n_valid-1) (int_of_float (ceil (float n_valid *. 0.999)) - 1)) in
    Printf.printf "  P50:   %.3f ms\n" p50;
    Printf.printf "  P99:   %.3f ms\n" p99;
    Printf.printf "  P99.9: %.3f ms\n" p999;
    if p999 <= 20.0 then
      Printf.printf "✅ P99.9 <= 20ms target MET!\n"
    else
      Printf.printf "❌ P99.9 > 20ms target FAILED\n"
  end else
    Printf.printf "  No successful requests!\n"