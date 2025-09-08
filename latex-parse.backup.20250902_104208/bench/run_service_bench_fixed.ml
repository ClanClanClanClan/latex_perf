open Unix
open Latex_parse_lib
open Percentiles

let read_file path =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in close_in ic; Bytes.unsafe_of_string s

let rec write_all fd b o l =
  if l=0 then () else let n=Unix.write fd b o l in if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)
let rec read_exact fd b o l =
  if l=0 then () else let n=Unix.read fd b o l in if n=0 then failwith "eof" else read_exact fd b (o+n) (l-n)

let send_req c (b:bytes) =
  let len = Bytes.length b in
  let hdr = Bytes.create 4 in
  Bytes.set hdr 0 (Char.chr ((len lsr 24) land 0xFF));
  Bytes.set hdr 1 (Char.chr ((len lsr 16) land 0xFF));
  Bytes.set hdr 2 (Char.chr ((len lsr  8) land 0xFF));
  Bytes.set hdr 3 (Char.chr ( len        land 0xFF));
  write_all c hdr 0 4; write_all c b 0 len

let recv_reply c =
  let hdr = Bytes.create 4 in
  read_exact c hdr 0 4;
  let len =
    ((Char.code (Bytes.get hdr 0)) lsl 24)
    lor ((Char.code (Bytes.get hdr 1)) lsl 16)
    lor ((Char.code (Bytes.get hdr 2)) lsl 8)
    lor (Char.code (Bytes.get hdr 3))
  in
  let b = Bytes.create len in read_exact c b 0 len; b

let () =
  let file = Sys.argv.(1) in
  let iters = int_of_string Sys.argv.(2) in
  let payload = read_file file in
  let samples = Array.make iters 0.0 in
  
  Printf.printf "Starting %d requests...\n%!" iters;
  let start_time = Unix.gettimeofday () in
  
  (* REUSE THE SAME CONNECTION for batches *)
  let batch_size = 1000 in
  let num_batches = (iters + batch_size - 1) / batch_size in
  
  for batch = 0 to num_batches - 1 do
    let batch_start = batch * batch_size in
    let batch_end = min ((batch + 1) * batch_size) iters in
    
    (* Create one connection per batch *)
    let c = Unix.socket PF_UNIX SOCK_STREAM 0 in
    Unix.connect c (ADDR_UNIX Config.service_sock_path);
    
    for i = batch_start to batch_end - 1 do
      let t0 = Clock.now () in
      send_req c payload;
      let _reply = recv_reply c in
      let dt_ms = Clock.ms_of_ns Int64.(sub (Clock.now ()) t0) in
      samples.(i) <- dt_ms;
      
      (* Progress report every 10K requests *)
      if (i + 1) mod 10000 = 0 then
        let elapsed = Unix.gettimeofday () -. start_time in
        let rate = float (i + 1) /. elapsed in
        Printf.printf "  %d/%d (%.1f req/s, elapsed: %.1fs)\n%!" (i + 1) iters rate elapsed
    done;
    
    Unix.close c
  done;
  
  let total_time = Unix.gettimeofday () -. start_time in
  
  (* Calculate percentiles *)
  Printf.printf "\nCompleted %d requests in %.2fs (%.2f req/s)\n\n" 
    iters total_time (float iters /. total_time);
    
  Printf.printf "RTT Latency (ms):\n";
  Printf.printf "  P50:    %.3f\n" (exact samples 0.50);
  Printf.printf "  P90:    %.3f\n" (exact samples 0.90);
  Printf.printf "  P95:    %.3f\n" (exact samples 0.95);
  Printf.printf "  P99:    %.3f\n" (exact samples 0.99);
  if iters >= 1000 then
    Printf.printf "  P99.9:  %.3f\n" (exact samples 0.999);
  if iters >= 10000 then
    Printf.printf "  P99.99: %.3f\n" (exact samples 0.9999);
  Printf.printf "  Max:    %.3f\n" (Array.fold_left max neg_infinity samples);
  Printf.printf "  Mean:   %.3f\n" (mean samples)