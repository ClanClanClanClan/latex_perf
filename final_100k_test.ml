open Unix

let () =
  let payload = 
    let ic = open_in_bin "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/corpora/perf/perf_smoke_big.tex" in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic; 
    Bytes.unsafe_of_string s
  in
  
  Printf.printf "Cleaning up old service...\n%!";
  let _ = Sys.command "pkill -9 -f main_service 2>/dev/null; rm -f /tmp/l0_lex_svc.sock" in
  
  Printf.printf "Starting fresh service for 100k test...\n%!";
  
  (* Start service in background *)
  let service_pid = match fork () with
  | 0 -> 
    (* Redirect all output to /dev/null *)
    let null = openfile "/dev/null" [O_RDWR] 0o666 in
    dup2 null stdin; 
    dup2 null stdout; 
    dup2 null stderr;
    close null;
    (* Execute service *)
    execv "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/_build/default/latex-parse/src/main_service.exe"
          [|"main_service"; "--workers"; "2"; "--hedge-ms"; "12"|]
  | pid -> pid 
  in
  
  Printf.printf "Service started with PID %d\n%!" service_pid;
  Printf.printf "Waiting for service to be ready...\n%!";
  sleep 3; (* Give service time to start *)
  
  let rec write_all fd b o l =
    if l > 0 then let n = write fd b o l in write_all fd b (o+n) (l-n)
  in
  
  let rec read_exact fd b o l =
    if l > 0 then let n = read fd b o l in 
    if n = 0 then failwith "EOF" else read_exact fd b (o+n) (l-n)
  in
  
  let n_total = 100000 in
  let samples = ref [] in
  let errors = ref 0 in
  
  Printf.printf "\nRunning %d sequential requests...\n%!" n_total;
  let start_time = gettimeofday () in
  
  for i = 1 to n_total do
    if i mod 1000 = 0 then begin
      let elapsed = gettimeofday () -. start_time in
      let rate = float i /. elapsed in
      Printf.printf "%6d / %d (%.0f req/s, est. %.1f min remaining)\n%!" 
        i n_total rate ((float (n_total - i)) /. rate /. 60.0)
    end;
    
    try
      let sock = socket PF_UNIX SOCK_STREAM 0 in
      let t_start = gettimeofday () in
      
      connect sock (ADDR_UNIX "/tmp/l0_lex_svc.sock");
      
      let len = Bytes.length payload in
      let hdr = Bytes.create 4 in
      Bytes.set hdr 0 (Char.chr ((len lsr 24) land 0xFF));
      Bytes.set hdr 1 (Char.chr ((len lsr 16) land 0xFF));
      Bytes.set hdr 2 (Char.chr ((len lsr  8) land 0xFF));
      Bytes.set hdr 3 (Char.chr (len land 0xFF));
      
      write_all sock hdr 0 4; 
      write_all sock payload 0 len;
      
      let rhdr = Bytes.create 4 in 
      read_exact sock rhdr 0 4;
      let rlen = ((Char.code (Bytes.get rhdr 0)) lsl 24) lor
                 ((Char.code (Bytes.get rhdr 1)) lsl 16) lor
                 ((Char.code (Bytes.get rhdr 2)) lsl 8) lor
                 (Char.code (Bytes.get rhdr 3)) in
      
      let rb = Bytes.create rlen in 
      read_exact sock rb 0 rlen;
      close sock;
      
      let dt = (gettimeofday () -. t_start) *. 1000.0 in
      samples := dt :: !samples
    with e ->
      incr errors;
      if !errors <= 10 then
        Printf.printf "  Error at request %d: %s\n%!" i (Printexc.to_string e)
  done;
  
  let end_time = gettimeofday () in
  let total_time = end_time -. start_time in
  
  Printf.printf "\n\nCompleted in %.1f seconds\n" total_time;
  Printf.printf "Successful requests: %d/%d (errors: %d)\n" 
    (List.length !samples) n_total !errors;
  
  if List.length !samples > 0 then begin
    let arr = Array.of_list !samples in
    Array.sort compare arr;
    let n = Array.length arr in
    
    let mean = (Array.fold_left (+.) 0.0 arr) /. float n in
    let p50 = arr.(n/2) in
    let p90 = arr.(min (n-1) (int_of_float (ceil (float n *. 0.90)) - 1)) in
    let p95 = arr.(min (n-1) (int_of_float (ceil (float n *. 0.95)) - 1)) in
    let p99 = arr.(min (n-1) (int_of_float (ceil (float n *. 0.99)) - 1)) in
    let p999 = arr.(min (n-1) (int_of_float (ceil (float n *. 0.999)) - 1)) in
    let p9999 = arr.(min (n-1) (int_of_float (ceil (float n *. 0.9999)) - 1)) in
    let max_val = arr.(n-1) in
    let min_val = arr.(0) in
    
    Printf.printf "\n=== FINAL 100K RESULTS ===\n";
    Printf.printf "Samples: %d\n" n;
    Printf.printf "Errors: %d\n\n" !errors;
    
    Printf.printf "LATENCY PERCENTILES:\n";
    Printf.printf "  Min:    %.3f ms\n" min_val;
    Printf.printf "  P50:    %.3f ms\n" p50;
    Printf.printf "  Mean:   %.3f ms\n" mean;
    Printf.printf "  P90:    %.3f ms\n" p90;
    Printf.printf "  P95:    %.3f ms\n" p95;
    Printf.printf "  P99:    %.3f ms\n" p99;
    Printf.printf "  P99.9:  %.3f ms  %s\n" p999 
      (if p999 <= 20.0 then "✅ PASS" else "❌ FAIL");
    Printf.printf "  P99.99: %.3f ms\n" p9999;
    Printf.printf "  Max:    %.3f ms\n\n" max_val;
    
    Printf.printf "THROUGHPUT:\n";
    Printf.printf "  %.1f requests/second\n\n" (float n /. total_time);
    
    Printf.printf "TARGET REQUIREMENT: P99.9 ≤ 20ms\n";
    Printf.printf "ACTUAL P99.9: %.3f ms\n" p999;
    Printf.printf "STATUS: %s\n\n" 
      (if p999 <= 20.0 then "✅ MEETS TARGET" else "❌ FAILS TARGET")
  end else
    Printf.printf "\nNo successful requests completed!\n";
  
  (* Kill service *)
  Unix.kill service_pid Sys.sigterm;
  Printf.printf "Service terminated.\n"