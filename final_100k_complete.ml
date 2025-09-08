open Unix

let () =
  let payload = 
    let ic = open_in_bin "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/corpora/perf/perf_smoke_big.tex" in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic; 
    Bytes.unsafe_of_string s
  in
  
  Printf.printf "=== FINAL 100K TEST ===\n";
  Printf.printf "Starting service with high rotation thresholds (10GB/100 majors)...\n%!";
  let _ = Sys.command "pkill -9 -f main_service 2>/dev/null; rm -f /tmp/l0_lex_svc.sock" in
  
  (* Start service in background *)
  let service_pid = match fork () with
  | 0 -> 
    let null = openfile "/dev/null" [O_RDWR] 0o666 in
    dup2 null stdin; dup2 null stdout; dup2 null stderr;
    close null;
    execv "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/_build/default/latex-parse/src/main_service.exe"
          [|"main_service"; "--workers"; "2"; "--hedge-ms"; "12"|]
  | pid -> pid 
  in
  
  Printf.printf "Service PID: %d\n%!" service_pid;
  Printf.printf "Waiting for service to initialize...\n%!";
  sleep 3;
  
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
  let last_error_at = ref 0 in
  let error_details = ref [] in
  
  Printf.printf "\nRunning %d sequential requests...\n%!" n_total;
  Printf.printf "Expected duration: ~12-15 minutes based on previous tests\n\n%!";
  let start_time = gettimeofday () in
  
  for i = 1 to n_total do
    if i mod 5000 = 0 then begin
      let elapsed = gettimeofday () -. start_time in
      let rate = float i /. elapsed in
      let remaining = (float (n_total - i)) /. rate in
      Printf.printf "[%s] %6d / %d (%.0f req/s, %.1f min elapsed, est. %.1f min remaining, %d errors so far)\n%!" 
        (let t = Unix.localtime (Unix.time ()) in
         Printf.sprintf "%02d:%02d:%02d" t.tm_hour t.tm_min t.tm_sec)
        i n_total rate (elapsed /. 60.0) (remaining /. 60.0) !errors
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
      last_error_at := i;
      error_details := (i, Printexc.to_string e) :: !error_details;
      if !errors <= 5 then
        Printf.printf "  ⚠️  Error at request %d: %s\n%!" i (Printexc.to_string e)
      else if !errors = 6 then
        Printf.printf "  (suppressing further error messages)\n%!"
  done;
  
  let end_time = gettimeofday () in
  let total_time = end_time -. start_time in
  
  Printf.printf "\n" ;
  Printf.printf "════════════════════════════════════════════════\n";
  Printf.printf "           FINAL 100K TEST RESULTS              \n";
  Printf.printf "════════════════════════════════════════════════\n\n";
  
  Printf.printf "SUMMARY:\n";
  Printf.printf "  Total requests:     %d\n" n_total;
  Printf.printf "  Successful:         %d\n" (List.length !samples);
  Printf.printf "  Errors:             %d (%.4f%%)\n" !errors (100.0 *. float !errors /. float n_total);
  Printf.printf "  Duration:           %.1f seconds (%.1f minutes)\n" total_time (total_time /. 60.0);
  Printf.printf "  Throughput:         %.1f requests/second\n\n" (float (List.length !samples) /. total_time);
  
  if !errors > 0 then begin
    Printf.printf "ERROR ANALYSIS:\n";
    Printf.printf "  First 5 errors:\n";
    List.iter (fun (i, e) ->
      Printf.printf "    Request %d: %s\n" i e
    ) (List.rev (if List.length !error_details > 5 
                  then (let rec take n = function
                          | [] -> []
                          | _ when n = 0 -> []
                          | x::xs -> x :: take (n-1) xs
                        in take 5 (List.rev !error_details))
                  else !error_details));
    Printf.printf "  Last error at:      Request %d\n\n" !last_error_at
  end;
  
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
    
    Printf.printf "LATENCY PERCENTILES:\n";
    Printf.printf "  Min:                %.3f ms\n" min_val;
    Printf.printf "  P50 (median):       %.3f ms\n" p50;
    Printf.printf "  Mean:               %.3f ms\n" mean;
    Printf.printf "  P90:                %.3f ms\n" p90;
    Printf.printf "  P95:                %.3f ms\n" p95;
    Printf.printf "  P99:                %.3f ms\n" p99;
    Printf.printf "  P99.9:              %.3f ms  %s\n" p999 
      (if p999 <= 20.0 then "✅" else "❌");
    Printf.printf "  P99.99:             %.3f ms\n" p9999;
    Printf.printf "  Max:                %.3f ms\n\n" max_val;
    
    Printf.printf "════════════════════════════════════════════════\n";
    Printf.printf "REQUIREMENT: P99.9 ≤ 20ms\n";
    Printf.printf "ACTUAL:      P99.9 = %.3f ms\n" p999;
    Printf.printf "ERROR RATE:  %.4f%% (Target: 0%%)\n" (100.0 *. float !errors /. float n_total);
    Printf.printf "\n";
    Printf.printf "FINAL STATUS: %s\n" 
      (if p999 <= 20.0 && !errors = 0 then 
        "✅ ✅ ✅ ALL REQUIREMENTS MET ✅ ✅ ✅"
       else if p999 <= 20.0 && !errors < 100 then 
        "⚠️  LATENCY OK BUT HAS MINOR ERRORS" 
       else if p999 <= 20.0 then
        "❌ LATENCY OK BUT TOO MANY ERRORS"
       else if !errors = 0 then 
        "❌ NO ERRORS BUT LATENCY TOO HIGH"
       else 
        "❌ ❌ FAILS BOTH LATENCY AND ERROR REQUIREMENTS ❌ ❌");
    Printf.printf "════════════════════════════════════════════════\n"
  end else
    Printf.printf "\n❌ No successful requests completed!\n";
  
  (* Kill service *)
  Unix.kill service_pid Sys.sigterm;
  Printf.printf "\nService terminated.\n"