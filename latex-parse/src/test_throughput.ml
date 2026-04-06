(** Throughput benchmarks for lockfree queue (W63) and sentence splitter
    (W68-70). *)

let () =
  Printf.printf "[test_throughput] Measuring component throughput\n%!";

  (* ── W63: Lock-free queue throughput (target: 8M events/sec) ─── *)
  let q = Latex_parse_lib.Lockfree_queue.create 4096 in
  let n = 1_000_000 in
  let t0 = Unix.gettimeofday () in
  for i = 1 to n do
    while not (Latex_parse_lib.Lockfree_queue.try_push q i) do
      ignore (Latex_parse_lib.Lockfree_queue.try_pop q)
    done
  done;
  (* Drain *)
  let drained = ref 0 in
  let continue = ref true in
  while !continue do
    match Latex_parse_lib.Lockfree_queue.try_pop q with
    | Some _ -> incr drained
    | None -> continue := false
  done;
  let t1 = Unix.gettimeofday () in
  let elapsed = t1 -. t0 in
  let events_per_sec = float_of_int n /. elapsed in
  Printf.printf "  [lockfree-queue] %d ops in %.3fs = %.1fM events/sec\n%!" n
    elapsed
    (events_per_sec /. 1_000_000.0);
  Printf.printf "  [lockfree-queue] Target: 8M events/sec → %s\n%!"
    (if events_per_sec >= 8_000_000.0 then "PASS"
     else "BELOW TARGET (single-thread)");
  ignore !drained;

  (* ── W63: Multi-domain throughput ────────────────────────────── *)
  let q2 = Latex_parse_lib.Lockfree_queue.create 8192 in
  let producer_count = 2 in
  let per_producer = 500_000 in
  let total = producer_count * per_producer in
  let consumed = Atomic.make 0 in
  let t2 = Unix.gettimeofday () in
  let producers =
    List.init producer_count (fun _ ->
        Domain.spawn (fun () ->
            for i = 1 to per_producer do
              Latex_parse_lib.Lockfree_queue.push q2 i
            done))
  in
  let consumer =
    Domain.spawn (fun () ->
        for _ = 1 to total do
          ignore (Latex_parse_lib.Lockfree_queue.pop q2);
          ignore (Atomic.fetch_and_add consumed 1)
        done)
  in
  List.iter Domain.join producers;
  Domain.join consumer;
  let t3 = Unix.gettimeofday () in
  let mt_elapsed = t3 -. t2 in
  let mt_eps = float_of_int total /. mt_elapsed in
  Printf.printf
    "  [lockfree-queue] %d ops (2P+1C) in %.3fs = %.1fM events/sec\n%!" total
    mt_elapsed (mt_eps /. 1_000_000.0);
  Printf.printf "  [lockfree-queue] Multi-domain target: 8M → %s\n%!"
    (if mt_eps >= 8_000_000.0 then "PASS" else "BELOW (see note)");

  (* ── W68-70: Sentence splitter throughput (target: 50 MiB/s) ─── *)
  (* Generate a realistic document *)
  let doc_buf = Buffer.create 1_000_000 in
  for i = 1 to 10000 do
    Buffer.add_string doc_buf
      (Printf.sprintf
         "This is sentence number %d in the test document. It contains some \
          text that exercises the sentence splitter with periods and uppercase \
          letters. "
         i)
  done;
  let doc = Buffer.contents doc_buf in
  let doc_bytes = String.length doc in
  let iters = 100 in
  let t4 = Unix.gettimeofday () in
  for _ = 1 to iters do
    ignore (Latex_parse_lib.Sentence_split.split doc)
  done;
  let t5 = Unix.gettimeofday () in
  let ss_elapsed = t5 -. t4 in
  let total_mib = float_of_int (doc_bytes * iters) /. (1024.0 *. 1024.0) in
  let mib_per_sec = total_mib /. ss_elapsed in
  Printf.printf "\n  [sentence-split] %d bytes × %d iters = %.1f MiB\n%!"
    doc_bytes iters total_mib;
  Printf.printf "  [sentence-split] Elapsed: %.3fs\n%!" ss_elapsed;
  Printf.printf "  [sentence-split] Throughput: %.1f MiB/s\n%!" mib_per_sec;
  Printf.printf "  [sentence-split] Target: 50 MiB/s → %s\n%!"
    (if mib_per_sec >= 50.0 then "PASS" else "BELOW TARGET");

  Printf.printf "\n[test_throughput] Done\n%!"
