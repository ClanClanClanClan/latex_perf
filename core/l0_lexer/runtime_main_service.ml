open Unix
let () = Simd_guard.require ()

let unlink_if_exists p = try Unix.unlink p with _ -> ()
let rec read_exact fd b o l =
  if l=0 then () else
  try let n=Unix.read fd b o l in if n=0 then failwith "client eof" else read_exact fd b (o+n) (l-n)
  with Unix.Unix_error (Unix.EINTR,_,_) -> read_exact fd b o l
let rec write_all fd b o l =
  if l=0 then () else
  try let n=Unix.write fd b o l in if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)
  with Unix.Unix_error (Unix.EINTR,_,_) -> write_all fd b o l

let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore

let run () =
  let sock_path = Config.service_sock_path in
  unlink_if_exists sock_path;
  (match Sys.getenv_opt "L0_PROM" with
   | Some "1" -> ignore (Thread.create Metrics_prometheus.serve ())
   | _ -> ());
  let srv = Unix.socket PF_UNIX SOCK_STREAM 0 in
  Unix.set_close_on_exec srv;
  Unix.bind srv (ADDR_UNIX sock_path); Unix.listen srv 64;
  prerr_endline ("[svc] listening at "^sock_path);

  let parse_cores s =
    try s |> String.split_on_char ',' |> List.map int_of_string |> Array.of_list
    with _ -> Config.pool_cores
  in
  let cores = match Sys.getenv_opt "L0_POOL_CORES" with
    | Some s -> parse_cores s
    | None -> Config.pool_cores in
  let pool = Broker.init_pool cores in

  let tail_csv_keep = Config.tail_trace_keep in
  let slow = ref ([] : (float * (int64*int64*int64*int64*int64*int64*bool*string)) list) in
  let slow_mu = Mutex.create () in
  let add_slowest ms row =
    Mutex.lock slow_mu;
    let xs = (ms, row) :: !slow |> List.sort (fun (a,_) (b,_) -> compare b a) in
    let rec take n = function []->[] | _ when n=0 -> [] | y::ys -> y::take (n-1) ys in
    slow := take tail_csv_keep xs;
    Mutex.unlock slow_mu
  in
  let dump_csv () =
    Mutex.lock slow_mu;
    (try
       let oc = open_out Config.tail_csv_path in
       output_string oc "ms_total,t_in_start,t_in_done,t_proc_start,t_hedge_fire,t_first_reply,t_reply_ready,hedged,origin\n";
       List.iter (fun (ms,(a,b,c,d,e,f,h,origin)) ->
         Printf.fprintf oc "%.3f,%Ld,%Ld,%Ld,%Ld,%Ld,%Ld,%d,%s\n" ms a b c d e f (if h then 1 else 0) origin)
         (List.rev !slow);
       close_out oc
     with _ -> ());
    Mutex.unlock slow_mu
  in

  let handle_conn c =
    let rec loop () =
      let hdr = Bytes.create 4 in
      (try read_exact c hdr 0 4 with _ -> raise Exit);
      let len =
        ((Char.code (Bytes.get hdr 0)) lsl 24)
        lor ((Char.code (Bytes.get hdr 1)) lsl 16)
        lor ((Char.code (Bytes.get hdr 2)) lsl 8)
        lor (Char.code (Bytes.get hdr 3))
      in
      if len <= 0 || len > Config.max_req_bytes then raise Exit;
      let req = Bytes.create len in read_exact c req 0 len;

      let recv () = req in
      let last_result : Broker.svc_result option ref = ref None in
      let process (req:bytes) =
        try
          let r = Broker.hedged_call pool ~input:req ~hedge_ms:Config.hedge_timer_ms_default in
          last_result := Some r;
          `Ok r
        with _ -> (last_result := None; `Err)
      in
      let put32 b off v =
        Bytes.unsafe_set b off     (Char.unsafe_chr (((v lsr 24) land 0xFF)));
        Bytes.unsafe_set b (off+1) (Char.unsafe_chr (((v lsr 16) land 0xFF)));
        Bytes.unsafe_set b (off+2) (Char.unsafe_chr (((v lsr  8) land 0xFF)));
        Bytes.unsafe_set b (off+3) (Char.unsafe_chr ( v         land 0xFF))
      in
      let format = function
        | `Ok r ->
            let b = Bytes.create 13 in
            put32 b 0 r.Broker.status;
            put32 b 4 r.Broker.n_tokens;
            put32 b 8 r.Broker.issues_len;
            Bytes.unsafe_set b 12 (match r.Broker.origin with `P->Char.unsafe_chr 1 | `H->Char.unsafe_chr 2);
            b
        | `Err ->
            let b = Bytes.create 13 in
            put32 b 0 1; put32 b 4 0; put32 b 8 0; Bytes.unsafe_set b 12 (Char.unsafe_chr 0); b
      in
      let send reply =
        let len = Bytes.length reply in
        let rhdr = Bytes.create 4 in
        Bytes.unsafe_set rhdr 0 (Char.unsafe_chr ((len lsr 24) land 0xFF));
        Bytes.unsafe_set rhdr 1 (Char.unsafe_chr ((len lsr 16) land 0xFF));
        Bytes.unsafe_set rhdr 2 (Char.unsafe_chr ((len lsr  8) land 0xFF));
        Bytes.unsafe_set rhdr 3 (Char.unsafe_chr ( len        land 0xFF));
        write_all c rhdr 0 4; write_all c reply 0 len
      in

      Metrics_prometheus.on_request ();
      let (ms, st) = Service_bracket.measure_bytes_in_to_reply_ready ~recv ~process ~format ~send in
      Metrics_prometheus.observe_latency ms;
      let hedged, status = match !last_result with
        | Some r -> (r.Broker.hedge_fired, r.Broker.status)
        | None -> (false, 1)
      in
      if status <> 0 then Metrics_prometheus.on_error ();
      add_slowest ms (st.Service_bracket.t_in_start, st.t_in_done, st.t_proc_start, st.t_hedge_fire, st.t_first_reply, st.t_reply_ready, hedged, "");
      if Broker.(pool.requests mod 10_000 = 0) then begin
        Printf.eprintf "[hedge] req=%d fired=%d (%.3f%%) wins=%d (%.1f%%) rotations=%d\n%!"
          Broker.(pool.requests) Broker.(pool.hedge_fired)
          (100.0 *. float Broker.(pool.hedge_fired) /. float (max 1 Broker.(pool.requests)))
          Broker.(pool.hedge_wins)
          (100.0 *. float Broker.(pool.hedge_wins) /. float (max 1 Broker.(pool.hedge_fired)))
          Broker.(pool.rotations);
        dump_csv ()
      end;
      loop ()
    in
    try loop () with _ -> (try Unix.close c with _ -> ())
  in

  let rec accept_loop () =
    try
      let (c,_) = Unix.accept srv in
      ignore (Thread.create handle_conn c);
      accept_loop ()
    with Unix.Unix_error (Unix.EINTR,_,_) -> accept_loop ()
  in
  accept_loop ()

let () = run ()
