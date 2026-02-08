open Unix

let () =
  Latex_parse_lib.Simd_guard.require
    () (* hard guard: refuse to start without SIMD unless L0_ALLOW_SCALAR=1 *)

let unlink_if_exists p = try Unix.unlink p with _ -> ()

let rec read_exact fd b o l =
  if l = 0 then ()
  else
    try
      let n = Unix.read fd b o l in
      if n = 0 then failwith "client eof" else read_exact fd b (o + n) (l - n)
    with Unix.Unix_error (Unix.EINTR, _, _) -> read_exact fd b o l

let rec write_all fd b o l =
  if l = 0 then ()
  else
    try
      let n = Unix.write fd b o l in
      if n = 0 then failwith "short write" else write_all fd b (o + n) (l - n)
    with Unix.Unix_error (Unix.EINTR, _, _) -> write_all fd b o l

let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore

let[@inline] put_u8 b off v =
  Bytes.unsafe_set b off (Char.unsafe_chr (v land 0xFF))

let be32_get b off =
  (Char.code (Bytes.get b off) lsl 24)
  lor (Char.code (Bytes.get b (off + 1)) lsl 16)
  lor (Char.code (Bytes.get b (off + 2)) lsl 8)
  lor Char.code (Bytes.get b (off + 3))

let be32_put b off v =
  put_u8 b off ((v lsr 24) land 0xFF);
  put_u8 b (off + 1) ((v lsr 16) land 0xFF);
  put_u8 b (off + 2) ((v lsr 8) land 0xFF);
  put_u8 b (off + 3) (v land 0xFF)

let be64_get b off =
  let open Int64 in
  let byte i = of_int (Char.code (Bytes.get b (off + i))) in
  logor
    (shift_left (byte 0) 56)
    (logor
       (shift_left (byte 1) 48)
       (logor
          (shift_left (byte 2) 40)
          (logor
             (shift_left (byte 3) 32)
             (logor
                (shift_left (byte 4) 24)
                (logor
                   (shift_left (byte 5) 16)
                   (logor (shift_left (byte 6) 8) (byte 7)))))))

let be64_put b off v =
  let open Int64 in
  put_u8 b (off + 0) (to_int (shift_right_logical v 56));
  put_u8 b (off + 1) (to_int (shift_right_logical v 48));
  put_u8 b (off + 2) (to_int (shift_right_logical v 40));
  put_u8 b (off + 3) (to_int (shift_right_logical v 32));
  put_u8 b (off + 4) (to_int (shift_right_logical v 24));
  put_u8 b (off + 5) (to_int (shift_right_logical v 16));
  put_u8 b (off + 6) (to_int (shift_right_logical v 8));
  put_u8 b (off + 7) (to_int v)

let hex_prefix b =
  let limit = min 16 (Bytes.length b) in
  let buf = Buffer.create (limit * 3) in
  for i = 0 to limit - 1 do
    if i > 0 then Buffer.add_char buf ' ';
    Buffer.add_string buf (Printf.sprintf "%02X" (Char.code (Bytes.get b i)))
  done;
  Buffer.contents buf

let run () =
  let sock_path = Latex_parse_lib.Config.service_sock_path in
  unlink_if_exists sock_path;
  (* optional Prometheus exporter *)
  (match Sys.getenv_opt "L0_PROM" with
  | Some "1" ->
      ignore (Thread.create Latex_parse_lib.Metrics_prometheus.serve ())
  | _ -> ());
  let srv = Unix.socket PF_UNIX SOCK_STREAM 0 in
  Unix.set_close_on_exec srv;
  Unix.bind srv (ADDR_UNIX sock_path);
  Unix.listen srv 64;
  prerr_endline ("[svc] listening at " ^ sock_path);

  (* Allow overriding pool cores via env: L0_POOL_CORES="0,1,2,3" *)
  let parse_cores s =
    try s |> String.split_on_char ',' |> List.map int_of_string |> Array.of_list
    with _ -> Latex_parse_lib.Config.pool_cores
  in
  let cores =
    match Sys.getenv_opt "L0_POOL_CORES" with
    | Some s -> parse_cores s
    | None -> Latex_parse_lib.Config.pool_cores
  in
  Printf.eprintf "[svc] forking workers for cores: %s\n%!"
    (String.concat "," (List.map string_of_int (Array.to_list cores)));
  let pool = Latex_parse_lib.Broker.init_pool cores in
  Printf.eprintf "[svc] pool ready, %d workers spawned\n%!"
    (Array.length Latex_parse_lib.Broker.(pool.workers));

  let tail_csv_keep = Latex_parse_lib.Config.tail_trace_keep in
  let slow =
    ref
      ([]
        : (float
          * (int64 * int64 * int64 * int64 * int64 * int64 * bool * string))
          list)
  in
  let slow_mu = Mutex.create () in
  let add_slowest ms row =
    Mutex.lock slow_mu;
    let xs =
      (ms, row) :: !slow |> List.sort (fun (a, _) (b, _) -> compare b a)
    in
    let rec take n = function
      | [] -> []
      | _ when n = 0 -> []
      | y :: ys -> y :: take (n - 1) ys
    in
    slow := take tail_csv_keep xs;
    Mutex.unlock slow_mu
  in
  let dump_csv () =
    Mutex.lock slow_mu;
    (try
       let oc = open_out Latex_parse_lib.Config.tail_csv_path in
       output_string oc
         "ms_total,t_in_start,t_in_done,t_proc_start,t_hedge_fire,t_first_reply,t_reply_ready,hedged,origin\n";
       List.iter
         (fun (ms, (a, b, c, d, e, f, h, origin)) ->
           Printf.fprintf oc "%.3f,%Ld,%Ld,%Ld,%Ld,%Ld,%Ld,%d,%s\n" ms a b c d e
             f
             (if h then 1 else 0)
             origin)
         (List.rev !slow);
       close_out oc
     with _ -> ());
    Mutex.unlock slow_mu
  in

  let handle_conn c =
    let tid = Thread.id (Thread.self ()) in
    Printf.eprintf "[svc:t%d] handle_conn entered pid=%d\n%!" tid
      (Unix.getpid ());
    (* keep-alive loop: many requests per connection *)
    let rec loop () =
      (* recv *)
      Printf.eprintf "[svc:t%d] reading hdr...\n%!" tid;
      let hdr = Bytes.create 16 in
      (try read_exact c hdr 0 16
       with e ->
         Printf.eprintf "[svc:t%d] read_exact(hdr) exn: %s\n%!" tid
           (Printexc.to_string e);
         raise Exit);
      Printf.eprintf "[svc:t%d] got hdr\n%!" tid;
      let msg_type = be32_get hdr 0 in
      if msg_type <> 1 then (
        Printf.eprintf "[svc:t%d] bad msg_type=%d\n%!" tid msg_type;
        raise Exit);
      let req_id = be64_get hdr 4 in
      let payload_len = be32_get hdr 12 in
      Printf.eprintf "[svc:t%d] recv req_id=%Ld len=%d\n%!" tid req_id
        payload_len;
      let doc_bytes_max = Latex_parse_lib.Config.max_req_bytes in
      let payload = Bytes.create payload_len in
      read_exact c payload 0 payload_len;
      let req, used_prefix =
        if payload_len >= 4 then
          let announced = be32_get payload 0 in
          if announced <= payload_len - 4 then
            (Bytes.sub payload 4 announced, true)
          else (payload, false)
        else (payload, false)
      in
      if not used_prefix then
        Format.eprintf "[svc] len prefix ignored payload_len=%d sample=%s@."
          payload_len (hex_prefix payload);
      if Bytes.length req > doc_bytes_max then raise Exit;

      let recv () = req in
      let last_result : Latex_parse_lib.Broker.svc_result option ref =
        ref None
      in
      let process (req : bytes) =
        Printf.eprintf "[svc:t%d] calling hedged_call len=%d\n%!" tid
          (Bytes.length req);
        try
          let r =
            Latex_parse_lib.Broker.hedged_call pool ~input:req
              ~hedge_ms:Latex_parse_lib.Config.hedge_timer_ms_default
          in
          Printf.eprintf "[svc:t%d] hedged_call returned status=%d\n%!" tid
            r.Latex_parse_lib.Broker.status;
          last_result := Some r;
          `Ok r
        with exn ->
          last_result := None;
          Printf.eprintf "[svc:t%d] hedged_call exn: %s len=%d sample=%s\n%!"
            tid (Printexc.to_string exn) (Bytes.length req) (hex_prefix req);
          `Err
      in
      let put32 b off v =
        Bytes.unsafe_set b off (Char.unsafe_chr ((v lsr 24) land 0xFF));
        Bytes.unsafe_set b (off + 1) (Char.unsafe_chr ((v lsr 16) land 0xFF));
        Bytes.unsafe_set b (off + 2) (Char.unsafe_chr ((v lsr 8) land 0xFF));
        Bytes.unsafe_set b (off + 3) (Char.unsafe_chr (v land 0xFF))
      in
      let format = function
        | `Ok r ->
            let status = r.Latex_parse_lib.Broker.status in
            let tokens = r.Latex_parse_lib.Broker.n_tokens in
            let issues = r.Latex_parse_lib.Broker.issues_len in
            let origin_char =
              match r.Latex_parse_lib.Broker.origin with
              | `P -> Char.unsafe_chr 1
              | `H -> Char.unsafe_chr 2
            in
            if status <> 0 then
              Format.eprintf
                "[svc] nonzero status=%d tokens=%d issues=%d origin=%c len=%d \
                 sample=%s@."
                status tokens issues
                (if origin_char = Char.unsafe_chr 1 then 'P' else 'H')
                (Bytes.length req) (hex_prefix req);
            let b = Bytes.create 13 in
            put32 b 0 status;
            put32 b 4 tokens;
            put32 b 8 issues;
            Bytes.unsafe_set b 12 origin_char;
            b
        | `Err ->
            let b = Bytes.create 13 in
            put32 b 0 1;
            put32 b 4 0;
            put32 b 8 0;
            Bytes.unsafe_set b 12 (Char.unsafe_chr 0);
            b
      in
      let send reply =
        let len = Bytes.length reply in
        let rhdr = Bytes.create 16 in
        be32_put rhdr 0 2;
        be64_put rhdr 4 req_id;
        be32_put rhdr 12 len;
        write_all c rhdr 0 16;
        write_all c reply 0 len
      in

      Latex_parse_lib.Metrics_prometheus.on_request ();
      let ms, st =
        Latex_parse_lib.Service_bracket.measure_bytes_in_to_reply_ready ~recv
          ~process ~format ~send
      in
      Latex_parse_lib.Metrics_prometheus.observe_latency ms;
      (* get actual hedge telemetry from broker result *)
      let hedged, status =
        match !last_result with
        | Some r ->
            ( r.Latex_parse_lib.Broker.hedge_fired,
              r.Latex_parse_lib.Broker.status )
        | None -> (false, 1)
      in
      if status <> 0 then Latex_parse_lib.Metrics_prometheus.on_error ();
      add_slowest ms
        ( st.Latex_parse_lib.Service_bracket.t_in_start,
          st.t_in_done,
          st.t_proc_start,
          st.t_hedge_fire,
          st.t_first_reply,
          st.t_reply_ready,
          hedged,
          "" );
      if Latex_parse_lib.Broker.(pool.requests mod 10_000 = 0) then (
        Printf.eprintf
          "[hedge] req=%d fired=%d (%.3f%%) wins=%d (%.1f%%) rotations=%d\n%!"
          Latex_parse_lib.Broker.(pool.requests)
          Latex_parse_lib.Broker.(pool.hedge_fired)
          (100.0
          *. float Latex_parse_lib.Broker.(pool.hedge_fired)
          /. float (max 1 Latex_parse_lib.Broker.(pool.requests)))
          Latex_parse_lib.Broker.(pool.hedge_wins)
          (100.0
          *. float Latex_parse_lib.Broker.(pool.hedge_wins)
          /. float (max 1 Latex_parse_lib.Broker.(pool.hedge_fired)))
          Latex_parse_lib.Broker.(pool.rotations);
        dump_csv ());
      loop ()
    in
    try loop ()
    with exn -> (
      Printf.eprintf "[svc:t%d] loop exn: %s\n%!" tid (Printexc.to_string exn);
      try Unix.close c with _ -> ())
  in

  Printf.eprintf "[svc] entering accept_loop\n%!";
  let rec accept_loop () =
    try
      let c, _ = Unix.accept srv in
      Printf.eprintf "[svc] accepted connection, spawning thread\n%!";
      (try
         ignore (Thread.create handle_conn c);
         Printf.eprintf "[svc] thread created\n%!"
       with exn -> (
         Printf.eprintf "[svc] Thread.create FAILED: %s\n%!"
           (Printexc.to_string exn);
         try Unix.close c with _ -> ()));
      accept_loop ()
    with
    | Unix.Unix_error (Unix.EINTR, _, _) -> accept_loop ()
    | exn ->
        Printf.eprintf "[svc] accept exn: %s\n%!" (Printexc.to_string exn);
        accept_loop ()
  in
  accept_loop ()

let () = run ()
