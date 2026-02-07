open Unix

let setup_worker_process () =
  Qos.init_for_worker ~core:0;
  Pretouch.enable_memory_locking ();
  Gc_prep.drain_major ();
  let arena = Arena.create_arena () in
  arena

let run_worker_loop socket_path arena =
  let server_sock = Ipc.create_server_socket socket_path in
  Printf.eprintf "[Worker] Listening on %s\n%!" socket_path;

  let rec serve_loop () =
    let client_sock, _ = accept server_sock in
    (try
       let header = Ipc.recv_all client_sock 4 in
       let req_len = Int32.to_int (String.get_int32_le header 0) in
       let req_data = Ipc.recv_all client_sock req_len in
       let request = Ipc.unmarshal_request (header ^ req_data) in

       (* Pretouch memory based on estimated token count *)
       let est_tokens = Real_processor.estimate_tokens request.doc_content in
       let _active_soa = Arena.get_active_soa arena in
       Pretouch.pre_touch_ba_prefix
         (Bigarray.Array1.create Bigarray.char Bigarray.c_layout
            (est_tokens * 12))
         ~est_tokens;

       (* Process the document *)
       let t0 = Clock.now_ns () in
       let token_count, digest, _process_ns =
         Real_processor.run request.doc_content arena
       in
       let t1 = Clock.now_ns () in
       let actual_process_ns = Int64.sub t1 t0 in

       let response =
         { Ipc.token_count; digest; process_ns = actual_process_ns }
       in
       let resp_data = Ipc.marshal_response response in
       Ipc.send_all client_sock resp_data;
       close client_sock
     with e ->
       close client_sock;
       Printf.eprintf "[Worker] Error: %s\n%!" (Printexc.to_string e));
    serve_loop ()
  in
  serve_loop ()

let start_worker socket_path =
  let arena = setup_worker_process () in
  run_worker_loop socket_path arena
