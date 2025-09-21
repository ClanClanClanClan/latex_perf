(* Enhanced main service demonstrating SIMD.md § 3.6 timing and advanced features *)

open Unix
open L0_lexer

let unlink_if_exists p = try Unix.unlink p with _ -> ()

let rec read_exact fd b o l =
  if l=0 then () else
  let n = Unix.read fd b o l in
  if n=0 then failwith "client eof" else read_exact fd b (o+n) (l-n)
let rec write_all fd b o l =
  if l=0 then () else
  let n = Unix.write fd b o l in
  if n=0 then failwith "short write" else write_all fd b (o+n) (l-n)

let run () =
  Simd_caps.enforce_in_ci ();

  let sock_path = Config.service_sock_path in
  unlink_if_exists sock_path;
  let srv = Unix.socket PF_UNIX SOCK_STREAM 0 in
  Unix.bind srv (ADDR_UNIX sock_path); Unix.listen srv 64;
  prerr_endline (Printf.sprintf "[Enhanced Service] listening at %s" sock_path);

  let pool = Broker.init_pool [|0;1|] in
  let metrics = Metrics_logger.create ~keep:Config.tail_trace_keep in

  let rec accept_loop () =
    let (c,_) = Unix.accept srv in

    let recv () =
      let hdr = Bytes.create 4 in
      read_exact c hdr 0 4;
      let len =
        ((Char.code (Bytes.get hdr 0)) lsl 24)
        lor ((Char.code (Bytes.get hdr 1)) lsl 16)
        lor ((Char.code (Bytes.get hdr 2)) lsl 8)
        lor (Char.code (Bytes.get hdr 3))
      in
      if len > Config.max_req_bytes then failwith "req too large";
      let b = Bytes.create len in read_exact c b 0 len; b
    in

    let stamps_ref = ref (Service_bracket.make ()) in
    Broker.set_stamp_hooks pool
      ~hedge_fire:(fun t -> (!stamps_ref).Service_bracket.t_hedge_fire <- t)
      ~first_reply:(fun t -> (!stamps_ref).Service_bracket.t_first_reply <- t);

    let process req =
      Broker.hedged_call pool ~input:req ~hedge_ms:Config.hedge_timer_ms_default
    in
    let format r =
      let b = Bytes.create 13 in
      let put32 off v =
        Bytes.set b off (Char.chr ((v lsr 24) land 0xFF));
        Bytes.set b (off+1) (Char.chr ((v lsr 16) land 0xFF));
        Bytes.set b (off+2) (Char.chr ((v lsr  8) land 0xFF));
        Bytes.set b (off+3) (Char.chr ( v        land 0xFF))
      in
      put32 0 r.Broker.status; put32 4 r.n_tokens; put32 8 r.issues_len;
      Bytes.set b 12 (match r.origin with `P->'\001' | `H->'\002'); b
    in
    let send reply =
      let len = Bytes.length reply in
      let hdr = Bytes.create 4 in
      Bytes.set hdr 0 (Char.chr ((len lsr 24) land 0xFF));
      Bytes.set hdr 1 (Char.chr ((len lsr 16) land 0xFF));
      Bytes.set hdr 2 (Char.chr ((len lsr  8) land 0xFF));
      Bytes.set hdr 3 (Char.chr ( len        land 0xFF));
      write_all c hdr 0 4; write_all c reply 0 len
    in

    (* Enhanced SIMD.md § 3.6 timing measurement *)
    let (ms, st) = Service_bracket.measure_bytes_in_to_reply_ready ~recv ~process ~format ~send in
    
    (* Record to tail logger with enhanced metrics *)
    let hedged = st.Service_bracket.t_hedge_fire <> 0L in
    if hedged then Metrics_logger.bump_hedge metrics ~win:(st.Service_bracket.t_first_reply >= st.Service_bracket.t_hedge_fire);
    
    let row = {
      Metrics_logger.ms_total = ms;
      t_in_start    = st.t_in_start;
      t_in_done     = st.t_in_done;
      t_proc_start  = st.t_proc_start;
      t_hedge_fire  = st.t_hedge_fire;
      t_first_reply = st.t_first_reply;
      t_reply_ready = st.t_reply_ready;
      hedged; origin = if hedged then "H" else "P";
    } in
    Metrics_logger.note metrics row;
    Metrics_logger.set_rotations metrics pool.Broker.rotations;
    
    Unix.close c;
    
    (* Periodically dump CSV and print enhanced metrics *)
    if Random.int 1000 = 0 then begin
      Metrics_logger.dump_csv metrics Config.tail_csv_path;
      Metrics_logger.print_summary metrics
    end;
    
    (* Print enhanced timing breakdown for this request *)
    if st.t_hedge_fire <> 0L then
      Printf.eprintf "[Enhanced] %.3fms (HEDGED: fire=%Ldns, reply=%Ldns)\n%!" ms st.t_hedge_fire st.t_first_reply
    else
      Printf.eprintf "[Enhanced] %.3fms (primary: proc=%Ldns)\n%!" ms (Int64.sub st.t_first_reply st.t_proc_start);
    
    accept_loop ()
  in
  accept_loop ()

let () = run ()