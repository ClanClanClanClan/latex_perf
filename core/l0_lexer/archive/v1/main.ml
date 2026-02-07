(* src/main.ml *)

let () =
  (* Parse CLI: cores list, hedge timer override, pool size *)
  let cores = [| 2; 3; 6; 7 |] in
  (* pin across physical cores *)
  let pool = Broker.init_pool ~cores in
  (* Read stdin for file paths (perf harness), or expose a simple TCP proxy to
     accept requests *)
  let rec serve () =
    match input_line stdin with
    | file -> (
        let ch = open_in_bin file in
        let len = in_channel_length ch in
        let buf = really_input_string ch len in
        close_in ch;
        match
          Broker.hedged_request pool
            ~input:(Bytes.unsafe_of_string buf)
            ~hedge_ns:Config.hedge_timer_ns_default
        with
        | `Ok (st, nt, iss, mb10, maj, origin) ->
            Printf.printf
              "OK status=%d tokens=%d issues=%d alloc_mb=%.1f major=%d origin=%s\n\
               %!"
              st nt iss
              (float mb10 /. 10.0)
              maj
              (match origin with `Primary -> "P" | `Hedged -> "H");
            serve ()
        | `Timeout ->
            Printf.printf "TIMEOUT\n%!";
            serve ()
        | `Error ->
            Printf.printf "ERROR\n%!";
            serve ())
    | exception End_of_file -> ()
  in
  serve ()
