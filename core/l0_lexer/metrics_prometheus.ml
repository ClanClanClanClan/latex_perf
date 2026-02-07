open Unix
open Printf

(* Minimal Prometheus exporter; enable with L0_PROM=1. Configuration: -
   L0_PROM_ADDR = "HOST:PORT" (default 127.0.0.1:9109) - L0_PROM_UDS =
   "/path/to/socket" (serve over Unix domain socket) If both are set, UDS takes
   precedence. *)

let default_port = 9109
let default_host = inet_addr_loopback

let parse_addr s =
  match String.split_on_char ':' s with
  | [ h; p ] ->
      let host =
        try inet_addr_of_string h
        with _ -> (* fallback to loopback on parse failure *) default_host
      in
      let port = try int_of_string p with _ -> default_port in
      (host, port)
  | _ -> (default_host, default_port)

let mu = Mutex.create ()
let c_requests = ref 0
let c_errors = ref 0
let c_hedge_fired = ref 0
let c_hedge_wins = ref 0
let c_rotations = ref 0

(* latency histogram buckets (ms): [0,5), [5,10), [10,15), [15,20), [20,30),
   [30,50), [50,+inf) *)
let buckets = [| 5.; 10.; 15.; 20.; 30.; 50. |]
let h_counts = Array.make (Array.length buckets + 1) 0

let observe_latency ms =
  Mutex.lock mu;
  let rec idx i =
    if i >= Array.length buckets then Array.length buckets
    else if ms < buckets.(i) then i
    else idx (i + 1)
  in
  let i = idx 0 in
  h_counts.(i) <- h_counts.(i) + 1;
  Mutex.unlock mu

let inc r = incr r

let on_request () =
  Mutex.lock mu;
  inc c_requests;
  Mutex.unlock mu

let on_error () =
  Mutex.lock mu;
  inc c_errors;
  Mutex.unlock mu

let on_hedge_fired () =
  Mutex.lock mu;
  inc c_hedge_fired;
  Mutex.unlock mu

let on_hedge_win () =
  Mutex.lock mu;
  inc c_hedge_wins;
  Mutex.unlock mu

let on_rotation () =
  Mutex.lock mu;
  inc c_rotations;
  Mutex.unlock mu

let dump_metrics oc =
  Mutex.lock mu;
  fprintf oc
    "# HELP l0_requests_total total requests\n\
     # TYPE l0_requests_total counter\n\
     l0_requests_total %d\n"
    !c_requests;
  fprintf oc
    "# HELP l0_errors_total error responses\n\
     # TYPE l0_errors_total counter\n\
     l0_errors_total %d\n"
    !c_errors;
  fprintf oc
    "# HELP l0_hedge_fired_total hedges fired\n\
     # TYPE l0_hedge_fired_total counter\n\
     l0_hedge_fired_total %d\n"
    !c_hedge_fired;
  fprintf oc
    "# HELP l0_hedge_wins_total hedge wins\n\
     # TYPE l0_hedge_wins_total counter\n\
     l0_hedge_wins_total %d\n"
    !c_hedge_wins;
  fprintf oc
    "# HELP l0_rotations_total worker rotations\n\
     # TYPE l0_rotations_total counter\n\
     l0_rotations_total %d\n"
    !c_rotations;
  fprintf oc
    "# HELP l0_latency_ms latency histogram (ms)\n\
     # TYPE l0_latency_ms histogram\n";
  let sum = Array.fold_left ( + ) 0 h_counts in
  let accum = ref 0 in
  Array.iteri
    (fun i _ ->
      accum := !accum + h_counts.(i);
      fprintf oc "l0_latency_ms_bucket{le=\"%.0f\"} %d\n" buckets.(i) !accum)
    buckets;
  fprintf oc "l0_latency_ms_bucket{le=\"+Inf\"} %d\nl0_latency_ms_count %d\n"
    sum sum;
  Mutex.unlock mu

let serve () =
  let uds_opt = Sys.getenv_opt "L0_PROM_UDS" in
  let tcp_opt = Sys.getenv_opt "L0_PROM_ADDR" in
  let serve_tcp ~host ~port =
    let fd = socket PF_INET SOCK_STREAM 0 in
    setsockopt fd SO_REUSEADDR true;
    bind fd (ADDR_INET (host, port));
    listen fd 64;
    eprintf "[prom] http://127.0.0.1:%d/metrics\n%!" port;
    let rec loop () =
      let c, _ = accept fd in
      ignore
        (Thread.create
           (fun cfd ->
             let buf = Bytes.create 1024 in
             ignore (Unix.read cfd buf 0 1024);
             let oc = out_channel_of_descr cfd in
             output_string oc
               "HTTP/1.1 200 OK\r\n\
                Content-Type: text/plain; version=0.0.4\r\n\
                \r\n";
             dump_metrics oc;
             flush oc;
             try close_out oc with _ -> ())
           c);
      loop ()
    in
    loop ()
  in
  let serve_uds path =
    (try Unix.unlink path with _ -> ());
    let fd = socket PF_UNIX SOCK_STREAM 0 in
    bind fd (ADDR_UNIX path);
    listen fd 64;
    eprintf
      "[prom] uds://%s (curl --unix-socket %s http://localhost/metrics)\n%!"
      path path;
    let rec loop () =
      let c, _ = accept fd in
      ignore
        (Thread.create
           (fun cfd ->
             let buf = Bytes.create 1024 in
             ignore (Unix.read cfd buf 0 1024);
             let oc = out_channel_of_descr cfd in
             output_string oc
               "HTTP/1.1 200 OK\r\n\
                Content-Type: text/plain; version=0.0.4\r\n\
                \r\n";
             dump_metrics oc;
             flush oc;
             try close_out oc with _ -> ())
           c);
      loop ()
    in
    loop ()
  in
  (* Prefer UDS if provided, else TCP *)
  try
    match uds_opt with
    | Some p when p <> "" -> serve_uds p
    | _ ->
        let h, p =
          match tcp_opt with
          | Some s -> parse_addr s
          | None -> (default_host, default_port)
        in
        serve_tcp ~host:h ~port:p
  with Unix_error (e, _, _) ->
    eprintf "[prom] bind failed: %s (metrics disabled)\n%!" (error_message e)
