(* Fault Injection Testing Framework for SIMD v2 Service *)

open Printf

(* Fault types that can be injected *)
type fault_type =
  | WorkerCrash of int (* Crash worker N *)
  | NetworkDelay of float (* Add network delay in seconds *)
  | MemoryPressure of int (* Allocate N MB of memory *)
  | CPUSpike of float (* Consume CPU for N seconds *)
  | IOBlock of float (* Block I/O for N seconds *)
  | RandomWorkerKill (* Kill random worker *)
  | BrokerOverload (* Overwhelm broker with requests *)

(* Fault injection configuration *)
type fault_config = {
  enabled : bool;
  probability : float; (* 0.0 to 1.0 *)
  faults : fault_type list;
  seed : int option;
}

(* Global fault injection state *)
let config =
  ref { enabled = false; probability = 0.0; faults = []; seed = None }

(* Initialize random generator with optional seed *)
let init_random seed_opt =
  match seed_opt with
  | Some seed -> Random.init seed
  | None -> Random.self_init ()

(* Check if fault should be triggered based on probability *)
let should_inject_fault () =
  !config.enabled && Random.float 1.0 < !config.probability

(* Inject worker crash fault *)
let inject_worker_crash worker_id =
  eprintf "[FAULT] Injecting worker crash for worker %d\n%!" worker_id;
  (* Send SIGKILL to worker process *)
  try
    Unix.kill worker_id Sys.sigkill;
    eprintf "[FAULT] Worker %d killed\n%!" worker_id
  with Unix.Unix_error (err, _, _) ->
    eprintf "[FAULT] Failed to kill worker %d: %s\n%!" worker_id
      (Unix.error_message err)

(* Inject network delay *)
let inject_network_delay delay_seconds =
  eprintf "[FAULT] Injecting network delay of %.2fs\n%!" delay_seconds;
  Thread.delay delay_seconds

(* Inject memory pressure *)
let inject_memory_pressure mb_count =
  eprintf "[FAULT] Injecting memory pressure: %d MB\n%!" mb_count;
  (* Allocate and hold memory *)
  let size = mb_count * 1024 * 1024 in
  let _buffer = Bytes.create size in
  (* Fill buffer to ensure allocation *)
  Bytes.fill _buffer 0 size 'X';
  eprintf "[FAULT] Memory pressure applied\n%!"

(* Inject CPU spike *)
let inject_cpu_spike duration =
  eprintf "[FAULT] Injecting CPU spike for %.2fs\n%!" duration;
  let start_time = Unix.gettimeofday () in
  while Unix.gettimeofday () -. start_time < duration do
    (* Busy loop to consume CPU *)
    for _ = 1 to 1000000 do
      ignore (Random.int 1000)
    done
  done;
  eprintf "[FAULT] CPU spike completed\n%!"

(* Inject I/O block *)
let inject_io_block duration =
  eprintf "[FAULT] Injecting I/O block for %.2fs\n%!" duration;
  (* Block on a pipe read that will timeout *)
  let read_fd, write_fd = Unix.pipe () in
  Unix.set_close_on_exec read_fd;
  Unix.set_close_on_exec write_fd;

  let start_time = Unix.gettimeofday () in
  try
    (* Set non-blocking and try to read *)
    Unix.set_nonblock read_fd;
    while Unix.gettimeofday () -. start_time < duration do
      Thread.delay 0.1;
      try
        let buffer = Bytes.create 1 in
        ignore (Unix.read read_fd buffer 0 1)
      with Unix.Unix_error (Unix.EAGAIN, _, _) -> ()
    done
  with _ ->
    ();

    Unix.close read_fd;
    Unix.close write_fd;
    eprintf "[FAULT] I/O block completed\n%!"

(* Kill a random worker from the pool *)
let inject_random_worker_kill worker_pids =
  match worker_pids with
  | [] -> eprintf "[FAULT] No workers to kill\n%!"
  | pids ->
      let idx = Random.int (List.length pids) in
      let pid = List.nth pids idx in
      inject_worker_crash pid

(* Overwhelm broker with rapid requests *)
let inject_broker_overload socket_path request_count =
  eprintf "[FAULT] Injecting broker overload with %d requests\n%!" request_count;

  (* Create multiple connections and send requests rapidly *)
  let send_flood_request i =
    try
      let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      Unix.connect sock (Unix.ADDR_UNIX socket_path);

      (* Send minimal request *)
      let request = sprintf "FLOOD_%d" i in
      let len = String.length request in
      let header = Bytes.create 4 in
      Bytes.set header 0 (char_of_int (len land 0xff));
      Bytes.set header 1 (char_of_int ((len lsr 8) land 0xff));
      Bytes.set header 2 (char_of_int ((len lsr 16) land 0xff));
      Bytes.set header 3 (char_of_int ((len lsr 24) land 0xff));

      ignore (Unix.write sock header 0 4);
      ignore (Unix.write sock (Bytes.of_string request) 0 len);

      Unix.close sock
    with _ -> ()
  in

  (* Send requests in parallel threads *)
  let threads = ref [] in
  for i = 1 to request_count do
    let t = Thread.create send_flood_request i in
    threads := t :: !threads
  done;

  (* Wait for all threads *)
  List.iter Thread.join !threads;
  eprintf "[FAULT] Broker overload completed\n%!"

(* Main fault injection function *)
let inject_fault fault_type =
  if should_inject_fault () then
    match fault_type with
    | WorkerCrash pid -> inject_worker_crash pid
    | NetworkDelay delay -> inject_network_delay delay
    | MemoryPressure mb -> inject_memory_pressure mb
    | CPUSpike duration -> inject_cpu_spike duration
    | IOBlock duration -> inject_io_block duration
    | RandomWorkerKill -> eprintf "[FAULT] Random kill requires worker list\n%!"
    | BrokerOverload ->
        eprintf "[FAULT] Broker overload requires socket path\n%!"

(* Configure fault injection *)
let configure ~enabled ~probability ~faults ~seed =
  config := { enabled; probability; faults; seed };
  init_random seed;
  eprintf "[FAULT] Fault injection configured: enabled=%b, probability=%.2f\n%!"
    enabled probability

(* Run fault injection test scenario *)
let run_scenario scenario_name worker_pids socket_path =
  eprintf "[FAULT] Running scenario: %s\n%!" scenario_name;

  match scenario_name with
  | "worker_chaos" ->
      (* Randomly kill workers during operation *)
      configure ~enabled:true ~probability:0.1 ~faults:[ RandomWorkerKill ]
        ~seed:(Some 42);
      for _ = 1 to 10 do
        Thread.delay 1.0;
        if should_inject_fault () then inject_random_worker_kill worker_pids
      done
  | "network_issues" ->
      (* Simulate network delays *)
      configure ~enabled:true ~probability:0.2 ~faults:[ NetworkDelay 0.5 ]
        ~seed:(Some 42);
      for _ = 1 to 20 do
        Thread.delay 0.5;
        inject_fault (NetworkDelay (Random.float 1.0))
      done
  | "resource_stress" ->
      (* Memory and CPU pressure *)
      configure ~enabled:true ~probability:0.3
        ~faults:[ MemoryPressure 100; CPUSpike 0.5 ]
        ~seed:(Some 42);
      inject_fault (MemoryPressure 200);
      Thread.delay 1.0;
      inject_fault (CPUSpike 2.0)
  | "broker_flood" ->
      (* Overwhelm broker with requests *)
      configure ~enabled:true ~probability:1.0 ~faults:[ BrokerOverload ]
        ~seed:(Some 42);
      inject_broker_overload socket_path 1000
  | "combined_chaos" ->
      (* All faults combined *)
      configure ~enabled:true ~probability:0.15
        ~faults:
          [
            WorkerCrash 0;
            NetworkDelay 0.2;
            MemoryPressure 50;
            CPUSpike 0.1;
            IOBlock 0.1;
          ]
        ~seed:(Some 42);

      for i = 1 to 100 do
        Thread.delay 0.1;
        let fault = List.nth !config.faults (Random.int 5) in
        inject_fault fault;

        (* Occasionally kill a worker *)
        if i mod 20 = 0 && worker_pids <> [] then
          inject_random_worker_kill worker_pids
      done
  | _ -> eprintf "[FAULT] Unknown scenario: %s\n%!" scenario_name

(* Check if system recovered from faults *)
let check_recovery socket_path =
  eprintf "[FAULT] Checking system recovery...\n%!";

  try
    (* Try to connect and send a test request *)
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX socket_path);

    (* Send health check *)
    let request = "HEALTH_CHECK" in
    let len = String.length request in
    let header = Bytes.create 4 in
    Bytes.set header 0 (char_of_int (len land 0xff));
    Bytes.set header 1 (char_of_int ((len lsr 8) land 0xff));
    Bytes.set header 2 (char_of_int ((len lsr 16) land 0xff));
    Bytes.set header 3 (char_of_int ((len lsr 24) land 0xff));

    ignore (Unix.write sock header 0 4);
    ignore (Unix.write sock (Bytes.of_string request) 0 len);

    (* Try to read response *)
    let response_header = Bytes.create 4 in
    let n = Unix.read sock response_header 0 4 in

    Unix.close sock;

    if n = 4 then (
      eprintf "[FAULT] System recovered successfully ✓\n%!";
      true)
    else (
      eprintf "[FAULT] System partially recovered\n%!";
      false)
  with exn ->
    eprintf "[FAULT] System not recovered: %s\n%!" (Printexc.to_string exn);
    false

(* Export for use in other modules *)
let is_enabled () = !config.enabled
let get_probability () = !config.probability

let trigger_random_fault () =
  if should_inject_fault () && !config.faults <> [] then
    let fault =
      List.nth !config.faults (Random.int (List.length !config.faults))
    in
    inject_fault fault
