(* Proof-Farm Infrastructure Foundation - LaTeX Perfectionist v25 *)
(* Distributed proof verification system for formal verification at scale *)

open Unix

(* Proof job specification *)
type proof_job = {
  id: string;
  coq_file: string;
  dependencies: string list;
  priority: int;  (* 0-9, higher = more urgent *)
  timeout_ms: int;
  retry_count: int;
}

(* Worker status *)
type worker_status = 
  | Idle
  | Busy of proof_job
  | Failed of string
  | Terminated

(* Worker node *)
type worker = {
  id: string;
  hostname: string;
  port: int;
  mutable status: worker_status;
  mutable last_heartbeat: float;
  mutable jobs_completed: int;
  mutable jobs_failed: int;
}

(* Job result *)
type job_result = 
  | Success of {
      job_id: string;
      worker_id: string;
      time_ms: float;
      admits_found: int;
      proof_terms: string list;
    }
  | Failure of {
      job_id: string;
      worker_id: string;
      error: string;
      time_ms: float;
    }
  | Timeout of {
      job_id: string;
      worker_id: string;
      timeout_ms: int;
    }

(* Farm configuration *)
type farm_config = {
  max_workers: int;
  heartbeat_interval_ms: int;
  job_queue_size: int;
  result_cache_size: int;
  checkpoint_interval_s: int;
}

(* Farm state *)
type farm_state = {
  config: farm_config;
  mutable workers: worker list;
  mutable job_queue: proof_job Queue.t;
  mutable active_jobs: (string, proof_job * worker) Hashtbl.t;
  mutable completed_jobs: (string, job_result) Hashtbl.t;
  mutable total_jobs_submitted: int;
  mutable total_jobs_completed: int;
  mutable total_jobs_failed: int;
  mutable start_time: float;
}

(* Default configuration *)
let default_config = {
  max_workers = 128;  (* As per spec: 128-pod farm *)
  heartbeat_interval_ms = 5000;
  job_queue_size = 10000;
  result_cache_size = 1000;
  checkpoint_interval_s = 300;  (* 5 minutes *)
}

(* Create farm state *)
let create_farm ?(config=default_config) () = {
  config;
  workers = [];
  job_queue = Queue.create ();
  active_jobs = Hashtbl.create 256;
  completed_jobs = Hashtbl.create config.result_cache_size;
  total_jobs_submitted = 0;
  total_jobs_completed = 0;
  total_jobs_failed = 0;
  start_time = Unix.gettimeofday ();
}

(* Register worker *)
let register_worker farm hostname port =
  let worker = {
    id = Printf.sprintf "worker-%s-%d-%d" hostname port (Random.int 99999);
    hostname;
    port;
    status = Idle;
    last_heartbeat = Unix.gettimeofday ();
    jobs_completed = 0;
    jobs_failed = 0;
  } in
  farm.workers <- worker :: farm.workers;
  Printf.printf "Registered worker: %s (%s:%d)\n" worker.id hostname port;
  worker

(* Submit proof job *)
let submit_job farm job =
  Queue.add job farm.job_queue;
  farm.total_jobs_submitted <- farm.total_jobs_submitted + 1;
  Printf.printf "Submitted job: %s (priority=%d, queue_size=%d)\n" 
    job.id job.priority (Queue.length farm.job_queue)

(* Find idle worker *)
let find_idle_worker farm =
  List.find_opt (fun w -> w.status = Idle) farm.workers

(* Assign job to worker *)
let assign_job farm worker job =
  worker.status <- Busy job;
  Hashtbl.add farm.active_jobs job.id (job, worker);
  Printf.printf "Assigned job %s to worker %s\n" job.id worker.id

(* Complete job *)
let complete_job farm job_id result =
  (match Hashtbl.find_opt farm.active_jobs job_id with
   | Some (_job, worker) ->
       worker.status <- Idle;
       (match result with
        | Success _ -> 
            worker.jobs_completed <- worker.jobs_completed + 1;
            farm.total_jobs_completed <- farm.total_jobs_completed + 1
        | Failure _ | Timeout _ ->
            worker.jobs_failed <- worker.jobs_failed + 1;
            farm.total_jobs_failed <- farm.total_jobs_failed + 1);
       Hashtbl.remove farm.active_jobs job_id
   | None -> ());
  
  Hashtbl.replace farm.completed_jobs job_id result;
  
  (* Evict old results if cache is full *)
  if Hashtbl.length farm.completed_jobs > farm.config.result_cache_size then
    let oldest_key = ref None in
    Hashtbl.iter (fun k _v ->
      match !oldest_key with
      | None -> oldest_key := Some k
      | Some _ -> ()  (* Simple FIFO for now *)
    ) farm.completed_jobs;
    (match !oldest_key with
     | Some k -> Hashtbl.remove farm.completed_jobs k
     | None -> ())

(* Schedule jobs *)
let schedule_jobs farm =
  let rec schedule () =
    if not (Queue.is_empty farm.job_queue) then
      match find_idle_worker farm with
      | Some worker ->
          let job = Queue.pop farm.job_queue in
          assign_job farm worker job;
          schedule ()
      | None -> ()
  in
  schedule ()

(* Process heartbeats and detect failed workers *)
let process_heartbeats farm =
  let current_time = Unix.gettimeofday () in
  let timeout = float_of_int farm.config.heartbeat_interval_ms /. 1000. *. 3. in
  
  List.iter (fun worker ->
    if current_time -. worker.last_heartbeat > timeout then begin
      Printf.printf "Worker %s timed out (no heartbeat for %.1fs)\n" 
        worker.id (current_time -. worker.last_heartbeat);
      
      (* Move job back to queue if worker was busy *)
      (match worker.status with
       | Busy job ->
           Printf.printf "Requeuing job %s from failed worker %s\n" job.id worker.id;
           Queue.add job farm.job_queue;
           Hashtbl.remove farm.active_jobs job.id
       | _ -> ());
      
      worker.status <- Failed "heartbeat_timeout"
    end
  ) farm.workers

(* Update worker heartbeat *)
let update_heartbeat farm worker_id =
  match List.find_opt (fun w -> w.id = worker_id) farm.workers with
  | Some worker ->
      worker.last_heartbeat <- Unix.gettimeofday ()
  | None ->
      Printf.printf "Unknown worker: %s\n" worker_id

(* Get farm statistics *)
type farm_stats = {
  total_workers: int;
  idle_workers: int;
  busy_workers: int;
  failed_workers: int;
  queue_size: int;
  active_jobs: int;
  jobs_submitted: int;
  jobs_completed: int;
  jobs_failed: int;
  uptime_hours: float;
  throughput_per_hour: float;
  success_rate: float;
}

let get_stats farm =
  let count_status status =
    List.length (List.filter (fun w -> 
      match w.status, status with
      | Idle, `Idle -> true
      | Busy _, `Busy -> true
      | Failed _, `Failed -> true
      | Terminated, `Terminated -> true
      | _ -> false
    ) farm.workers)
  in
  
  let uptime = (Unix.gettimeofday () -. farm.start_time) /. 3600. in
  let throughput = if uptime > 0. then 
    float_of_int farm.total_jobs_completed /. uptime 
  else 0. in
  let success_rate = if farm.total_jobs_completed + farm.total_jobs_failed > 0 then
    float_of_int farm.total_jobs_completed /. 
    float_of_int (farm.total_jobs_completed + farm.total_jobs_failed)
  else 0. in
  
  {
    total_workers = List.length farm.workers;
    idle_workers = count_status `Idle;
    busy_workers = count_status `Busy;
    failed_workers = count_status `Failed;
    queue_size = Queue.length farm.job_queue;
    active_jobs = Hashtbl.length farm.active_jobs;
    jobs_submitted = farm.total_jobs_submitted;
    jobs_completed = farm.total_jobs_completed;
    jobs_failed = farm.total_jobs_failed;
    uptime_hours = uptime;
    throughput_per_hour = throughput;
    success_rate = success_rate;
  }

(* Pretty print statistics *)
let pp_stats stats =
  Printf.printf "=== Proof Farm Statistics ===\n";
  Printf.printf "Workers: %d total (%d idle, %d busy, %d failed)\n" 
    stats.total_workers stats.idle_workers stats.busy_workers stats.failed_workers;
  Printf.printf "Jobs: %d submitted, %d completed, %d failed\n"
    stats.jobs_submitted stats.jobs_completed stats.jobs_failed;
  Printf.printf "Queue: %d pending, %d active\n" 
    stats.queue_size stats.active_jobs;
  Printf.printf "Performance: %.1f jobs/hour, %.1f%% success rate\n"
    stats.throughput_per_hour (stats.success_rate *. 100.);
  Printf.printf "Uptime: %.2f hours\n" stats.uptime_hours

(* Checkpoint farm state to disk *)
let checkpoint_farm farm path =
  try
    let oc = open_out_bin path in
    Marshal.to_channel oc farm [];
    close_out oc;
    Printf.printf "Checkpointed farm state to %s\n" path
  with exn ->
    Printf.printf "Failed to checkpoint: %s\n" (Printexc.to_string exn)

(* Restore farm state from disk *)
let restore_farm path =
  try
    let ic = open_in_bin path in
    let farm = Marshal.from_channel ic in
    close_in ic;
    Printf.printf "Restored farm state from %s\n" path;
    Some farm
  with exn ->
    Printf.printf "Failed to restore: %s\n" (Printexc.to_string exn);
    None

(* Main farm loop (for testing) *)
let run_farm_loop farm duration_s =
  let end_time = Unix.gettimeofday () +. float_of_int duration_s in
  
  let rec loop () =
    if Unix.gettimeofday () < end_time then begin
      (* Schedule available jobs *)
      schedule_jobs farm;
      
      (* Process heartbeats *)
      process_heartbeats farm;
      
      (* Sleep briefly *)
      Unix.sleepf 0.1;
      
      loop ()
    end
  in
  loop ();
  
  (* Final statistics *)
  let stats = get_stats farm in
  pp_stats stats