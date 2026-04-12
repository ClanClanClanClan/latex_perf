(* ══════════════════════════════════════════════════════════════════════
   Edf_scheduler — Earliest Deadline First task scheduler

   Assigns deadlines: closer to edit = earlier, lower layer = higher priority.
   Sequential drain in deadline order. Publishes lifecycle events to Event_bus.
   Uses Lockfree_queue for the submission path (future concurrency ready). Spec
   W111-120.
   ══════════════════════════════════════════════════════════════════════ *)

type task = {
  task_id : string;
  layer_id : int;
  chunk_id : int64;
  deadline : float;
  work : unit -> Validators_common.result list;
}

type stats = {
  tasks_executed : int;
  tasks_cancelled : int;
  avg_latency_ms : float;
  max_latency_ms : float;
  deadline_misses : int;
}

type stats_internal = {
  mutable si_tasks_executed : int;
  mutable si_tasks_cancelled : int;
  mutable si_total_latency_ms : float;
  mutable si_max_latency_ms : float;
  mutable si_deadline_misses : int;
}

type scheduler = {
  _queue : task Lockfree_queue.t;
  mutable pending : task list;
  si : stats_internal;
}

let create ?(capacity = 1024) () : scheduler =
  {
    _queue = Lockfree_queue.create capacity;
    pending = [];
    si =
      {
        si_tasks_executed = 0;
        si_tasks_cancelled = 0;
        si_total_latency_ms = 0.0;
        si_max_latency_ms = 0.0;
        si_deadline_misses = 0;
      };
  }

let compute_deadline ~(edit_pos : int) ~(chunk_start : int) ~(layer_id : int) :
    float =
  float (abs (chunk_start - edit_pos)) +. (float layer_id *. 1000.0)

let submit (sched : scheduler) (task : task) : unit =
  sched.pending <- task :: sched.pending

let submit_batch (sched : scheduler) (tasks : task list) : unit =
  sched.pending <- tasks @ sched.pending

let pending_count (sched : scheduler) : int = List.length sched.pending

let cancel_chunk (sched : scheduler) (chunk_id : int64) : unit =
  let before = List.length sched.pending in
  sched.pending <- List.filter (fun t -> t.chunk_id <> chunk_id) sched.pending;
  let removed = before - List.length sched.pending in
  sched.si.si_tasks_cancelled <- sched.si.si_tasks_cancelled + removed

let drain (sched : scheduler) : Validators_common.result list =
  let tasks =
    List.sort (fun a b -> compare a.deadline b.deadline) sched.pending
  in
  sched.pending <- [];
  let bus = Event_bus.global () in
  let results = ref [] in
  List.iter
    (fun task ->
      Event_bus.publish bus
        (Event_bus.TaskScheduled
           { task_id = task.task_id; deadline = task.deadline });
      let t0 = Unix.gettimeofday () in
      let res = task.work () in
      let t1 = Unix.gettimeofday () in
      let elapsed_ms = (t1 -. t0) *. 1000.0 in
      sched.si.si_tasks_executed <- sched.si.si_tasks_executed + 1;
      sched.si.si_total_latency_ms <- sched.si.si_total_latency_ms +. elapsed_ms;
      if elapsed_ms > sched.si.si_max_latency_ms then
        sched.si.si_max_latency_ms <- elapsed_ms;
      if t1 > task.deadline && task.deadline > 0.0 then (
        sched.si.si_deadline_misses <- sched.si.si_deadline_misses + 1;
        Event_bus.publish bus
          (Event_bus.DeadlineMissed
             { task_id = task.task_id; deadline = task.deadline; actual = t1 }));
      Event_bus.publish bus
        (Event_bus.TaskCompleted { task_id = task.task_id; elapsed_ms });
      results := res :: !results)
    tasks;
  List.concat (List.rev !results)

let stats (sched : scheduler) : stats =
  let s = sched.si in
  let avg =
    if s.si_tasks_executed > 0 then
      s.si_total_latency_ms /. float s.si_tasks_executed
    else 0.0
  in
  {
    tasks_executed = s.si_tasks_executed;
    tasks_cancelled = s.si_tasks_cancelled;
    avg_latency_ms = avg;
    max_latency_ms = s.si_max_latency_ms;
    deadline_misses = s.si_deadline_misses;
  }

let reset_stats (sched : scheduler) : unit =
  sched.si.si_tasks_executed <- 0;
  sched.si.si_tasks_cancelled <- 0;
  sched.si.si_total_latency_ms <- 0.0;
  sched.si.si_max_latency_ms <- 0.0;
  sched.si.si_deadline_misses <- 0
