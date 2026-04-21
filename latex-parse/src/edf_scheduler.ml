(* ══════════════════════════════════════════════════════════════════════
   Edf_scheduler — priority-ordered task scheduler

   Assigns priorities: closer to edit = lower priority value = higher urgency.
   Lower layer = higher urgency. Sequential drain in priority order. Publishes
   lifecycle events to Event_bus.

   NOTE: `priority` is a relative ordering value, NOT a wall-clock deadline. It
   must never be compared against Unix time. (Expert audit fix, v26 WS0.)

   PR #241 (p1.6, memo §11.2 + §16.1): priority now includes a per-class offset
   so Class A (keystroke-critical) always outranks B (debounce) which outranks C
   (build-coupled) which outranks D (advisory). This was the missing §11.2
   scheduler wiring called out in every audit round since P1 merged. The offset
   is larger than any realistic layer/chunk component so class dominance is
   total-ordering within a drain cycle.
   ══════════════════════════════════════════════════════════════════════ *)

(** Offset added to each task's priority based on [execution_class]. Dominant
    over layer and chunk distance. *)
let class_priority_offset (ec : Rule_contract_loader.execution_class) : float =
  match ec with
  | Rule_contract_loader.A -> 0.0
  | Rule_contract_loader.B -> 1_000_000.0
  | Rule_contract_loader.C -> 2_000_000.0
  | Rule_contract_loader.D -> 3_000_000.0

type task = {
  task_id : string;
  layer_id : int;
  chunk_id : int64;
  priority : float;
  work : unit -> Validators_common.result list;
  execution_class : Rule_contract_loader.execution_class;
      (** PR #241 (p1.6): submitted tasks carry their class so [drain] can apply
          the offset at sort time. *)
}

type stats = {
  tasks_executed : int;
  tasks_cancelled : int;
  avg_latency_ms : float;
  max_latency_ms : float;
}

type stats_internal = {
  mutable si_tasks_executed : int;
  mutable si_tasks_cancelled : int;
  mutable si_total_latency_ms : float;
  mutable si_max_latency_ms : float;
}

type scheduler = { mutable pending : task list; si : stats_internal }

let create ?capacity:(_ = 1024) () : scheduler =
  {
    pending = [];
    si =
      {
        si_tasks_executed = 0;
        si_tasks_cancelled = 0;
        si_total_latency_ms = 0.0;
        si_max_latency_ms = 0.0;
      };
  }

let compute_priority ~(edit_pos : int) ~(chunk_start : int) ~(layer_id : int) :
    float =
  float (abs (chunk_start - edit_pos)) +. (float layer_id *. 1000.0)

(** Effective priority used for sort: base [priority] + class offset. Monotonic
    in class: A < B < C < D regardless of layer/chunk. *)
let effective_priority (t : task) : float =
  t.priority +. class_priority_offset t.execution_class

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
    List.sort
      (fun a b -> compare (effective_priority a) (effective_priority b))
      sched.pending
  in
  sched.pending <- [];
  let bus = Event_bus.global () in
  let results = ref [] in
  List.iter
    (fun task ->
      Event_bus.publish bus
        (Event_bus.TaskScheduled
           { task_id = task.task_id; priority = task.priority });
      let t0 = Unix.gettimeofday () in
      let res = task.work () in
      let t1 = Unix.gettimeofday () in
      let elapsed_ms = (t1 -. t0) *. 1000.0 in
      sched.si.si_tasks_executed <- sched.si.si_tasks_executed + 1;
      sched.si.si_total_latency_ms <- sched.si.si_total_latency_ms +. elapsed_ms;
      if elapsed_ms > sched.si.si_max_latency_ms then
        sched.si.si_max_latency_ms <- elapsed_ms;
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
  }

let reset_stats (sched : scheduler) : unit =
  sched.si.si_tasks_executed <- 0;
  sched.si.si_tasks_cancelled <- 0;
  sched.si.si_total_latency_ms <- 0.0;
  sched.si.si_max_latency_ms <- 0.0
