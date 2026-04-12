(** Test EDF scheduler. 12+ cases. *)

open Latex_parse_lib
open Test_helpers

let mk_task ?(layer = 0) ?(chunk = 0L) ?(deadline = 0.0) id result_id =
  {
    Edf_scheduler.task_id = id;
    layer_id = layer;
    chunk_id = chunk;
    deadline;
    work =
      (fun () ->
        [
          {
            Validators_common.id = result_id;
            severity = Info;
            message = "test";
            count = 1;
          };
        ]);
  }

let () =
  (* ── compute_deadline ───────────────────────────────────────── *)
  run "closer chunk = lower deadline" (fun tag ->
      let d1 =
        Edf_scheduler.compute_deadline ~edit_pos:100 ~chunk_start:100
          ~layer_id:0
      in
      let d2 =
        Edf_scheduler.compute_deadline ~edit_pos:100 ~chunk_start:500
          ~layer_id:0
      in
      expect (d1 < d2) (tag ^ ": closer < farther"));

  run "lower layer = lower deadline" (fun tag ->
      let d0 =
        Edf_scheduler.compute_deadline ~edit_pos:0 ~chunk_start:0 ~layer_id:0
      in
      let d1 =
        Edf_scheduler.compute_deadline ~edit_pos:0 ~chunk_start:0 ~layer_id:1
      in
      let d2 =
        Edf_scheduler.compute_deadline ~edit_pos:0 ~chunk_start:0 ~layer_id:2
      in
      expect (d0 < d1 && d1 < d2) (tag ^ ": L0 < L1 < L2"));

  run "same position same layer = same deadline" (fun tag ->
      let d1 =
        Edf_scheduler.compute_deadline ~edit_pos:50 ~chunk_start:100 ~layer_id:1
      in
      let d2 =
        Edf_scheduler.compute_deadline ~edit_pos:50 ~chunk_start:100 ~layer_id:1
      in
      expect (d1 = d2) (tag ^ ": deterministic"));

  (* ── submit + drain ─────────────────────────────────────────── *)
  run "single task" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched (mk_task ~deadline:1.0 "t1" "RULE-001");
      let results = Edf_scheduler.drain sched in
      expect (List.length results = 1) (tag ^ ": 1 result"));

  run "empty drain returns []" (fun tag ->
      let sched = Edf_scheduler.create () in
      let results = Edf_scheduler.drain sched in
      expect (results = []) (tag ^ ": empty"));

  run "deadline ordering" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched (mk_task ~deadline:3.0 "late" "LATE");
      Edf_scheduler.submit sched (mk_task ~deadline:1.0 "early" "EARLY");
      Edf_scheduler.submit sched (mk_task ~deadline:2.0 "mid" "MID");
      let results = Edf_scheduler.drain sched in
      expect (List.length results = 3) (tag ^ ": 3 results");
      (* First result should be from earliest deadline *)
      expect ((List.hd results).id = "EARLY") (tag ^ ": EARLY first"));

  run "submit_batch" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit_batch sched
        [ mk_task ~deadline:2.0 "b" "B"; mk_task ~deadline:1.0 "a" "A" ];
      let results = Edf_scheduler.drain sched in
      expect (List.length results = 2) (tag ^ ": 2 results");
      expect ((List.hd results).id = "A") (tag ^ ": A first"));

  (* ── cancel_chunk ───────────────────────────────────────────── *)
  run "cancel_chunk removes tasks" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched (mk_task ~chunk:1L ~deadline:1.0 "t1" "R1");
      Edf_scheduler.submit sched (mk_task ~chunk:2L ~deadline:2.0 "t2" "R2");
      Edf_scheduler.submit sched (mk_task ~chunk:1L ~deadline:3.0 "t3" "R3");
      Edf_scheduler.cancel_chunk sched 1L;
      expect (Edf_scheduler.pending_count sched = 1) (tag ^ ": 1 left"));

  (* ── pending_count ──────────────────────────────────────────── *)
  run "pending_count accurate" (fun tag ->
      let sched = Edf_scheduler.create () in
      expect (Edf_scheduler.pending_count sched = 0) (tag ^ ": 0 initial");
      Edf_scheduler.submit sched (mk_task "t1" "R1");
      Edf_scheduler.submit sched (mk_task "t2" "R2");
      expect (Edf_scheduler.pending_count sched = 2) (tag ^ ": 2 after submit");
      ignore (Edf_scheduler.drain sched);
      expect (Edf_scheduler.pending_count sched = 0) (tag ^ ": 0 after drain"));

  (* ── stats ──────────────────────────────────────────────────── *)
  run "stats tracking" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.reset_stats sched;
      Edf_scheduler.submit sched (mk_task ~deadline:1.0 "t1" "R1");
      ignore (Edf_scheduler.drain sched);
      let s = Edf_scheduler.stats sched in
      expect (s.tasks_executed = 1) (tag ^ ": 1 executed");
      expect (s.tasks_cancelled = 0) (tag ^ ": 0 cancelled"));

  run "stats after cancel" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.reset_stats sched;
      Edf_scheduler.submit sched (mk_task ~chunk:1L "t1" "R1");
      Edf_scheduler.submit sched (mk_task ~chunk:1L "t2" "R2");
      Edf_scheduler.cancel_chunk sched 1L;
      let s = Edf_scheduler.stats sched in
      expect (s.tasks_cancelled = 2) (tag ^ ": 2 cancelled"))

let () = finalise "edf-scheduler"
