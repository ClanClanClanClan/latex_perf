(** Test EDF scheduler. 12+ cases. *)

open Latex_parse_lib
open Test_helpers

let mk_task ?(layer = 0) ?(chunk = 0L) ?(priority = 0.0)
    ?(execution_class = Rule_contract_loader.B) id result_id =
  {
    Edf_scheduler.task_id = id;
    layer_id = layer;
    chunk_id = chunk;
    priority;
    execution_class;
    work =
      (fun () ->
        [
          Validators_common.mk_result ~id:result_id ~severity:Info
            ~message:"test" ~count:1;
        ]);
  }

let () =
  (* ── compute_priority ───────────────────────────────────────── *)
  run "closer chunk = lower priority" (fun tag ->
      let d1 =
        Edf_scheduler.compute_priority ~edit_pos:100 ~chunk_start:100
          ~layer_id:0
      in
      let d2 =
        Edf_scheduler.compute_priority ~edit_pos:100 ~chunk_start:500
          ~layer_id:0
      in
      expect (d1 < d2) (tag ^ ": closer < farther"));

  run "lower layer = lower priority" (fun tag ->
      let d0 =
        Edf_scheduler.compute_priority ~edit_pos:0 ~chunk_start:0 ~layer_id:0
      in
      let d1 =
        Edf_scheduler.compute_priority ~edit_pos:0 ~chunk_start:0 ~layer_id:1
      in
      let d2 =
        Edf_scheduler.compute_priority ~edit_pos:0 ~chunk_start:0 ~layer_id:2
      in
      expect (d0 < d1 && d1 < d2) (tag ^ ": L0 < L1 < L2"));

  run "same position same layer = same priority" (fun tag ->
      let d1 =
        Edf_scheduler.compute_priority ~edit_pos:50 ~chunk_start:100 ~layer_id:1
      in
      let d2 =
        Edf_scheduler.compute_priority ~edit_pos:50 ~chunk_start:100 ~layer_id:1
      in
      expect (d1 = d2) (tag ^ ": deterministic"));

  (* ── submit + drain ─────────────────────────────────────────── *)
  run "single task" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched (mk_task ~priority:1.0 "t1" "RULE-001");
      let results = Edf_scheduler.drain sched in
      expect (List.length results = 1) (tag ^ ": 1 result"));

  run "empty drain returns []" (fun tag ->
      let sched = Edf_scheduler.create () in
      let results = Edf_scheduler.drain sched in
      expect (results = []) (tag ^ ": empty"));

  run "priority ordering" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched (mk_task ~priority:3.0 "late" "LATE");
      Edf_scheduler.submit sched (mk_task ~priority:1.0 "early" "EARLY");
      Edf_scheduler.submit sched (mk_task ~priority:2.0 "mid" "MID");
      let results = Edf_scheduler.drain sched in
      expect (List.length results = 3) (tag ^ ": 3 results");
      (* First result should be from lowest priority *)
      expect ((List.hd results).id = "EARLY") (tag ^ ": EARLY first"));

  run "submit_batch" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit_batch sched
        [ mk_task ~priority:2.0 "b" "B"; mk_task ~priority:1.0 "a" "A" ];
      let results = Edf_scheduler.drain sched in
      expect (List.length results = 2) (tag ^ ": 2 results");
      expect ((List.hd results).id = "A") (tag ^ ": A first"));

  (* ── cancel_chunk ───────────────────────────────────────────── *)
  run "cancel_chunk removes tasks" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched (mk_task ~chunk:1L ~priority:1.0 "t1" "R1");
      Edf_scheduler.submit sched (mk_task ~chunk:2L ~priority:2.0 "t2" "R2");
      Edf_scheduler.submit sched (mk_task ~chunk:1L ~priority:3.0 "t3" "R3");
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
      Edf_scheduler.submit sched (mk_task ~priority:1.0 "t1" "R1");
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
      expect (s.tasks_cancelled = 2) (tag ^ ": 2 cancelled"));

  (* ── PR #241 (p1.6): per-class priority dominance (memo §11.2) ──── *)
  run "Class A outranks B regardless of layer" (fun tag ->
      let sched = Edf_scheduler.create () in
      (* B task at priority 0 (lowest layer, right at edit); A task at priority
         999 (far from edit, high layer). Class offset must still place A
         first. *)
      Edf_scheduler.submit sched
        (mk_task ~priority:0.0 ~execution_class:Rule_contract_loader.B "b_task"
           "B_RESULT");
      Edf_scheduler.submit sched
        (mk_task ~priority:999.0 ~execution_class:Rule_contract_loader.A
           "a_task" "A_RESULT");
      let results = Edf_scheduler.drain sched in
      expect ((List.hd results).id = "A_RESULT") (tag ^ ": Class A runs first"));

  run "Class D always last" (fun tag ->
      let sched = Edf_scheduler.create () in
      Edf_scheduler.submit sched
        (mk_task ~priority:0.0 ~execution_class:Rule_contract_loader.D "d_task"
           "D_RESULT");
      Edf_scheduler.submit sched
        (mk_task ~priority:500.0 ~execution_class:Rule_contract_loader.C
           "c_task" "C_RESULT");
      let results = Edf_scheduler.drain sched in
      expect ((List.nth results 1).id = "D_RESULT") (tag ^ ": Class D runs last");
      expect ((List.hd results).id = "C_RESULT") (tag ^ ": Class C before D"));

  run "effective_priority respects class" (fun tag ->
      let a =
        mk_task ~priority:10.0 ~execution_class:Rule_contract_loader.A "a" "A"
      in
      let d =
        mk_task ~priority:0.0 ~execution_class:Rule_contract_loader.D "d" "D"
      in
      expect
        (Edf_scheduler.effective_priority a < Edf_scheduler.effective_priority d)
        (tag ^ ": A < D even with higher base priority"));

  run "class_priority_offset monotone" (fun tag ->
      let oa = Edf_scheduler.class_priority_offset Rule_contract_loader.A in
      let ob = Edf_scheduler.class_priority_offset Rule_contract_loader.B in
      let oc = Edf_scheduler.class_priority_offset Rule_contract_loader.C in
      let od = Edf_scheduler.class_priority_offset Rule_contract_loader.D in
      expect (oa < ob && ob < oc && oc < od) (tag ^ ": A<B<C<D"))

let () = finalise "edf-scheduler"
