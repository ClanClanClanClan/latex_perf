(** Tests for Validator_dag — dependency graph + conflict resolution. *)

open Test_helpers

let () =
  let open Latex_parse_lib.Validator_dag in
  (* Test 1: Empty DAG *)
  run "empty DAG" (fun tag ->
      match build_dag [] with
      | Ok dag ->
          expect (dag.topo_order = []) (tag ^ ": empty order");
          expect (dag.edges = []) (tag ^ ": no edges")
      | Error msg -> expect false (tag ^ ": " ^ msg));

  (* Test 2: Linear chain A → B → C *)
  run "linear chain" (fun tag ->
      let a =
        {
          id = "A";
          phase = L0;
          provides = [ "cap_a" ];
          requires = [];
          conflicts = [];
        }
      in
      let b =
        {
          id = "B";
          phase = L1;
          provides = [ "cap_b" ];
          requires = [ "cap_a" ];
          conflicts = [];
        }
      in
      let c =
        {
          id = "C";
          phase = L2;
          provides = [ "cap_c" ];
          requires = [ "cap_b" ];
          conflicts = [];
        }
      in
      match build_dag [ a; b; c ] with
      | Ok dag ->
          expect
            (List.length dag.topo_order = 3)
            (tag ^ ": 3 nodes in topo order")
      | Error msg -> expect false (tag ^ ": " ^ msg));

  (* Test 3: Cycle detection *)
  run "cycle detected" (fun tag ->
      let a =
        {
          id = "A";
          phase = L0;
          provides = [ "cap_a" ];
          requires = [ "cap_b" ];
          conflicts = [];
        }
      in
      let b =
        {
          id = "B";
          phase = L0;
          provides = [ "cap_b" ];
          requires = [ "cap_a" ];
          conflicts = [];
        }
      in
      match build_dag [ a; b ] with
      | Ok _ -> expect false (tag ^ ": should detect cycle")
      | Error msg ->
          expect (String.length msg > 0) (tag ^ ": error message present"));

  (* Test 4: Conflict detection *)
  run "conflict detected" (fun tag ->
      let a =
        {
          id = "A";
          phase = L0;
          provides = [];
          requires = [];
          conflicts = [ "B" ];
        }
      in
      let b =
        { id = "B"; phase = L0; provides = []; requires = []; conflicts = [] }
      in
      let conflicts = detect_conflicts [ a; b ] in
      expect (List.length conflicts = 1) (tag ^ ": 1 conflict");
      expect ((List.hd conflicts).rule_a = "A") (tag ^ ": A conflicts B"));

  (* Test 5: No conflicts *)
  run "no conflicts" (fun tag ->
      let a = default_meta "TYPO-001" L0 in
      let b = default_meta "TYPO-002" L0 in
      let conflicts = detect_conflicts [ a; b ] in
      expect (conflicts = []) (tag ^ ": no conflicts"));

  (* Test 6: Conflict resolution — higher severity wins *)
  run "conflict resolution severity" (fun tag ->
      let a = default_meta "A" L0 in
      let b = default_meta "B" L0 in
      let winner = resolve_conflict a b 3 1 in
      expect (winner = "A") (tag ^ ": higher severity wins"));

  (* Test 7: Conflict resolution — lower phase wins on tie *)
  run "conflict resolution phase" (fun tag ->
      let a = default_meta "A" L0 in
      let b = default_meta "B" L2 in
      let winner = resolve_conflict a b 2 2 in
      expect (winner = "A") (tag ^ ": lower phase wins"));

  (* Test 8: Default metadata *)
  run "default meta" (fun tag ->
      let m = default_meta "TYPO-001" L0 in
      expect (m.id = "TYPO-001") (tag ^ ": id");
      expect (m.provides = [ "TYPO-001" ]) (tag ^ ": provides self");
      expect (m.requires = []) (tag ^ ": no requires");
      expect (m.conflicts = []) (tag ^ ": no conflicts"));

  (* Test 9: Large DAG — all current rules with no deps *)
  run "large DAG no cycles" (fun tag ->
      let metas =
        List.init 600 (fun i -> default_meta (Printf.sprintf "RULE-%03d" i) L0)
      in
      match build_dag metas with
      | Ok dag ->
          expect (List.length dag.topo_order = 600) (tag ^ ": 600 nodes");
          expect (dag.edges = []) (tag ^ ": no edges")
      | Error msg -> expect false (tag ^ ": " ^ msg));

  finalise "validator_dag"
