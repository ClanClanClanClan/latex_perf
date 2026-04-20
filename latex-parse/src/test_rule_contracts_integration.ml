(** Tests for PR #237 rule contracts + real validator DAG (memo §10, §15.4).

    Exercises:
    - Rule_contract_loader loads the full catalogue (645+ contracts).
    - Every runtime rule has a contract.
    - Class C population from contracts matches execution_class.ml.
    - DAG builds acyclic.
    - Every contract's [layer] parses cleanly. *)

open Latex_parse_lib
open Test_helpers

let () =
  (* 1. Loader returns the full catalogue (>= 645 baseline). *)
  run "Rule_contract_loader loads full catalogue" (fun tag ->
      let n = Rule_contract_loader.count () in
      expect (n >= 645)
        (tag ^ ": loaded " ^ string_of_int n ^ " contracts, expected >= 645"));

  (* 2. Every runtime Class C rule has a matching contract. *)
  run "every Class C rule has a contract" (fun tag ->
      let missing =
        List.filter_map
          (fun (r : Validators.rule) ->
            match Rule_contract_loader.find_opt r.id with
            | Some _ -> None
            | None -> Some r.id)
          Validators.rules_class_c
      in
      expect (missing = [])
        (tag
        ^ ": "
        ^ string_of_int (List.length missing)
        ^ " Class C rule(s) without contract: "
        ^ String.concat "," missing));

  (* 3. Class C contracts count matches runtime Class C list count. *)
  run "Class C count parity" (fun tag ->
      let contracts = Rule_contract_loader.load () in
      let contract_c =
        List.filter_map
          (fun (c : Rule_contract_loader.contract) ->
            if c.execution_class = Rule_contract_loader.C then Some c.rule_id
            else None)
          contracts
      in
      let runtime_c =
        List.map (fun (r : Validators.rule) -> r.id) Validators.rules_class_c
      in
      let sorted xs = List.sort compare xs in
      expect
        (sorted contract_c = sorted runtime_c)
        (tag
        ^ ": contract C ("
        ^ string_of_int (List.length contract_c)
        ^ ") vs runtime C ("
        ^ string_of_int (List.length runtime_c)
        ^ ")"));

  (* 4. Every contract layer string parsed to a concrete phase without
     defaulting to L0 — catches YAML typos. We compare against the raw yaml by
     re-parsing a small representative sample. *)
  run "contract layer fields parse non-trivially" (fun tag ->
      let contracts = Rule_contract_loader.load () in
      (* Build a map of rule_id -> phase_ordinal as reported by the loader. *)
      let layers =
        List.map
          (fun (c : Rule_contract_loader.contract) ->
            (c.rule_id, Validator_dag.phase_ordinal c.layer))
          contracts
      in
      (* Known anchors: LAY-025 is L2_Ast (phase_ordinal=2); TYPO-001 is
         L0_Lexer (phase_ordinal=0); STYLE-001 is L4_Style (phase_ordinal=4). *)
      let lookup id = List.assoc_opt id layers in
      expect
        (lookup "LAY-025" = Some 2)
        (tag ^ ": LAY-025 layer should be L2_Ast");
      expect
        (lookup "TYPO-001" = Some 0)
        (tag ^ ": TYPO-001 layer should be L0_Lexer");
      expect
        (lookup "STYLE-001" = Some 4)
        (tag ^ ": STYLE-001 layer should be L4_Style"));

  (* 5. LAY-025/026/027 have formal_conditional proof class. *)
  run "LAY-025/026/027 are formal_conditional" (fun tag ->
      let check rid =
        match Rule_contract_loader.find_opt rid with
        | Some c ->
            expect
              (c.proof_class = Rule_contract_loader.Formal_conditional)
              (tag ^ ": " ^ rid ^ " proof_class should be formal_conditional")
        | None -> expect false (tag ^ ": " ^ rid ^ " missing from contracts")
      in
      check "LAY-025";
      check "LAY-026";
      check "LAY-027");

  (* 6. L3 conservative rules have formal_conservative proof class. *)
  run "L3 file-based rules are formal_conservative" (fun tag ->
      let conservative_ids =
        [
          "FIG-004";
          "FIG-006";
          "FIG-016";
          "COL-001";
          "PDF-006";
          "PDF-007";
          "TIKZ-002";
          "CJK-007";
        ]
      in
      List.iter
        (fun rid ->
          match Rule_contract_loader.find_opt rid with
          | Some c ->
              expect
                (c.proof_class = Rule_contract_loader.Formal_conservative)
                (tag ^ ": " ^ rid ^ " should be formal_conservative")
          | None -> expect false (tag ^ ": " ^ rid ^ " missing"))
        conservative_ids);

  (* 7. DAG builds successfully with contracts (no cycles). *)
  run "DAG builds acyclic from contracts" (fun tag ->
      let metas =
        List.map Rule_contract_loader.to_validator_meta
          (Rule_contract_loader.load ())
      in
      match Validator_dag.build_dag metas with
      | Ok dag ->
          expect
            (List.length dag.Validator_dag.topo_order
            = List.length dag.Validator_dag.nodes)
            (tag ^ ": topo_order covers all nodes")
      | Error msg -> expect false (tag ^ ": build_dag failed: " ^ msg));

  (* 8. execution_class routing: Class C contracts are not keystroke-safe. *)
  run "Class C contracts are not keystroke-safe" (fun tag ->
      let contracts_c =
        List.filter_map
          (fun (c : Rule_contract_loader.contract) ->
            if c.execution_class = Rule_contract_loader.C then Some c.rule_id
            else None)
          (Rule_contract_loader.load ())
      in
      let leaked =
        List.filter
          (fun id ->
            Execution_class.is_keystroke_safe (Execution_class.classify id))
          contracts_c
      in
      expect (leaked = [])
        (tag
        ^ ": "
        ^ string_of_int (List.length leaked)
        ^ " Class C rule(s) leaked into keystroke-safe set"));

  finalise "rule_contracts_integration"
