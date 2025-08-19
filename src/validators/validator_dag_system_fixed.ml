(* VALIDATOR DAG SYSTEM - PERFORMANCE FIXED VERSION *)
(* Each validator gets independent stream to fix shared mutable state bug *)

open Printf
open Validator_core_fixed  (* Use the FIXED array-based version! *)
open Specification_compliant_validators

(* Validator manifest schema as specified in planner Section 6 *)
type validator_manifest = {
  id: string;
  phase: string;
  provides: string list;
  requires: string list;
  conflicts: string list;
  severity: [`Error | `Warning | `Info];
  description: string;
  validator_module: (module VALIDATOR);
}

(* Phase ordinals for conflict resolution *)
let phase_ordinal = function
  | "L0_Lexer" -> 0
  | "L1_Expanded" -> 1
  | "L3_Semantics" -> 2
  | _ -> 999

(* Severity ordinals for conflict resolution *)
let severity_ordinal = function
  | `Error -> 0
  | `Warning -> 1  
  | `Info -> 2

(* DAG execution system *)
module ValidatorDAG = struct
  
  type execution_graph = {
    manifests: (string, validator_manifest) Hashtbl.t;
    dependency_graph: (string, string list) Hashtbl.t;
    reverse_deps: (string, string list) Hashtbl.t;
    execution_order: string list;
    conflicts_resolved: (string * string * string) list;
  }
  
  exception CyclicDependency of string list
  exception ConflictResolutionFailed of string * string
  exception MissingDependency of string * string
  
  (* Topological sort implementation *)
  let rec topological_sort nodes dep_graph =
    let visited = Hashtbl.create (List.length nodes) in
    let visiting = Hashtbl.create (List.length nodes) in
    let result = ref [] in
    let cycle_path = ref [] in
    
    let rec visit node =
      if Hashtbl.mem visiting node then begin
        let cycle_start = ref false in
        let cycle = List.fold_left (fun acc n ->
          if n = node then cycle_start := true;
          if !cycle_start then n :: acc else acc
        ) [] !cycle_path in
        raise (CyclicDependency (List.rev (node :: cycle)))
      end;
      
      if not (Hashtbl.mem visited node) then begin
        Hashtbl.add visiting node true;
        cycle_path := node :: !cycle_path;
        
        let deps = try Hashtbl.find dep_graph node with Not_found -> [] in
        List.iter visit deps;
        
        Hashtbl.remove visiting node;
        Hashtbl.add visited node true;
        cycle_path := List.tl !cycle_path;
        result := node :: !result
      end
    in
    
    List.iter visit nodes;
    !result
  
  (* Build static DAG at startup *)
  let build_dag manifests =
    let manifest_table = Hashtbl.create (List.length manifests) in
    let dep_graph = Hashtbl.create (List.length manifests) in
    let reverse_deps = Hashtbl.create (List.length manifests) in
    let conflicts_resolved = ref [] in
    
    (* Load all manifests *)
    List.iter (fun manifest ->
      if Hashtbl.mem manifest_table manifest.id then
        failwith (sprintf "Duplicate validator ID: %s" manifest.id);
      Hashtbl.add manifest_table manifest.id manifest
    ) manifests;
    
    (* Resolve conflicts *)
    let resolve_conflicts conflicting_validators =
      let sorted = List.sort (fun v1 v2 ->
        let sev_cmp = compare (severity_ordinal v1.severity) (severity_ordinal v2.severity) in
        if sev_cmp <> 0 then sev_cmp
        else let phase_cmp = compare (phase_ordinal v1.phase) (phase_ordinal v2.phase) in
        if phase_cmp <> 0 then phase_cmp
        else String.compare v1.id v2.id
      ) conflicting_validators in
      match sorted with
      | winner :: losers ->
          List.iter (fun loser ->
            let reason = sprintf "Conflict resolution: %s wins over %s" 
                        winner.id loser.id in
            conflicts_resolved := (winner.id, loser.id, reason) :: !conflicts_resolved
          ) losers;
          winner
      | [] -> failwith "Empty conflict set"
    in
    
    (* Process conflicts *)
    let final_manifests = ref [] in
    let processed_conflicts = Hashtbl.create 10 in
    
    List.iter (fun manifest ->
      let conflicting = List.filter (fun other ->
        other.id <> manifest.id && 
        (List.mem other.id manifest.conflicts || List.mem manifest.id other.conflicts)
      ) manifests in
      
      if conflicting = [] then
        final_manifests := manifest :: !final_manifests
      else begin
        let conflict_group = manifest :: conflicting in
        let conflict_key = String.concat "," (List.sort String.compare (List.map (fun v -> v.id) conflict_group)) in
        
        if not (Hashtbl.mem processed_conflicts conflict_key) then begin
          Hashtbl.add processed_conflicts conflict_key true;
          let winner = resolve_conflicts conflict_group in
          final_manifests := winner :: !final_manifests
        end
      end
    ) manifests;
    
    (* Build dependency graph *)
    List.iter (fun manifest ->
      Hashtbl.add dep_graph manifest.id manifest.requires;
      
      List.iter (fun req ->
        let current_deps = try Hashtbl.find reverse_deps req with Not_found -> [] in
        Hashtbl.replace reverse_deps req (manifest.id :: current_deps)
      ) manifest.requires
    ) !final_manifests;
    
    (* Verify dependencies exist *)
    List.iter (fun manifest ->
      List.iter (fun req ->
        if not (Hashtbl.mem manifest_table req) then
          raise (MissingDependency (manifest.id, req))
      ) manifest.requires
    ) !final_manifests;
    
    (* Determine execution order *)
    let execution_order = topological_sort (List.map (fun m -> m.id) !final_manifests) dep_graph in
    
    {
      manifests = manifest_table;
      dependency_graph = dep_graph;
      reverse_deps;
      execution_order;
      conflicts_resolved = !conflicts_resolved;
    }
  
  (* FIXED: Execute validators with INDEPENDENT streams! *)
  let execute_validators dag context tokens_array =
    let all_issues = ref [] in
    let execution_stats = ref [] in
    
    List.iter (fun validator_id ->
      try
        let manifest = Hashtbl.find dag.manifests validator_id in
        let module V = (val manifest.validator_module : VALIDATOR) in
        
        (* CRITICAL FIX: Create NEW stream for EACH validator! *)
        let fresh_stream = create_stream tokens_array in
        
        let start_time = Unix.gettimeofday () in
        let issues = V.validate context fresh_stream in
        let end_time = Unix.gettimeofday () in
        let execution_time = (end_time -. start_time) *. 1000.0 in
        
        execution_stats := (validator_id, execution_time, List.length issues) :: !execution_stats;
        all_issues := issues @ !all_issues;
        
        printf "Executed %s: %d issues in %.3fms\n" validator_id (List.length issues) execution_time
        
      with Not_found ->
        printf "Warning: Validator %s not found in manifest table\n" validator_id
    ) dag.execution_order;
    
    (!all_issues, List.rev !execution_stats)
  
  (* Execute validators using token list (backwards compatibility) *)
  let execute_validators_from_list dag context token_list =
    let tokens_array = Array.of_list token_list in
    execute_validators dag context tokens_array
  
  (* Diagnostic functions *)
  let print_dag_info dag =
    printf "=== VALIDATOR DAG INFORMATION ===\n";
    printf "Total validators: %d\n" (Hashtbl.length dag.manifests);
    printf "Execution order: %s\n" (String.concat " -> " dag.execution_order);
    printf "Conflicts resolved: %d\n" (List.length dag.conflicts_resolved);
    
    List.iter (fun (winner, loser, reason) ->
      printf "  CONFLICT: %s\n" reason
    ) dag.conflicts_resolved;
    
    printf "=== DEPENDENCY ANALYSIS ===\n";
    List.iter (fun validator_id ->
      let deps = try Hashtbl.find dag.dependency_graph validator_id with Not_found -> [] in
      let rev_deps = try Hashtbl.find dag.reverse_deps validator_id with Not_found -> [] in
      printf "%s: requires=[%s] provides_for=[%s]\n" 
             validator_id 
             (String.concat ", " deps)
             (String.concat ", " rev_deps)
    ) dag.execution_order
    
  let verify_dag_acyclic dag =
    try
      let _ = topological_sort dag.execution_order dag.dependency_graph in
      true
    with CyclicDependency cycle ->
      printf "ERROR: Cyclic dependency detected: %s\n" (String.concat " -> " cycle);
      false
end

(* Include all the manifest definitions from original file *)
module FoundationValidators = struct
  
  let typo001_manifest = {
    id = "TYPO-001";
    phase = "L0_Lexer";
    provides = ["ascii_quote_detection"; "typography_basic"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Error;
    description = "ASCII straight quotes (\" … \") must be curly quotes";
    validator_module = (module SpecCompliantTYPO001);
  }
  
  let typo002_manifest = {
    id = "TYPO-002";
    phase = "L0_Lexer";
    provides = ["hyphen_detection"; "typography_basic"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Warning;
    description = "Double hyphen -- should be en‑dash –";
    validator_module = (module SpecCompliantTYPO002);
  }
  
  let typo003_manifest = {
    id = "TYPO-003";
    phase = "L0_Lexer";
    provides = ["em_dash_detection"; "typography_advanced"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Warning;
    description = "Triple hyphen --- should be em‑dash —";
    validator_module = (module SpecCompliantTYPO003);
  }
  
  let typo005_manifest = {
    id = "TYPO-005";
    phase = "L0_Lexer";
    provides = ["ellipsis_detection"; "typography_advanced"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Warning;
    description = "Ellipsis typed as three periods ...; use \\dots";
    validator_module = (module SpecCompliantTYPO005);
  }
  
  let typo006_manifest = {
    id = "TYPO-006";
    phase = "L0_Lexer";
    provides = ["tab_detection"; "whitespace_validation"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Tab character U+0009 forbidden";
    validator_module = (module SpecCompliantTYPO006);
  }
  
  (* Foundation capabilities *)
  let tokenization_capability = {
    id = "tokenization";
    phase = "L0_Lexer";
    provides = ["tokenization"];
    requires = [];
    conflicts = [];
    severity = `Info;
    description = "Basic tokenization capability (provided by L0 lexer)";
    validator_module = (module struct
      let rule_id = "tokenization"
      let name = "Tokenization capability"
      let description = "Basic tokenization capability"
      let default_severity = `Info
      let validate context stream = []
    end : VALIDATOR);
  }
  
  let macro_expansion_capability = {
    id = "macro_expansion";
    phase = "L1_Expanded";
    provides = ["macro_expansion"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Info;
    description = "Macro expansion capability (provided by L1 expander)";
    validator_module = (module struct
      let rule_id = "macro_expansion"
      let name = "Macro expansion capability"
      let description = "Macro expansion capability"
      let default_severity = `Info
      let validate context stream = []
    end : VALIDATOR);
  }

  (* Week 1 Foundation validator set *)
  let foundation_week1_manifests = [
    tokenization_capability;
    macro_expansion_capability;
    typo001_manifest;
    typo002_manifest;
    typo003_manifest;
    typo005_manifest;
    typo006_manifest;
  ]
end

(* Initialize validator system *)
let initialize_validator_system () =
  try
    printf "Building FIXED validator DAG system...\n";
    let dag = ValidatorDAG.build_dag FoundationValidators.foundation_week1_manifests in
    
    printf "Verifying DAG is acyclic...\n";
    if ValidatorDAG.verify_dag_acyclic dag then
      printf "✅ DAG is acyclic - validator system ready\n"
    else
      failwith "❌ Cyclic dependencies detected - system cannot start";
    
    ValidatorDAG.print_dag_info dag;
    dag
    
  with
  | ValidatorDAG.CyclicDependency cycle ->
      printf "❌ FATAL: Cyclic dependency: %s\n" (String.concat " -> " cycle);
      failwith "Cannot proceed with cyclic validator dependencies"
  | ValidatorDAG.MissingDependency (validator, dep) ->
      printf "❌ FATAL: Validator %s requires missing dependency: %s\n" validator dep;
      failwith "Cannot proceed with missing dependencies"
  | exn ->
      printf "❌ FATAL: Validator system initialization failed: %s\n" (Printexc.to_string exn);
      raise exn