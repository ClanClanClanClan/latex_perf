(* VALIDATOR DAG SYSTEM - Following PLANNER_v25_R1.yaml Section 6 *)
(* Manifest schema {id,phase,provides,requires,conflicts} with DAG execution *)

open Printf
open Validator_core
open Specification_compliant_validators

(* Validator manifest schema as specified in planner Section 6 *)
type validator_manifest = {
  id: string;                           (* e.g., "TYPO-001" *)
  phase: string;                        (* "L0_Lexer" | "L1_Expanded" | "L3_Semantics" *)
  provides: string list;                (* capabilities this validator provides *)
  requires: string list;                (* dependencies this validator needs *)
  conflicts: string list;               (* validators that conflict with this one *)
  severity: [`Error | `Warning | `Info]; (* default severity for conflict resolution *)
  description: string;                  (* human-readable description *)
  validator_module: (module VALIDATOR);  (* actual validator implementation *)
}

(* Phase ordinals for conflict resolution as per planner *)
let phase_ordinal = function
  | "L0_Lexer" -> 0
  | "L1_Expanded" -> 1
  | "L3_Semantics" -> 2
  | _ -> 999  (* unknown phases sort last *)

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
    conflicts_resolved: (string * string * string) list; (* (winner, loser, reason) *)
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
        (* Cycle detected *)
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
  
  (* Build static DAG at startup - cycles abort as per planner *)
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
    
    (* Resolve conflicts using planner's conflict-resolution order *)
    (* Order: (severity, phase-ordinal, id-lex) *)
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
            let reason = sprintf "Conflict resolution: %s wins over %s (severity=%s, phase=%s, id-lex)" 
                        winner.id loser.id 
                        (match winner.severity with `Error -> "Error" | `Warning -> "Warning" | `Info -> "Info")
                        winner.phase in
            conflicts_resolved := (winner.id, loser.id, reason) :: !conflicts_resolved
          ) losers;
          winner
      | [] -> failwith "Empty conflict set"
    in
    
    (* Check for conflicts and resolve them *)
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
      
      (* Build reverse dependencies *)
      List.iter (fun req ->
        let current_deps = try Hashtbl.find reverse_deps req with Not_found -> [] in
        Hashtbl.replace reverse_deps req (manifest.id :: current_deps)
      ) manifest.requires
    ) !final_manifests;
    
    (* Verify all dependencies exist *)
    List.iter (fun manifest ->
      List.iter (fun req ->
        if not (Hashtbl.mem manifest_table req) then
          raise (MissingDependency (manifest.id, req))
      ) manifest.requires
    ) !final_manifests;
    
    (* Topological sort to detect cycles and determine execution order *)
    let execution_order = topological_sort (List.map (fun m -> m.id) !final_manifests) dep_graph in
    
    {
      manifests = manifest_table;
      dependency_graph = dep_graph;
      reverse_deps;
      execution_order;
      conflicts_resolved = !conflicts_resolved;
    }
  (* Execute validators in DAG-determined order *)
  let execute_validators dag context stream =
    let all_issues = ref [] in
    let execution_stats = ref [] in
    
    List.iter (fun validator_id ->
      try
        let manifest = Hashtbl.find dag.manifests validator_id in
        let module V = (val manifest.validator_module : VALIDATOR) in
        
        let start_time = Unix.gettimeofday () in
        let issues = V.validate context stream in
        let end_time = Unix.gettimeofday () in
        let execution_time = (end_time -. start_time) *. 1000.0 in (* ms *)
        
        execution_stats := (validator_id, execution_time, List.length issues) :: !execution_stats;
        all_issues := issues @ !all_issues;
        
        printf "Executed %s: %d issues in %.2fms\n" validator_id (List.length issues) execution_time
        
      with Not_found ->
        printf "Warning: Validator %s not found in manifest table\n" validator_id
    ) dag.execution_order;
    
    (!all_issues, List.rev !execution_stats)
  
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
    (* This function should eventually be proven in ValidatorGraphProofs.v *)
    try
      let _ = topological_sort dag.execution_order dag.dependency_graph in
      true
    with CyclicDependency cycle ->
      printf "ERROR: Cyclic dependency detected: %s\n" (String.concat " -> " cycle);
      false
end

(* Foundation Year 1 validators with proper manifests *)
module FoundationValidators = struct
  
  (* Example: TYPO-001 with proper manifest *)
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
  
  let delim001_manifest = {
    id = "DELIM-001";
    phase = "L1_Expanded";
    provides = ["brace_matching"; "delimiter_basic"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Unmatched delimiters { … } after macro expansion";
    validator_module = (module SpecCompliantDELIM001);
  }
  
  let delim003_manifest = {
    id = "DELIM-003";
    phase = "L1_Expanded";
    provides = ["left_right_matching"; "delimiter_advanced"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Unmatched \\left without \\right";
    validator_module = (module SpecCompliantDELIM003);
  }
  
  let ref001_manifest = {
    id = "REF-001";
    phase = "L1_Expanded";
    provides = ["reference_validation"; "label_checking"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Undefined \\ref / \\eqref label after expansion";
    validator_module = (module SpecCompliantREF001);
  }
  
  let ref002_manifest = {
    id = "REF-002";
    phase = "L1_Expanded";
    provides = ["label_uniqueness"; "reference_integrity"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Duplicate label name";
    validator_module = (module SpecCompliantREF002);
  }
  
  let ref003_manifest = {
    id = "REF-003";
    phase = "L1_Expanded";
    provides = ["label_formatting"; "reference_style"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Warning;
    description = "Label contains spaces";
    validator_module = (module SpecCompliantREF003);
  }
  
  (* Week 2 Expansion validators *)
  let typo007_manifest = {
    id = "TYPO-007";
    phase = "L0_Lexer";
    provides = ["trailing_space_detection"; "whitespace_advanced"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Info;
    description = "Trailing spaces at end of line";
    validator_module = (module SpecCompliantTYPO007);
  }
  
  let delim002_manifest = {
    id = "DELIM-002";
    phase = "L1_Expanded";
    provides = ["extra_brace_detection"; "delimiter_error"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Extra closing } detected";
    validator_module = (module SpecCompliantDELIM002);
  }
  
  let delim004_manifest = {
    id = "DELIM-004";
    phase = "L1_Expanded";
    provides = ["right_without_left_detection"; "delimiter_error"];
    requires = ["macro_expansion"; "tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Unmatched \\right without \\left";
    validator_module = (module SpecCompliantDELIM004);
  }
  
  let spc001_manifest = {
    id = "SPC-001";
    phase = "L0_Lexer";
    provides = ["differential_spacing"; "math_typography"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Info;
    description = "Missing thin space before differential dx, dy, etc.";
    validator_module = (module SpecCompliantSPC001);
  }
  
  let spc002_manifest = {
    id = "SPC-002";
    phase = "L0_Lexer";
    provides = ["punctuation_spacing"; "text_typography"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Info;
    description = "Unwanted space before punctuation";
    validator_module = (module SpecCompliantSPC002);
  }
  
  let spc003_manifest = {
    id = "SPC-003";
    phase = "L0_Lexer";
    provides = ["nonbreaking_space"; "reference_typography"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Warning;
    description = "Missing non-breaking space in common contexts";
    validator_module = (module SpecCompliantSPC003);
  }
  
  let char001_manifest = {
    id = "CHAR-001";
    phase = "L0_Lexer";
    provides = ["unicode_validation"; "character_safety"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Invalid or problematic Unicode characters";
    validator_module = (module SpecCompliantCHAR001);
  }
  
  let char002_manifest = {
    id = "CHAR-002";
    phase = "L0_Lexer";
    provides = ["encoding_validation"; "character_integrity"];
    requires = ["tokenization"];
    conflicts = [];
    severity = `Error;
    description = "Character encoding issues";
    validator_module = (module SpecCompliantCHAR002);
  }
  
  (* Foundation capability manifests *)
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

  (* Week 1 Foundation validator set (10 critical validators + 2 capabilities) *)
  let foundation_week1_manifests = [
    (* Foundation capabilities *)
    tokenization_capability;
    macro_expansion_capability;
    
    (* L0_Lexer validators (5 validators) *)
    typo001_manifest;  (* ASCII quotes *)
    typo002_manifest;  (* Double hyphen *)
    typo003_manifest;  (* Triple hyphen *)
    typo005_manifest;  (* Ellipsis periods *)
    typo006_manifest;  (* Tab character *)
    
    (* L1_Expanded validators (5 validators) *)
    delim001_manifest; (* Unmatched braces *)
    delim003_manifest; (* Unmatched \left without \right *)
    ref001_manifest;   (* Undefined references *)
    ref002_manifest;   (* Duplicate labels *)
    ref003_manifest;   (* Label contains spaces *)
  ]
  
  (* Week 2 Expansion validator set (18 total validators + 2 capabilities) *)
  let foundation_week2_manifests = foundation_week1_manifests @ [
    (* Additional L0_Lexer validators (8 validators) *)
    typo007_manifest;  (* Trailing spaces *)
    spc001_manifest;   (* Differential spacing *)
    spc002_manifest;   (* Punctuation spacing *)
    spc003_manifest;   (* Non-breaking space *)
    char001_manifest;  (* Unicode validation *)
    char002_manifest;  (* Character encoding *)
    
    (* Additional L1_Expanded validators (2 validators) *)
    delim002_manifest; (* Extra closing braces *)
    delim004_manifest; (* Unmatched \right without \left *)
  ]
  
  (* Foundation Year 1 validator set (targeting 180 total) *)
  let foundation_year1_manifests = foundation_week2_manifests
end

(* Main DAG system initialization *)
let initialize_validator_system () =
  try
    printf "Building Week 2 Expansion validator DAG system...\n";
    let dag = ValidatorDAG.build_dag FoundationValidators.foundation_week2_manifests in
    
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

(* Note: This implements the DAG-based validator system as specified in 
   PLANNER_v25_R1.yaml Section 6, with proper conflict resolution,
   dependency management, and cycle detection. The system follows the
   planner's systematic approach for Year 1 foundation development. *)