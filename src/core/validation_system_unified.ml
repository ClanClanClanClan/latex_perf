(* UNIFIED VALIDATION SYSTEM - USES PIPELINE_CORE TYPES *)
(* Production-ready validation system with proper architecture *)

open Pipeline_core

module UnifiedValidationSystem : ValidationSystem = struct

  (* === VALIDATION TYPES USING UNIFIED SYSTEM === *)
  
  type issue = {
    rule_id: string;
    message: string;
    position: Location.t;
    suggestion: string option;
    confidence: float;
    severity: [`Error | `Warning | `Info];
    category: string;
  }

  type validation_metrics = {
    total_tokens: int;
    total_issues: int;
    execution_time_ms: float;
    rules_triggered: string list;
    false_positive_estimate: float;
  }

  type input = located_token list
  type output = issue list * validation_metrics
  type error = string

  type options = {
    enabled_rules: string list option; (* None = all rules *)
    max_issues_per_rule: int;
    performance_mode: bool; (* Skip expensive rules *)
    confidence_threshold: float;
    category_filters: string list option;
  }

  let stage_name = "ValidationSystem"

  let default_options = {
    enabled_rules = None;
    max_issues_per_rule = 100;
    performance_mode = false;
    confidence_threshold = 0.5;
    category_filters = None;
  }

  (* === RULE EXECUTION FRAMEWORK === *)
  
  type rule_function = located_token list -> issue list

  type rule_definition = {
    id: string;
    name: string;
    description: string;
    category: string;
    cost: [`Low | `Medium | `High]; (* Performance cost *)
    enabled_by_default: bool;
    implementation: rule_function;
  }

  (* === UTILITY FUNCTIONS FOR RULE IMPLEMENTATIONS === *)
  
  let extract_chars_around_position tokens pos radius =
    let len = List.length tokens in
    let start_pos = max 0 (pos - radius) in
    let end_pos = min len (pos + radius + 1) in
    let relevant_tokens = List.filteri (fun i _ -> i >= start_pos && i < end_pos) tokens in
    let chars = List.filter_map (fun tok -> 
      match tok.token with
      | TChar (uchar, _) -> 
          let code = Uchar.to_int uchar in
          if code >= 32 && code <= 126 then Some (Char.chr code) else None
      | _ -> None
    ) relevant_tokens in
    String.of_seq (List.to_seq chars)

  let find_macro_sequence tokens start_pos macro_name =
    let rec search i =
      if i >= List.length tokens then None
      else
        match (List.nth tokens i).token with
        | TMacro name when String.equal name macro_name -> Some i
        | _ -> search (i + 1)
    in
    search start_pos

  let find_environment_bounds tokens env_name =
    let rec scan i depth acc =
      if i >= List.length tokens then acc
      else
        match (List.nth tokens i).token with
        | TMacro "begin" when i + 2 < List.length tokens ->
            (match (List.nth tokens (i+1)).token, (List.nth tokens (i+2)).token with
            | TGroupOpen, TMacro name when String.equal name env_name ->
                if depth = 0 then scan (i+3) 1 (Some i)
                else scan (i+3) (depth+1) acc
            | _ -> scan (i+1) depth acc)
        | TMacro "end" when i + 2 < List.length tokens ->
            (match (List.nth tokens (i+1)).token, (List.nth tokens (i+2)).token with
            | TGroupOpen, TMacro name when String.equal name env_name ->
                if depth = 1 then [(match acc with Some start -> start | None -> i), i]
                else scan (i+3) (depth-1) acc
            | _ -> scan (i+1) depth acc)
        | _ -> scan (i+1) depth acc
    in
    scan 0 0 None

  (* === RULE IMPLEMENTATIONS === *)
  
  (* Rule: Deprecated eqnarray environment *)
  let check_deprecated_environments tokens =
    let issues = ref [] in
    let deprecated_envs = ["eqnarray"; "eqnarray*"] in
    
    List.iteri (fun i tok ->
      match tok.token with
      | TMacro "begin" when i + 2 < List.length tokens ->
          (match (List.nth tokens (i+1)).token, (List.nth tokens (i+2)).token with
          | TGroupOpen, TMacro env_name when List.mem env_name deprecated_envs ->
              issues := {
                rule_id = "MATH-001";
                message = Printf.sprintf "Deprecated %s environment detected" env_name;
                position = tok.location;
                suggestion = Some "Use \\begin{align} from amsmath package instead";
                confidence = 0.95;
                severity = `Warning;
                category = "Math";
              } :: !issues
          | _ -> ())
      | _ -> ()
    ) tokens;
    List.rev !issues

  (* Rule: Figures without captions *)
  let check_figure_captions tokens =
    let issues = ref [] in
    let figure_bounds = find_environment_bounds tokens "figure" in
    
    List.iter (fun (start_pos, end_pos) ->
      let figure_tokens = List.filteri (fun i _ -> i >= start_pos && i <= end_pos) tokens in
      let has_caption = List.exists (fun tok -> 
        match tok.token with TMacro "caption" -> true | _ -> false
      ) figure_tokens in
      
      if not has_caption then
        let start_tok = List.nth tokens start_pos in
        issues := {
          rule_id = "FIG-001";
          message = "Figure environment without caption";
          position = start_tok.location;
          suggestion = Some "Add \\caption{description} to figure";
          confidence = 0.9;
          severity = `Warning;
          category = "Structure";
        } :: !issues
    ) figure_bounds;
    List.rev !issues

  (* Rule: Straight quotation marks *)
  let check_quotation_marks tokens =
    let issues = ref [] in
    
    List.iteri (fun i tok ->
      match tok.token with
      | TChar (uchar, _) ->
          let code = Uchar.to_int uchar in
          (match code with
          | 34 -> (* straight double quote *)
              issues := {
                rule_id = "TYPO-002";
                message = "Straight quotation marks found";
                position = tok.location;
                suggestion = Some "Use ``text'' for double quotes";
                confidence = 0.9;
                severity = `Warning;
                category = "Typography";
              } :: !issues
          | 39 -> (* straight single quote/apostrophe *)
              let context = extract_chars_around_position tokens i 3 in
              if String.contains context ' ' then (* likely a quote, not math prime *)
                issues := {
                  rule_id = "TYPO-003";
                  message = "Straight apostrophe/quote found";
                  position = tok.location;
                  suggestion = Some "Use LaTeX single quotes `text'";
                  confidence = 0.7;
                  severity = `Warning;
                  category = "Typography";
                } :: !issues
          | _ -> ())
      | _ -> ()
    ) tokens;
    List.rev !issues

  (* Rule: Environment nesting validation *)
  let check_environment_nesting tokens =
    let issues = ref [] in
    let env_stack = ref [] in
    
    List.iteri (fun i tok ->
      match tok.token with
      | TMacro "begin" when i + 2 < List.length tokens ->
          (match (List.nth tokens (i+1)).token, (List.nth tokens (i+2)).token with
          | TGroupOpen, TMacro env_name ->
              env_stack := (env_name, tok.location) :: !env_stack
          | _ -> ())
      | TMacro "end" when i + 2 < List.length tokens ->
          (match (List.nth tokens (i+1)).token, (List.nth tokens (i+2)).token with
          | TGroupOpen, TMacro env_name ->
              (match !env_stack with
              | (expected, _) :: rest when String.equal expected env_name ->
                  env_stack := rest
              | (expected, _) :: _ ->
                  issues := {
                    rule_id = "NEST-001";
                    message = Printf.sprintf "Environment mismatch: expected %s, got %s" expected env_name;
                    position = tok.location;
                    suggestion = Some "Fix environment nesting order";
                    confidence = 0.95;
                    severity = `Error;
                    category = "Structure";
                  } :: !issues
              | [] ->
                  issues := {
                    rule_id = "NEST-002";
                    message = Printf.sprintf "\\end{%s} without matching \\begin" env_name;
                    position = tok.location;
                    suggestion = Some "Add matching \\begin or remove \\end";
                    confidence = 0.9;
                    severity = `Error;
                    category = "Structure";
                  } :: !issues)
          | _ -> ())
      | _ -> ()
    ) tokens;
    
    (* Check for unclosed environments *)
    List.iter (fun (env_name, location) ->
      issues := {
        rule_id = "NEST-003";
        message = Printf.sprintf "Unclosed environment: %s" env_name;
        position = location;
        suggestion = Some (Printf.sprintf "Add \\end{%s}" env_name);
        confidence = 0.95;
        severity = `Error;
        category = "Structure";
      } :: !issues
    ) !env_stack;
    
    List.rev !issues

  (* Rule: Multiple consecutive spaces *)
  let check_spacing_consistency tokens =
    let issues = ref [] in
    let space_count = ref 0 in
    let space_start_pos = ref None in
    
    List.iteri (fun i tok ->
      match tok.token with
      | TSpace ->
          if !space_count = 0 then space_start_pos := Some tok.location;
          incr space_count
      | _ ->
          if !space_count > 2 then
            (match !space_start_pos with
            | Some pos ->
                issues := {
                  rule_id = "SPACE-001";
                  message = Printf.sprintf "Multiple consecutive spaces (%d)" !space_count;
                  position = pos;
                  suggestion = Some "Use single space or explicit spacing commands";
                  confidence = 0.8;
                  severity = `Warning;
                  category = "Spacing";
                } :: !issues
            | None -> ());
          space_count := 0;
          space_start_pos := None
    ) tokens;
    List.rev !issues

  (* Rule: Package conflicts *)
  let check_package_conflicts tokens =
    let issues = ref [] in
    let packages_loaded = ref [] in
    
    let conflict_groups = [
      (["natbib"; "biblatex"], "natbib and biblatex conflict - choose one bibliography system");
      (["amsmath"; "amstex"], "amsmath and amstex conflict - use amsmath for modern documents");  
      (["geometry"; "vmargin"], "geometry and vmargin conflict - geometry is preferred");
      (["enumitem"; "enumerate"], "enumitem and enumerate may conflict - enumitem is more powerful");
    ] in
    
    List.iteri (fun i tok ->
      match tok.token with
      | TMacro ("usepackage" | "RequirePackage") when i + 2 < List.length tokens ->
          (match (List.nth tokens (i+1)).token, (List.nth tokens (i+2)).token with
          | TGroupOpen, TMacro pkg_name ->
              packages_loaded := (pkg_name, tok.location) :: !packages_loaded;
              
              (* Check for conflicts *)
              List.iter (fun (conflict_pkgs, message) ->
                if List.mem pkg_name conflict_pkgs then
                  let conflicting = List.filter (fun (loaded_pkg, _) -> 
                    List.mem loaded_pkg conflict_pkgs && not (String.equal loaded_pkg pkg_name)
                  ) !packages_loaded in
                  if conflicting <> [] then
                    issues := {
                      rule_id = "PKG-001";
                      message = message;
                      position = tok.location;
                      suggestion = Some "Choose one package from conflicting set";
                      confidence = 0.9;
                      severity = `Error;
                      category = "Packages";
                    } :: !issues
              ) conflict_groups
          | _ -> ())
      | _ -> ()
    ) tokens;
    List.rev !issues

  (* === RULE REGISTRY === *)
  
  let rule_registry = [
    {
      id = "MATH-001";
      name = "Deprecated Math Environments";
      description = "Detects deprecated eqnarray environments";
      category = "Math";
      cost = `Low;
      enabled_by_default = true;
      implementation = check_deprecated_environments;
    };
    {
      id = "FIG-001"; 
      name = "Figure Captions";
      description = "Ensures figures have captions";
      category = "Structure";
      cost = `Medium;
      enabled_by_default = true;
      implementation = check_figure_captions;
    };
    {
      id = "TYPO-002/003";
      name = "Quotation Marks";
      description = "Detects straight quotation marks";
      category = "Typography";
      cost = `Low;
      enabled_by_default = true;
      implementation = check_quotation_marks;
    };
    {
      id = "NEST-001/002/003";
      name = "Environment Nesting";
      description = "Validates environment nesting";
      category = "Structure";
      cost = `Medium;
      enabled_by_default = true;
      implementation = check_environment_nesting;
    };
    {
      id = "SPACE-001";
      name = "Spacing Consistency";
      description = "Detects multiple consecutive spaces";
      category = "Spacing";
      cost = `Low;
      enabled_by_default = true;
      implementation = check_spacing_consistency;
    };
    {
      id = "PKG-001";
      name = "Package Conflicts";
      description = "Detects conflicting package combinations";
      category = "Packages";
      cost = `Medium;
      enabled_by_default = true;
      implementation = check_package_conflicts;
    };
  ]

  (* === PIPELINE STAGE IMPLEMENTATION === *)
  
  let validate_input tokens = 
    List.for_all (fun tok -> 
      match tok.token with 
      | TChar _ | TMacro _ | TParam _ | TGroupOpen | TGroupClose 
      | TMathShift | TAlignTab | TEndLine | TSpace | TComment _ | TEOF -> true
    ) tokens

  let validate_output (issues, metrics) =
    List.for_all (fun issue -> 
      String.length issue.rule_id > 0 && 
      String.length issue.message > 0 &&
      issue.confidence >= 0.0 && issue.confidence <= 1.0
    ) issues &&
    metrics.total_tokens >= 0 &&
    metrics.total_issues >= 0 &&
    metrics.execution_time_ms >= 0.0

  let process options tokens =
    let start_time = Sys.time () in
    
    if not (validate_input tokens) then
      Error "Invalid input tokens"
    else
      try
        let all_issues = ref [] in
        let rules_triggered = ref [] in
        
        (* Apply rule filters *)
        let active_rules = match options.enabled_rules with
          | None -> rule_registry
          | Some enabled -> List.filter (fun rule -> List.mem rule.id enabled) rule_registry
        in
        
        let active_rules = if options.performance_mode then
          List.filter (fun rule -> rule.cost <> `High) active_rules
        else active_rules in
        
        (* Execute all active rules *)
        List.iter (fun rule ->
          try
            let rule_issues = rule.implementation tokens in
            let filtered_issues = List.filter (fun issue -> 
              issue.confidence >= options.confidence_threshold
            ) rule_issues in
            let limited_issues = 
              if List.length filtered_issues > options.max_issues_per_rule then
                List.take options.max_issues_per_rule filtered_issues
              else filtered_issues
            in
            
            if List.length limited_issues > 0 then
              rules_triggered := rule.id :: !rules_triggered;
            all_issues := !all_issues @ limited_issues
          with
          | exn -> 
              (* Log rule execution error but continue *)
              Printf.eprintf "Warning: Rule %s failed: %s\n" rule.id (Printexc.to_string exn)
        ) active_rules;
        
        let execution_time = (Sys.time () -. start_time) *. 1000.0 in
        let issue_count = List.length !all_issues in
        
        (* Estimate false positive rate based on issue density *)
        let token_count = List.length tokens in
        let issue_density = if token_count > 0 then float issue_count /. float token_count else 0.0 in
        let false_positive_estimate = min 1.0 (issue_density *. 0.1) in
        
        let metrics = {
          total_tokens = token_count;
          total_issues = issue_count;
          execution_time_ms = execution_time;
          rules_triggered = List.rev !rules_triggered;
          false_positive_estimate = false_positive_estimate;
        } in
        
        let stage_metrics = {
          stage_name = "ValidationSystem";
          input_size = token_count;
          output_size = issue_count;
          execution_time_ms = execution_time;
          memory_used_kb = 0; (* Would need proper memory measurement *)
          errors_encountered = 0;
        } in
        
        let result = (List.rev !all_issues, metrics) in
        if validate_output result then
          Success (result, stage_metrics)
        else
          Error "Invalid output generated"
      with
      | exn -> Error (Printf.sprintf "Validation failed: %s" (Printexc.to_string exn))

  let run_validation ?(options = default_options) tokens =
    match process options tokens with
    | Success ((issues, metrics), stage_metrics) -> 
        Success (issues, metrics, stage_metrics)
    | Error msg -> Error msg

  let get_available_rules () = 
    List.map (fun rule -> rule.id) rule_registry

  let get_rule_description rule_id = 
    try
      let rule = List.find (fun r -> String.equal r.id rule_id) rule_registry in
      Some rule.description
    with Not_found -> None

end