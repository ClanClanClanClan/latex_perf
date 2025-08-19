(* environment_rules.ml - Environment matching and structure validators *)
(* Part of 623 total rules target for planner v25_R1 *)

open Printf
open Core_validation

(* Environment nesting rule *)
let environment_nesting_rule = {
  id = "ENV-001";
  name = "proper_environment_nesting";
  description = "Ensure environments are properly nested without overlap";
  severity = High;
  
  apply = fun content ->
    let env_stack = ref [] in
    let violations = ref [] in
    let pos = ref 0 in
    let len = String.length content in
    
    let extract_env_name start_pos =
      let rec find_brace pos =
        if pos < len && content.[pos] <> '{' then
          find_brace (pos + 1)
        else if pos < len then
          let end_pos = ref (pos + 1) in
          while !end_pos < len && content.[!end_pos] <> '}' do
            incr end_pos
          done;
          if !end_pos < len then
            Some (String.sub content (pos + 1) (!end_pos - pos - 1))
          else
            None
        else
          None
      in
      find_brace start_pos
    in
    
    while !pos < len - 6 do
      if String.sub content !pos 6 = "\\begin" then
        match extract_env_name (!pos + 6) with
        | Some env_name ->
            env_stack := (env_name, !pos, calculate_line content !pos) :: !env_stack;
            pos := !pos + 6
        | None -> incr pos
      else if !pos < len - 4 && String.sub content !pos 4 = "\\end" then
        match extract_env_name (!pos + 4) with
        | Some env_name ->
            (match !env_stack with
             | (expected_env, begin_pos, begin_line) :: rest when expected_env = env_name ->
                 env_stack := rest;
                 pos := !pos + 4
             | _ :: _ ->
                 violations := {
                   rule_id = "ENV-001";
                   message = sprintf "Improperly nested environment: \\end{%s}" env_name;
                   line = calculate_line content !pos;
                   column = calculate_column content !pos;
                   severity = High;
                 } :: !violations;
                 pos := !pos + 4
             | [] -> pos := !pos + 4)
        | None -> incr pos
      else
        incr pos
    done;
    
    List.rev !violations
}

(* Required environments rule *)
let required_environments_rule = {
  id = "ENV-002";
  name = "required_environments";
  description = "Check for required environments like document";
  severity = High;
  
  apply = fun content ->
    let violations = ref [] in
    let has_document = Str.string_match (Str.regexp "\\\\begin{document}") content 0 in
    
    if not has_document then
      violations := {
        rule_id = "ENV-002";
        message = "Missing required \\begin{document} environment";
        line = 1;
        column = 0;
        severity = High;
      } :: !violations;
    
    !violations
}

(* Math environment consistency *)
let math_environment_rule = {
  id = "ENV-003";
  name = "math_environment_consistency";
  description = "Ensure math environments are used consistently";
  severity = Medium;
  
  apply = fun content ->
    let violations = ref [] in
    let math_envs = ["equation"; "align"; "gather"; "multline"; "flalign"] in
    
    (* Check for mixed inline and display math *)
    let has_inline_math = Str.string_match (Str.regexp "\\$[^$]+\\$") content 0 in
    let has_display_math = Str.string_match (Str.regexp "\\$\\$[^$]+\\$\\$") content 0 in
    
    if has_inline_math && has_display_math then
      violations := {
        rule_id = "ENV-003";
        message = "Mixed inline ($) and display ($$) math delimiters - consider consistent approach";
        line = 1;
        column = 0;
        severity = Medium;
      } :: !violations;
    
    !violations
}

(* Figure environment structure *)
let figure_environment_rule = {
  id = "ENV-004";
  name = "figure_environment_structure";
  description = "Validate figure environment structure and required elements";
  severity = Medium;
  
  apply = fun content ->
    let violations = ref [] in
    let pos = ref 0 in
    let len = String.length content in
    
    while !pos < len - 13 do
      if String.sub content !pos 13 = "\\begin{figure" then begin
        let figure_start = !pos in
        let line_num = calculate_line content figure_start in
        
        (* Find end of figure *)
        let rec find_end_figure pos =
          if pos < len - 11 then
            if String.sub content pos 11 = "\\end{figure" then
              pos
            else
              find_end_figure (pos + 1)
          else
            len
        in
        
        let figure_end = find_end_figure (!pos + 13) in
        let figure_content = String.sub content figure_start (figure_end - figure_start) in
        
        (* Check for required elements *)
        let has_caption = Str.string_match (Str.regexp "\\\\caption") figure_content 0 in
        let has_label = Str.string_match (Str.regexp "\\\\label") figure_content 0 in
        
        if not has_caption then
          violations := {
            rule_id = "ENV-004";
            message = "Figure environment missing \\caption";
            line = line_num;
            column = 0;
            severity = Medium;
          } :: !violations;
        
        pos := figure_end + 11
      end else
        incr pos
    done;
    
    !violations
}

(* Table environment structure *)
let table_environment_rule = {
  id = "ENV-005";
  name = "table_environment_structure";
  description = "Validate table environment structure";
  severity = Medium;
  
  apply = fun content ->
    let violations = ref [] in
    let pos = ref 0 in
    let len = String.length content in
    
    while !pos < len - 12 do
      if String.sub content !pos 12 = "\\begin{table" then begin
        let table_start = !pos in
        let line_num = calculate_line content table_start in
        
        let rec find_end_table pos =
          if pos < len - 10 then
            if String.sub content pos 10 = "\\end{table" then
              pos
            else
              find_end_table (pos + 1)
          else
            len
        in
        
        let table_end = find_end_table (!pos + 12) in
        let table_content = String.sub content table_start (table_end - table_start) in
        
        (* Check for tabular environment *)
        let has_tabular = Str.string_match (Str.regexp "\\\\begin{tabular}") table_content 0 in
        let has_caption = Str.string_match (Str.regexp "\\\\caption") table_content 0 in
        
        if not has_tabular then
          violations := {
            rule_id = "ENV-005";
            message = "Table environment should contain tabular environment";
            line = line_num;
            column = 0;
            severity = Medium;
          } :: !violations;
        
        if not has_caption then
          violations := {
            rule_id = "ENV-005";
            message = "Table environment missing \\caption";
            line = line_num;
            column = 0;
            severity = Medium;
          } :: !violations;
        
        pos := table_end + 10
      end else
        incr pos
    done;
    
    !violations
}

(* Enumerate/itemize structure *)
let list_environment_rule = {
  id = "ENV-006";
  name = "list_environment_structure";
  description = "Validate enumerate and itemize environments have proper items";
  severity = Medium;
  
  apply = fun content ->
    let violations = ref [] in
    let list_envs = ["enumerate"; "itemize"; "description"] in
    
    List.iter (fun env ->
      let begin_pattern = sprintf "\\\\begin{%s}" env in
      let end_pattern = sprintf "\\\\end{%s}" env in
      let pos = ref 0 in
      let len = String.length content in
      
      while !pos < len - String.length begin_pattern do
        try
          let match_pos = Str.search_forward (Str.regexp begin_pattern) content !pos in
          let line_num = calculate_line content match_pos in
          
          (* Find end of environment *)
          let end_pos = 
            try Str.search_forward (Str.regexp end_pattern) content (match_pos + 1)
            with Not_found -> len
          in
          
          let env_content = String.sub content match_pos (end_pos - match_pos) in
          
          (* Check for \item commands *)
          let has_items = Str.string_match (Str.regexp "\\\\item") env_content 0 in
          
          if not has_items then
            violations := {
              rule_id = "ENV-006";
              message = sprintf "%s environment contains no \\item commands" env;
              line = line_num;
              column = 0;
              severity = Medium;
            } :: !violations;
          
          pos := end_pos + 1
        with Not_found ->
          pos := len
      done
    ) list_envs;
    
    !violations
}

(* Abstract environment check *)
let abstract_environment_rule = {
  id = "ENV-007";
  name = "abstract_placement";
  description = "Ensure abstract environment is properly placed";
  severity = Low;
  
  apply = fun content ->
    let violations = ref [] in
    
    try
      let abstract_pos = Str.search_forward (Str.regexp "\\\\begin{abstract}") content 0 in
      let document_pos = Str.search_forward (Str.regexp "\\\\begin{document}") content 0 in
      let line_num = calculate_line content abstract_pos in
      
      if abstract_pos < document_pos then
        violations := {
          rule_id = "ENV-007";
          message = "Abstract environment should be inside document environment";
          line = line_num;
          column = 0;
          severity = Low;
        } :: !violations
    with Not_found -> ();
    
    !violations
}

(* Export all environment rules *)
let all_environment_rules = [
  environment_nesting_rule;
  required_environments_rule;
  math_environment_rule;
  figure_environment_rule;
  table_environment_rule;
  list_environment_rule;
  abstract_environment_rule;
]

(* Rule count for planner tracking *)
let rule_count = List.length all_environment_rules