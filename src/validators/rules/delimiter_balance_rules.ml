(* delimiter_balance_rules.ml - Delimiter balance validators for LaTeX *)
(* Generated for planner v25_R1 goal of 623 total rules *)

open Printf
open Core_validation

(* Delimiter balance rule: Braces *)
let brace_balance_rule = {
  id = "DELIM-001";
  name = "brace_balance";
  description = "Ensure curly braces {} are properly balanced";
  severity = High;
  
  apply = fun content ->
    let open_count = ref 0 in
    let violations = ref [] in
    let pos = ref 0 in
    
    String.iteri (fun i c ->
      match c with
      | '{' -> 
          incr open_count;
          pos := i
      | '}' -> 
          if !open_count > 0 then
            decr open_count
          else
            violations := {
              rule_id = "DELIM-001";
              message = "Unmatched closing brace '}'";
              line = calculate_line content i;
              column = calculate_column content i;
              severity = High;
            } :: !violations
      | _ -> ()
    ) content;
    
    (* Check for unmatched opening braces *)
    if !open_count > 0 then
      violations := {
        rule_id = "DELIM-001";
        message = sprintf "%d unmatched opening brace(s) '{'" !open_count;
        line = calculate_line content (String.length content - 1);
        column = 0;
        severity = High;
      } :: !violations;
    
    List.rev !violations
}

(* Delimiter balance rule: Square brackets *)
let bracket_balance_rule = {
  id = "DELIM-002";
  name = "bracket_balance";
  description = "Ensure square brackets [] are properly balanced";
  severity = Medium;
  
  apply = fun content ->
    let open_count = ref 0 in
    let violations = ref [] in
    
    String.iteri (fun i c ->
      match c with
      | '[' -> incr open_count
      | ']' -> 
          if !open_count > 0 then
            decr open_count
          else
            violations := {
              rule_id = "DELIM-002";
              message = "Unmatched closing bracket ']'";
              line = calculate_line content i;
              column = calculate_column content i;
              severity = Medium;
            } :: !violations
      | _ -> ()
    ) content;
    
    if !open_count > 0 then
      violations := {
        rule_id = "DELIM-002";
        message = sprintf "%d unmatched opening bracket(s) '['" !open_count;
        line = calculate_line content (String.length content - 1);
        column = 0;
        severity = Medium;
      } :: !violations;
    
    List.rev !violations
}

(* Delimiter balance rule: Parentheses *)
let paren_balance_rule = {
  id = "DELIM-003";
  name = "paren_balance";
  description = "Ensure parentheses () are properly balanced";
  severity = Medium;
  
  apply = fun content ->
    let open_count = ref 0 in
    let violations = ref [] in
    
    String.iteri (fun i c ->
      match c with
      | '(' -> incr open_count
      | ')' -> 
          if !open_count > 0 then
            decr open_count
          else
            violations := {
              rule_id = "DELIM-003";
              message = "Unmatched closing parenthesis ')'";
              line = calculate_line content i;
              column = calculate_column content i;
              severity = Medium;
            } :: !violations
      | _ -> ()
    ) content;
    
    if !open_count > 0 then
      violations := {
        rule_id = "DELIM-003";
        message = sprintf "%d unmatched opening parenthesis(es) '('" !open_count;
        line = calculate_line content (String.length content - 1);
        column = 0;
        severity = Medium;
      } :: !violations;
    
    List.rev !violations
}

(* Math delimiter balance: $ signs *)
let math_delimiter_rule = {
  id = "DELIM-004";
  name = "math_delimiter_balance";
  description = "Ensure inline math delimiters $ are properly paired";
  severity = High;
  
  apply = fun content ->
    let in_math = ref false in
    let violations = ref [] in
    let last_dollar_pos = ref (-1) in
    
    String.iteri (fun i c ->
      if c = '$' && (i = 0 || content.[i-1] <> '\\') then
        if !in_math then begin
          in_math := false;
          last_dollar_pos := -1
        end else begin
          in_math := true;
          last_dollar_pos := i
        end
    ) content;
    
    if !in_math then
      violations := {
        rule_id = "DELIM-004";
        message = "Unmatched math delimiter '$'";
        line = calculate_line content !last_dollar_pos;
        column = calculate_column content !last_dollar_pos;
        severity = High;
      } :: !violations;
    
    !violations
}

(* Display math delimiter balance: $$ signs *)
let display_math_delimiter_rule = {
  id = "DELIM-005";
  name = "display_math_delimiter_balance";
  description = "Ensure display math delimiters $$ are properly paired";
  severity = High;
  
  apply = fun content ->
    let violations = ref [] in
    let pos = ref 0 in
    let len = String.length content in
    let in_display_math = ref false in
    let last_pos = ref (-1) in
    
    while !pos < len - 1 do
      if content.[!pos] = '$' && content.[!pos + 1] = '$' then
        if !in_display_math then begin
          in_display_math := false;
          pos := !pos + 2
        end else begin
          in_display_math := true;
          last_pos := !pos;
          pos := !pos + 2
        end
      else
        incr pos
    done;
    
    if !in_display_math then
      violations := {
        rule_id = "DELIM-005";
        message = "Unmatched display math delimiter '$$'";
        line = calculate_line content !last_pos;
        column = calculate_column content !last_pos;
        severity = High;
      } :: !violations;
    
    !violations
}

(* Begin/End environment balance *)
let begin_end_balance_rule = {
  id = "DELIM-006";
  name = "begin_end_balance";
  description = "Ensure \\begin{} and \\end{} commands are properly balanced";
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
            env_stack := (env_name, calculate_line content !pos) :: !env_stack;
            pos := !pos + 6
        | None -> incr pos
      else if !pos < len - 4 && String.sub content !pos 4 = "\\end" then
        match extract_env_name (!pos + 4) with
        | Some env_name ->
            (match !env_stack with
             | (expected_env, _) :: rest when expected_env = env_name ->
                 env_stack := rest;
                 pos := !pos + 4
             | (expected_env, begin_line) :: _ ->
                 violations := {
                   rule_id = "DELIM-006";
                   message = sprintf "Environment mismatch: \\end{%s} but expected \\end{%s} (opened at line %d)" 
                     env_name expected_env begin_line;
                   line = calculate_line content !pos;
                   column = calculate_column content !pos;
                   severity = High;
                 } :: !violations;
                 pos := !pos + 4
             | [] ->
                 violations := {
                   rule_id = "DELIM-006";
                   message = sprintf "Unmatched \\end{%s}" env_name;
                   line = calculate_line content !pos;
                   column = calculate_column content !pos;
                   severity = High;
                 } :: !violations;
                 pos := !pos + 4)
        | None -> incr pos
      else
        incr pos
    done;
    
    (* Check for unclosed environments *)
    List.iter (fun (env_name, line) ->
      violations := {
        rule_id = "DELIM-006";
        message = sprintf "Unclosed environment: \\begin{%s}" env_name;
        line;
        column = 0;
        severity = High;
      } :: !violations
    ) !env_stack;
    
    List.rev !violations
}

(* Angle bracket balance for \langle \rangle *)
let angle_bracket_rule = {
  id = "DELIM-007";
  name = "angle_bracket_balance";
  description = "Ensure \\langle and \\rangle are properly balanced";
  severity = Medium;
  
  apply = fun content ->
    let open_count = ref 0 in
    let violations = ref [] in
    let pos = ref 0 in
    let len = String.length content in
    
    while !pos < len - 6 do
      if String.sub content !pos 7 = "\\langle" then begin
        incr open_count;
        pos := !pos + 7
      end else if String.sub content !pos 7 = "\\rangle" then
        if !open_count > 0 then begin
          decr open_count;
          pos := !pos + 7
        end else begin
          violations := {
            rule_id = "DELIM-007";
            message = "Unmatched \\rangle";
            line = calculate_line content !pos;
            column = calculate_column content !pos;
            severity = Medium;
          } :: !violations;
          pos := !pos + 7
        end
      else
        incr pos
    done;
    
    if !open_count > 0 then
      violations := {
        rule_id = "DELIM-007";
        message = sprintf "%d unmatched \\langle" !open_count;
        line = calculate_line content (len - 1);
        column = 0;
        severity = Medium;
      } :: !violations;
    
    List.rev !violations
}

(* Quote balance for " pairs *)
let quote_balance_rule = {
  id = "DELIM-008";
  name = "quote_balance";
  description = "Ensure double quotes are properly balanced";
  severity = Low;
  
  apply = fun content ->
    let in_quote = ref false in
    let violations = ref [] in
    let last_quote_pos = ref (-1) in
    
    String.iteri (fun i c ->
      if c = '"' && (i = 0 || content.[i-1] <> '\\') then
        if !in_quote then begin
          in_quote := false;
          last_quote_pos := -1
        end else begin
          in_quote := true;
          last_quote_pos := i
        end
    ) content;
    
    if !in_quote then
      violations := {
        rule_id = "DELIM-008";
        message = "Unmatched double quote";
        line = calculate_line content !last_quote_pos;
        column = calculate_column content !last_quote_pos;
        severity = Low;
      } :: !violations;
    
    !violations
}

(* Export all delimiter balance rules *)
let all_delimiter_balance_rules = [
  brace_balance_rule;
  bracket_balance_rule;
  paren_balance_rule;
  math_delimiter_rule;
  display_math_delimiter_rule;
  begin_end_balance_rule;
  angle_bracket_rule;
  quote_balance_rule;
]

(* Rule count for planner tracking *)
let rule_count = List.length all_delimiter_balance_rules