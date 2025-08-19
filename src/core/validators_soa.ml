(* PHASE 3: SoA-compatible validators for off-heap token processing *)
open Tokens_soa

(* Issue type - same as original *)
type severity = Error | Warning | Info | Style

type issue = {
  rule_id: string;
  severity: severity;
  message: string;
  file: string;
  line: int;
  column: int;
  end_line: int;
  end_column: int;
  suggestion: string option;
}

(* Ellipsis validator - operates directly on SoA *)
let check_ellipsis_soa soa =
  let issues = ref [] in
  let len = soa.n in
  
  (* Process tokens directly from off-heap arrays *)
  for i = 0 to len - 3 do
    let c1 = unsafe_get_kind soa i in
    let d1 = unsafe_get_data soa i in
    
    if c1 = 12 && d1 = 46 then ( (* period catcode=12, char=46 *)
      let c2 = unsafe_get_kind soa (i + 1) in
      let d2 = unsafe_get_data soa (i + 1) in
      let c3 = unsafe_get_kind soa (i + 2) in
      let d3 = unsafe_get_data soa (i + 2) in
      
      if c2 = 12 && d2 = 46 && c3 = 12 && d3 = 46 then (
        let line = unsafe_get_line soa i in
        let col = unsafe_get_col soa i in
        issues := {
          rule_id = "ellipsis-001";
          severity = Warning;
          message = "Use \\ldots instead of three periods";
          file = "";
          line = line;
          column = col;
          end_line = line;
          end_column = col + 3;
          suggestion = Some "\\ldots";
        } :: !issues
      )
    )
  done;
  !issues

(* Math mode validator - operates directly on SoA *)
let check_math_mode_soa soa =
  let issues = ref [] in
  let len = soa.n in
  let in_math = ref false in
  
  for i = 0 to len - 1 do
    let catcode = unsafe_get_kind soa i in
    
    if catcode = 3 then (* math shift catcode *)
      in_math := not !in_math
    else if !in_math && catcode = 11 then ( (* letter in math *)
      let line = unsafe_get_line soa i in
      let col = unsafe_get_col soa i in
      issues := {
        rule_id = "math-002";
        severity = Info;
        message = "Consider using \\text{} for text in math mode";
        file = "";
        line = line;
        column = col;
        end_line = line;
        end_column = col + 1;
        suggestion = None;
      } :: !issues
    )
  done;
  !issues

(* Fast bracket balance validator - demonstrates SoA performance *)
let check_bracket_balance_soa soa =
  let issues = ref [] in
  let len = soa.n in
  let depth = ref 0 in
  
  for i = 0 to len - 1 do
    let catcode = unsafe_get_kind soa i in
    let data = unsafe_get_data soa i in
    
    match catcode, data with
    | 1, 123 -> incr depth  (* { catcode=1, char=123 *)
    | 2, 125 ->             (* } catcode=2, char=125 *)
        decr depth;
        if !depth < 0 then (
          let line = unsafe_get_line soa i in
          let col = unsafe_get_col soa i in
          issues := {
            rule_id = "bracket-001";
            severity = Error;
            message = "Unmatched closing brace";
            file = "";
            line = line;
            column = col;
            end_line = line;
            end_column = col + 1;
            suggestion = None;
          } :: !issues;
          depth := 0
        )
    | _ -> ()
  done;
  
  (* Check for unclosed braces *)
  if !depth > 0 then (
    issues := {
      rule_id = "bracket-002";
      severity = Error;
      message = Printf.sprintf "%d unclosed braces" !depth;
      file = "";
      line = 1;
      column = 1;
      end_line = 1;
      end_column = 1;
      suggestion = None;
    } :: !issues
  );
  
  !issues

(* SoA validator dispatcher *)
let validate_soa ?(mode="all") soa =
  match mode with
  | "minimal" ->
      (* Only math mode for maximum performance *)
      check_math_mode_soa soa
  | "critical" ->
      (* Essential validators *)
      let math_issues = check_math_mode_soa soa in
      let ellipsis_issues = check_ellipsis_soa soa in
      List.append math_issues ellipsis_issues
  | "enhanced" ->
      (* All validators including new bracket checker *)
      let math_issues = check_math_mode_soa soa in
      let ellipsis_issues = check_ellipsis_soa soa in
      let bracket_issues = check_bracket_balance_soa soa in
      List.concat [math_issues; ellipsis_issues; bracket_issues]
  | _ ->
      (* Standard all validators *)
      let ellipsis_issues = check_ellipsis_soa soa in
      let math_issues = check_math_mode_soa soa in
      List.append ellipsis_issues math_issues