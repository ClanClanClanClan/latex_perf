(* Typography Validation Rules - LaTeX Perfectionist v25 *)
(* Implements typography and formatting validation rules *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

(* Helper to check if a token is a specific character *)
let is_char c tok = match tok with
  | TChar (uc, _) -> Uchar.to_int uc = Char.code c
  | _ -> false

(* Helper to get character code from token *)
let get_char_code = function
  | TChar (uc, _) -> Some (Uchar.to_int uc)
  | _ -> None

type rule_severity = Info | Warning | Error

type validation_rule = {
  id: string;
  name: string;
  description: string;
  severity: rule_severity;
  category: string;
  check: token array -> validation_issue list;
}

and validation_issue = {
  rule_id: string;
  message: string;
  location: Location.t;
  suggestion: string option;
  confidence: float; (* 0.0 to 1.0 *)
}

(** Quote and punctuation rules *)
module QuoteRules = struct
  (* Rule: Use smart quotes instead of straight quotes *)
  let smart_quotes_rule = {
    id = "TYPO-001";
    name = "smart_quotes";
    description = "Use `` and '' for quotes instead of \"";
    severity = Warning;
    category = "typography";
    check = fun tokens ->
      let issues = ref [] in
      Array.iteri (fun i tok ->
        if is_char '"' tok then
          issues := {
            rule_id = "TYPO-001";
            message = "Use `` for opening quotes or '' for closing quotes";
            location = Location.make 0 0;
            suggestion = Some "Replace \" with `` or ''";
            confidence = 0.9;
          } :: !issues
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Correct ellipsis usage *)
  let ellipsis_rule = {
    id = "TYPO-002";
    name = "ellipsis";
    description = "Use \\ldots instead of ...";
    severity = Info;
    category = "typography";
    check = fun tokens ->
      let issues = ref [] in
      let rec check_dots i count =
        if i >= Array.length tokens then ()
        else match tokens.(i) with
        | TChar '.' when count = 2 ->
            issues := {
              rule_id = "TYPO-002";
              message = "Use \\ldots for ellipsis";
              location = Location.make 0 0;
              suggestion = Some "Replace ... with \\ldots";
              confidence = 0.95;
            } :: !issues;
            check_dots (i + 1) 0
        | TChar '.' -> check_dots (i + 1) (count + 1)
        | _ -> check_dots (i + 1) 0
      in
      check_dots 0 0;
      List.rev !issues
  }
  
  (* Rule: Em-dash and en-dash usage *)
  let dash_rule = {
    id = "TYPO-003";
    name = "dashes";
    description = "Use -- for en-dash and --- for em-dash";
    severity = Info;
    category = "typography";
    check = fun tokens ->
      let issues = ref [] in
      Array.iteri (fun i tok ->
        match tok with
        | TChar '-' when i > 0 && i < Array.length tokens - 1 ->
            (match tokens.(i-1), tokens.(i+1) with
            | TChar c1, TChar c2 when 
                Char.code c1 >= 48 && Char.code c1 <= 57 &&
                Char.code c2 >= 48 && Char.code c2 <= 57 ->
                (* Number range *)
                issues := {
                  rule_id = "TYPO-003";
                  message = "Use -- for number ranges";
                  location = Location.make 0 0;
                  suggestion = Some "Replace - with -- for ranges";
                  confidence = 0.8;
                } :: !issues
            | _ -> ())
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
end

(** Spacing rules *)
module SpacingRules = struct
  (* Rule: Non-breaking space before citations *)
  let nbsp_before_cite = {
    id = "SPACE-001";
    name = "nbsp_citations";
    description = "Use ~ before \\cite to prevent line breaks";
    severity = Warning;
    category = "spacing";
    check = fun tokens ->
      let issues = ref [] in
      Array.iteri (fun i tok ->
        match tok with
        | TMacro "cite" when i > 0 ->
            (match tokens.(i-1) with
            | TChar ' ' ->
                issues := {
                  rule_id = "SPACE-001";
                  message = "Use ~ before \\cite to prevent line breaks";
                  location = Location.make 0 0;
                  suggestion = Some "Replace space with ~";
                  confidence = 0.9;
                } :: !issues
            | _ -> ())
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Spacing around math *)
  let math_spacing = {
    id = "SPACE-002";
    name = "math_spacing";
    description = "Ensure proper spacing around inline math";
    severity = Info;
    category = "spacing";
    check = fun tokens ->
      let issues = ref [] in
      let in_math = ref false in
      Array.iteri (fun i tok ->
        match tok with
        | TMathShift ->
            in_math := not !in_math;
            if not !in_math && i < Array.length tokens - 1 then
              (match tokens.(i+1) with
              | TChar c when Char.code c >= 65 && Char.code c <= 122 ->
                  issues := {
                    rule_id = "SPACE-002";
                    message = "Add space after closing $";
                    location = Location.make 0 0;
                    suggestion = Some "Add space after math mode";
                    confidence = 0.7;
                  } :: !issues
              | _ -> ())
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Multiple spaces *)
  let multiple_spaces = {
    id = "SPACE-003";
    name = "multiple_spaces";
    description = "Avoid multiple consecutive spaces";
    severity = Info;
    category = "spacing";
    check = fun tokens ->
      let issues = ref [] in
      let space_count = ref 0 in
      Array.iter (fun tok ->
        match tok with
        | TChar ' ' ->
            incr space_count;
            if !space_count > 1 then
              issues := {
                rule_id = "SPACE-003";
                message = "Multiple consecutive spaces detected";
                location = Location.make 0 0;
                suggestion = Some "Use single space";
                confidence = 0.95;
              } :: !issues
        | TChar '\n' | TChar '\r' -> space_count := 0
        | _ -> space_count := 0
      ) tokens;
      List.rev !issues
  }
end

(** Consistency rules *)
module ConsistencyRules = struct
  (* Rule: Consistent macro usage *)
  let macro_consistency = {
    id = "CONS-001";
    name = "macro_variants";
    description = "Use consistent macro variants";
    severity = Warning;
    category = "consistency";
    check = fun tokens ->
      let issues = ref [] in
      let seen_macros = Hashtbl.create 100 in
      
      Array.iter (function
        | TMacro name ->
            (* Check for similar macros *)
            let variants = [
              ("epsilon", "varepsilon");
              ("phi", "varphi");
              ("theta", "vartheta");
              ("rho", "varrho");
            ] in
            List.iter (fun (base, variant) ->
              if name = base && Hashtbl.mem seen_macros variant then
                issues := {
                  rule_id = "CONS-001";
                  message = Printf.sprintf "Inconsistent use of \\%s and \\%s" base variant;
                  location = Location.make 0 0;
                  suggestion = Some "Use one variant consistently";
                  confidence = 0.8;
                } :: !issues
              else if name = variant && Hashtbl.mem seen_macros base then
                issues := {
                  rule_id = "CONS-001";
                  message = Printf.sprintf "Inconsistent use of \\%s and \\%s" variant base;
                  location = Location.make 0 0;
                  suggestion = Some "Use one variant consistently";
                  confidence = 0.8;
                } :: !issues
            ) variants;
            Hashtbl.replace seen_macros name true
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Abbreviation consistency *)
  let abbreviation_consistency = {
    id = "CONS-002";
    name = "abbreviations";
    description = "Use consistent abbreviations";
    severity = Info;
    category = "consistency";
    check = fun tokens ->
      let issues = ref [] in
      let abbrevs = Hashtbl.create 50 in
      
      (* Track common abbreviations *)
      let common_abbrevs = [
        ("e.g.", "eg");
        ("i.e.", "ie");
        ("etc.", "etc");
        ("Fig.", "Figure");
        ("Eq.", "Equation");
      ] in
      
      (* Simple pattern matching for abbreviations *)
      let rec scan i =
        if i >= Array.length tokens - 2 then ()
        else match tokens.(i), tokens.(i+1), tokens.(i+2) with
        | TChar 'e', TChar '.', TChar 'g' ->
            Hashtbl.add abbrevs "e.g." i;
            scan (i + 3)
        | TChar 'i', TChar '.', TChar 'e' ->
            Hashtbl.add abbrevs "i.e." i;
            scan (i + 3)
        | _ -> scan (i + 1)
      in
      scan 0;
      
      (* Check for inconsistencies *)
      List.iter (fun (formal, informal) ->
        let has_formal = Hashtbl.mem abbrevs formal in
        let has_informal = Hashtbl.mem abbrevs informal in
        if has_formal && has_informal then
          issues := {
            rule_id = "CONS-002";
            message = Printf.sprintf "Inconsistent abbreviation: both '%s' and '%s' used" formal informal;
            location = Location.make 0 0;
            suggestion = Some "Use one form consistently";
            confidence = 0.7;
          } :: !issues
      ) common_abbrevs;
      
      List.rev !issues
  }
end

(** Math notation rules *)
module MathRules = struct
  (* Rule: Proper function names *)
  let function_names = {
    id = "MATH-001";
    name = "function_names";
    description = "Use \\sin, \\cos, etc. instead of sin, cos in math";
    severity = Warning;
    category = "math";
    check = fun tokens ->
      let issues = ref [] in
      let in_math = ref false in
      let func_names = ["sin"; "cos"; "tan"; "log"; "ln"; "exp"; "min"; "max"] in
      
      Array.iteri (fun i tok ->
        match tok with
        | TMathShift -> in_math := not !in_math
        | TChar c when !in_math && i < Array.length tokens - 2 ->
            (* Check for function names spelled out *)
            let check_func name =
              let len = String.length name in
              if i + len <= Array.length tokens then
                let matches = ref true in
                for j = 0 to len - 1 do
                  match tokens.(i + j) with
                  | TChar ch when ch = name.[j] -> ()
                  | _ -> matches := false
                done;
                if !matches then
                  issues := {
                    rule_id = "MATH-001";
                    message = Printf.sprintf "Use \\%s instead of %s in math mode" name name;
                    location = Location.make 0 0;
                    suggestion = Some (Printf.sprintf "Replace with \\%s" name);
                    confidence = 0.9;
                  } :: !issues
            in
            List.iter check_func func_names
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Consistent integral limits *)
  let integral_limits = {
    id = "MATH-002";
    name = "integral_limits";
    description = "Use consistent integral limit placement";
    severity = Info;
    category = "math";
    check = fun tokens ->
      let issues = ref [] in
      let has_limits = ref false in
      let has_nolimits = ref false in
      
      Array.iter (function
        | TMacro "int" -> ()
        | TMacro "limits" -> has_limits := true
        | TMacro "nolimits" -> has_nolimits := true
        | _ -> ()
      ) tokens;
      
      if !has_limits && !has_nolimits then
        issues := {
          rule_id = "MATH-002";
          message = "Inconsistent use of \\limits and \\nolimits";
          location = Location.make 0 0;
          suggestion = Some "Use one style consistently";
          confidence = 0.8;
        } :: !issues;
      
      List.rev !issues
  }
end

(** Collect all typography rules *)
let all_rules = [
  QuoteRules.smart_quotes_rule;
  QuoteRules.ellipsis_rule;
  QuoteRules.dash_rule;
  SpacingRules.nbsp_before_cite;
  SpacingRules.math_spacing;
  SpacingRules.multiple_spaces;
  ConsistencyRules.macro_consistency;
  ConsistencyRules.abbreviation_consistency;
  MathRules.function_names;
  MathRules.integral_limits;
]

(** Run all validation rules *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    acc @ List.map (fun issue -> (rule, issue)) issues
  ) [] all_rules

(** Get rule count *)
let rule_count () = List.length all_rules

(** Get rules by category *)
let rules_by_category category =
  List.filter (fun r -> r.category = category) all_rules

(** Get rules by severity *)
let rules_by_severity severity =
  List.filter (fun r -> r.severity = severity) all_rules