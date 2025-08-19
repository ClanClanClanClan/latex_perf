(* Punctuation Rules - LaTeX Perfectionist v25 *)
(* Week 2 Sprint: Ellipsis and dash validation *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

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
  confidence: float;
}

(** ELLIPSIS RULES **)

(** Rule: Use \ldots instead of ... *)
let ellipsis_dots_rule = {
  id = "ELLIP-001";
  name = "ellipsis_command";
  description = "Use \\ldots instead of three periods";
  severity = Warning;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    let dot_count = ref 0 in
    let first_dot_loc = ref Location.dummy in
    
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 46 -> (* period *)
          if !dot_count = 0 then first_dot_loc := loc;
          incr dot_count;
          if !dot_count >= 3 then begin
            issues := {
              rule_id = "ELLIP-001";
              message = "Three periods ... found";
              location = !first_dot_loc;
              suggestion = Some "Replace with \\ldots";
              confidence = 0.95;
            } :: !issues;
            dot_count := 0
          end
      | _ -> dot_count := 0
    ) tokens;
    List.rev !issues
}

(** Rule: Correct ellipsis context *)
let ellipsis_context_rule = {
  id = "ELLIP-002";
  name = "ellipsis_context";
  description = "Use appropriate ellipsis command for context";
  severity = Info;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    let in_math = ref false in
    
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, _) when Uchar.to_int uc = Char.code '$' ->
          in_math := not !in_math
      | TCmd ((_, name), loc) when name = "ldots" && !in_math ->
          issues := {
            rule_id = "ELLIP-002";
            message = "Consider \\cdots in math mode";
            location = loc;
            suggestion = Some "Use \\cdots for centered dots in math";
            confidence = 0.7;
          } :: !issues
      | TCmd ((_, name), loc) when name = "cdots" && not !in_math ->
          issues := {
            rule_id = "ELLIP-002";
            message = "\\cdots used outside math mode";
            location = loc;
            suggestion = Some "Use \\ldots in text mode";
            confidence = 0.9;
          } :: !issues
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Unicode ellipsis *)
let unicode_ellipsis_rule = {
  id = "ELLIP-003";
  name = "unicode_ellipsis";
  description = "Avoid Unicode ellipsis character";
  severity = Warning;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 0x2026 -> (* … *)
          issues := {
            rule_id = "ELLIP-003";
            message = "Unicode ellipsis … found";
            location = loc;
            suggestion = Some "Replace with \\ldots";
            confidence = 1.0;
          } :: !issues
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** DASH RULES **)

(** Rule: Proper dash usage *)
let dash_types_rule = {
  id = "DASH-001";
  name = "dash_types";
  description = "Use correct dash types";
  severity = Warning;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    let hyphen_count = ref 0 in
    let first_hyphen_loc = ref Location.dummy in
    
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 45 -> (* hyphen *)
          if !hyphen_count = 0 then first_hyphen_loc := loc;
          incr hyphen_count;
          
          (* Check what follows *)
          if i < Array.length tokens - 1 then begin
            match tokens.(i+1) with
            | TChar (next_uc, _) when Uchar.to_int next_uc = 45 ->
                () (* Will be handled in next iteration *)
            | _ ->
                (* Process accumulated hyphens *)
                if !hyphen_count = 2 then
                  issues := {
                    rule_id = "DASH-001";
                    message = "Double hyphen -- found";
                    location = !first_hyphen_loc;
                    suggestion = Some "This creates an en-dash (correct for ranges)";
                    confidence = 0.6;
                  } :: !issues
                else if !hyphen_count = 3 then
                  issues := {
                    rule_id = "DASH-001";
                    message = "Triple hyphen --- found";
                    location = !first_hyphen_loc;
                    suggestion = Some "This creates an em-dash (correct for breaks)";
                    confidence = 0.6;
                  } :: !issues
                else if !hyphen_count > 3 then
                  issues := {
                    rule_id = "DASH-001";
                    message = Printf.sprintf "%d hyphens in a row" !hyphen_count;
                    location = !first_hyphen_loc;
                    suggestion = Some "Use -- for en-dash or --- for em-dash";
                    confidence = 0.9;
                  } :: !issues;
                hyphen_count := 0
          end
      | _ -> 
          if !hyphen_count > 3 then
            issues := {
              rule_id = "DASH-001";
              message = Printf.sprintf "%d hyphens in a row" !hyphen_count;
              location = !first_hyphen_loc;
              suggestion = Some "Use -- for en-dash or --- for em-dash";
              confidence = 0.9;
            } :: !issues;
          hyphen_count := 0
    ) tokens;
    List.rev !issues
}

(** Rule: Spacing around dashes *)
let dash_spacing_rule = {
  id = "DASH-002";
  name = "dash_spacing";
  description = "Check spacing around dashes";
  severity = Info;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 45 ->
          (* Check for -- (en-dash) *)
          if i < Array.length tokens - 1 then
            match tokens.(i+1) with
            | TChar (next_uc, _) when Uchar.to_int next_uc = 45 ->
                (* Found en-dash, check spacing *)
                if i > 0 && i < Array.length tokens - 2 then begin
                  let has_space_before = match tokens.(i-1) with
                    | TChar (uc, _) -> Uchar.to_int uc = 32
                    | _ -> false in
                  let has_space_after = match tokens.(i+2) with
                    | TChar (uc, _) -> Uchar.to_int uc = 32
                    | _ -> false in
                  
                  if has_space_before <> has_space_after then
                    issues := {
                      rule_id = "DASH-002";
                      message = "Inconsistent spacing around en-dash";
                      location = loc;
                      suggestion = Some "Use consistent spacing (both or neither)";
                      confidence = 0.8;
                    } :: !issues
                end
            | _ -> ()
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Unicode dashes *)
let unicode_dash_rule = {
  id = "DASH-003";
  name = "unicode_dashes";
  description = "Handle Unicode dash characters";
  severity = Info;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, loc) ->
          let code = Uchar.to_int uc in
          if code = 0x2013 then (* en-dash *)
            issues := {
              rule_id = "DASH-003";
              message = "Unicode en-dash found";
              location = loc;
              suggestion = Some "Consider using -- for consistency";
              confidence = 0.5;
            } :: !issues
          else if code = 0x2014 then (* em-dash *)
            issues := {
              rule_id = "DASH-003";
              message = "Unicode em-dash found";
              location = loc;
              suggestion = Some "Consider using --- for consistency";
              confidence = 0.5;
            } :: !issues
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Minus sign in math *)
let minus_sign_rule = {
  id = "DASH-004";
  name = "minus_sign";
  description = "Use proper minus in math mode";
  severity = Warning;
  category = "punctuation";
  check = fun tokens ->
    let issues = ref [] in
    let in_math = ref false in
    
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, _) when Uchar.to_int uc = Char.code '$' ->
          in_math := not !in_math
      | TChar (uc, loc) when Uchar.to_int uc = 45 && !in_math ->
          (* Hyphen in math mode - check if it's a minus *)
          let likely_minus = 
            if i > 0 then
              match tokens.(i-1) with
              | TChar (prev_uc, _) ->
                  let prev = Uchar.to_int prev_uc in
                  prev = 32 || prev = 61 (* space or = *)
              | _ -> false
            else false in
          
          if likely_minus then
            issues := {
              rule_id = "DASH-004";
              message = "Hyphen used as minus in math";
              location = loc;
              suggestion = Some "Already correct (- is minus in math mode)";
              confidence = 0.3;
            } :: !issues
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Collect all punctuation rules *)
let all_rules = [
  (* Ellipsis rules *)
  ellipsis_dots_rule;
  ellipsis_context_rule;
  unicode_ellipsis_rule;
  (* Dash rules *)
  dash_types_rule;
  dash_spacing_rule;
  unicode_dash_rule;
  minus_sign_rule;
]

(** Get rule by ID *)
let get_rule id =
  List.find_opt (fun r -> r.id = id) all_rules

(** Run all punctuation validators *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    issues @ acc
  ) [] all_rules