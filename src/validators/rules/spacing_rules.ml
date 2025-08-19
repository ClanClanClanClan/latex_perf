(* Spacing Validation Rules - LaTeX Perfectionist v25 *)
(* Week 2 Sprint: Adding critical spacing validators *)

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

(* Helper functions *)
let is_command cmd tok = match tok with
  | TCmd ((_, name), _) -> name = cmd
  | _ -> false

let is_text tok = match tok with
  | TChar _ -> true
  | _ -> false

(** Rule: Detect multiple consecutive spaces *)
let multiple_spaces_rule = {
  id = "SPACE-001";
  name = "multiple_spaces";
  description = "Avoid multiple consecutive spaces in text";
  severity = Warning;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    let consecutive_spaces = ref 0 in
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 32 -> (* space *)
          incr consecutive_spaces;
          if !consecutive_spaces > 1 then
            issues := {
              rule_id = "SPACE-001";
              message = Printf.sprintf "Found %d consecutive spaces" !consecutive_spaces;
              location = loc;
              suggestion = Some "Use single space or ~ for non-breaking space";
              confidence = 0.95;
            } :: !issues
      | _ -> consecutive_spaces := 0
    ) tokens;
    List.rev !issues
}

(** Rule: Use proper spacing commands instead of manual spacing *)
let manual_spacing_rule = {
  id = "SPACE-002";
  name = "manual_spacing";
  description = "Use LaTeX spacing commands instead of manual spaces";
  severity = Info;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    let space_count = ref 0 in
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 32 ->
          incr space_count;
          if !space_count >= 3 then begin
            issues := {
              rule_id = "SPACE-002";
              message = "Consider using \\quad, \\qquad, or \\hspace";
              location = loc;
              suggestion = Some "Replace multiple spaces with \\quad or \\qquad";
              confidence = 0.7;
            } :: !issues;
            space_count := 0
          end
      | _ -> space_count := 0
    ) tokens;
    List.rev !issues
}

(** Rule: Ensure proper spacing around math delimiters *)
let math_spacing_rule = {
  id = "SPACE-003";
  name = "math_delimiter_spacing";
  description = "Check spacing around $ delimiters";
  severity = Warning;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = Char.code '$' ->
          (* Check for missing space before $ *)
          if i > 0 then begin
            match tokens.(i-1) with
            | TChar (prev_uc, _) ->
                let prev_code = Uchar.to_int prev_uc in
                if prev_code <> 32 && prev_code <> 10 then (* not space or newline *)
                  issues := {
                    rule_id = "SPACE-003";
                    message = "Missing space before math delimiter $";
                    location = loc;
                    suggestion = Some "Add space before $";
                    confidence = 0.8;
                  } :: !issues
            | _ -> ()
          end;
          (* Check for missing space after $ *)
          if i < Array.length tokens - 1 then begin
            match tokens.(i+1) with
            | TChar (next_uc, _) ->
                let next_code = Uchar.to_int next_uc in
                if next_code = Char.code '$' then
                  () (* $$ is valid *)
                else if next_code <> 32 && next_code <> 10 then
                  issues := {
                    rule_id = "SPACE-003";
                    message = "Missing space after math delimiter $";
                    location = loc;
                    suggestion = Some "Add space after $";
                    confidence = 0.8;
                  } :: !issues
            | _ -> ()
          end
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Non-breaking space before references *)
let nbspace_before_ref = {
  id = "SPACE-004";
  name = "nbspace_references";
  description = "Use non-breaking space (~) before \\ref and \\cite";
  severity = Warning;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    Array.iteri (fun i tok ->
      match tok with
      | TCmd ((_, name), loc) when name = "ref" || name = "cite" ->
          if i > 0 then begin
            match tokens.(i-1) with
            | TChar (uc, _) when Uchar.to_int uc = 32 ->
                issues := {
                  rule_id = "SPACE-004";
                  message = Printf.sprintf "Use ~ before \\%s for non-breaking space" name;
                  location = loc;
                  suggestion = Some (Printf.sprintf "Replace space with ~ before \\%s" name);
                  confidence = 0.9;
                } :: !issues
            | _ -> ()
          end
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Check for tabs in source *)
let no_tabs_rule = {
  id = "SPACE-005";
  name = "no_tabs";
  description = "Avoid tab characters in LaTeX source";
  severity = Info;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 9 -> (* tab *)
          issues := {
            rule_id = "SPACE-005";
            message = "Tab character found";
            location = loc;
            suggestion = Some "Replace tabs with spaces";
            confidence = 1.0;
          } :: !issues
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Thin space in numbers *)
let number_spacing_rule = {
  id = "SPACE-006";
  name = "number_spacing";
  description = "Use thin space (\\,) for thousands separator";
  severity = Info;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    let digit_count = ref 0 in
    let number_start = ref (-1) in
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) ->
          let code = Uchar.to_int uc in
          if code >= 48 && code <= 57 then begin (* digit *)
            if !digit_count = 0 then number_start := i;
            incr digit_count
          end else begin
            if !digit_count >= 5 then (* 5+ digits *)
              issues := {
                rule_id = "SPACE-006";
                message = Printf.sprintf "Large number (%d digits) needs thousands separator" !digit_count;
                location = loc;
                suggestion = Some "Use \\, for thin space: 10\\,000";
                confidence = 0.6;
              } :: !issues;
            digit_count := 0
          end
      | _ -> digit_count := 0
    ) tokens;
    List.rev !issues
}

(** Rule: Check spacing around punctuation *)
let punctuation_spacing_rule = {
  id = "SPACE-007";
  name = "punctuation_spacing";
  description = "Ensure proper spacing around punctuation";
  severity = Warning;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) ->
          let code = Uchar.to_int uc in
          (* Check for space before period, comma, semicolon *)
          if (code = 46 || code = 44 || code = 59) && i > 0 then begin
            match tokens.(i-1) with
            | TChar (prev_uc, _) when Uchar.to_int prev_uc = 32 ->
                issues := {
                  rule_id = "SPACE-007";
                  message = "Unnecessary space before punctuation";
                  location = loc;
                  suggestion = Some "Remove space before punctuation";
                  confidence = 0.95;
                } :: !issues
            | _ -> ()
          end;
          (* Check for missing space after period *)
          if code = 46 && i < Array.length tokens - 1 then begin
            match tokens.(i+1) with
            | TChar (next_uc, _) ->
                let next_code = Uchar.to_int next_uc in
                if next_code >= 65 && next_code <= 90 then (* uppercase letter *)
                  issues := {
                    rule_id = "SPACE-007";
                    message = "Missing space after period";
                    location = loc;
                    suggestion = Some "Add space after period";
                    confidence = 0.9;
                  } :: !issues
            | _ -> ()
          end
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Check for trailing spaces *)
let trailing_space_rule = {
  id = "SPACE-008";
  name = "trailing_spaces";
  description = "Remove trailing spaces at end of lines";
  severity = Info;
  category = "spacing";
  check = fun tokens ->
    let issues = ref [] in
    let last_was_space = ref false in
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, loc) ->
          let code = Uchar.to_int uc in
          if code = 32 then
            last_was_space := true
          else if code = 10 && !last_was_space then begin (* newline after space *)
            issues := {
              rule_id = "SPACE-008";
              message = "Trailing space at end of line";
              location = loc;
              suggestion = Some "Remove trailing whitespace";
              confidence = 1.0;
            } :: !issues;
            last_was_space := false
          end else
            last_was_space := false
      | _ -> last_was_space := false
    ) tokens;
    List.rev !issues
}

(** Collect all spacing rules *)
let all_rules = [
  multiple_spaces_rule;
  manual_spacing_rule;
  math_spacing_rule;
  nbspace_before_ref;
  no_tabs_rule;
  number_spacing_rule;
  punctuation_spacing_rule;
  trailing_space_rule;
]

(** Get rule by ID *)
let get_rule id =
  List.find_opt (fun r -> r.id = id) all_rules

(** Run all spacing validators *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    issues @ acc
  ) [] all_rules