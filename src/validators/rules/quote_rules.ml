(* Quote Consistency Rules - LaTeX Perfectionist v25 *)
(* Week 2 Sprint: Quote validation for consistency *)

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

(* Track quote state *)
type quote_state = {
  mutable open_single: int;
  mutable open_double: int;
  mutable last_quote_pos: int;
}

(** Rule: Balanced quote pairs *)
let balanced_quotes_rule = {
  id = "QUOTE-001";
  name = "balanced_quotes";
  description = "Ensure quotes are properly balanced";
  severity = Error;
  category = "quotes";
  check = fun tokens ->
    let issues = ref [] in
    let state = { open_single = 0; open_double = 0; last_quote_pos = -1 } in
    
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) ->
          let code = Uchar.to_int uc in
          (* Check for ` (backtick) *)
          if code = 96 then begin
            (* Look ahead for double backtick *)
            if i < Array.length tokens - 1 then
              match tokens.(i+1) with
              | TChar (next_uc, _) when Uchar.to_int next_uc = 96 ->
                  state.open_double <- state.open_double + 1;
                  state.last_quote_pos <- i
              | _ ->
                  state.open_single <- state.open_single + 1;
                  state.last_quote_pos <- i
          end
          (* Check for ' (apostrophe/single quote) *)
          else if code = 39 then begin
            if i < Array.length tokens - 1 then
              match tokens.(i+1) with
              | TChar (next_uc, _) when Uchar.to_int next_uc = 39 ->
                  (* Double closing quote *)
                  if state.open_double > 0 then
                    state.open_double <- state.open_double - 1
                  else
                    issues := {
                      rule_id = "QUOTE-001";
                      message = "Unmatched closing double quote ''";
                      location = loc;
                      suggestion = Some "Add opening quote `` before this";
                      confidence = 0.9;
                    } :: !issues
              | _ ->
                  (* Single closing quote *)
                  if state.open_single > 0 then
                    state.open_single <- state.open_single - 1
                  else
                    issues := {
                      rule_id = "QUOTE-001";
                      message = "Unmatched closing single quote '";
                      location = loc;
                      suggestion = Some "Add opening quote ` before this";
                      confidence = 0.85;
                    } :: !issues
          end
      | _ -> ()
    ) tokens;
    
    (* Check for unclosed quotes at end *)
    if state.open_single > 0 then
      issues := {
        rule_id = "QUOTE-001";
        message = Printf.sprintf "%d unclosed single quote(s)" state.open_single;
        location = Location.dummy;
        suggestion = Some "Add closing quote(s) '";
        confidence = 0.9;
      } :: !issues;
      
    if state.open_double > 0 then
      issues := {
        rule_id = "QUOTE-001";
        message = Printf.sprintf "%d unclosed double quote(s)" state.open_double;
        location = Location.dummy;
        suggestion = Some "Add closing quote(s) ''";
        confidence = 0.9;
      } :: !issues;
    
    List.rev !issues
}

(** Rule: Avoid straight quotes *)
let no_straight_quotes_rule = {
  id = "QUOTE-002";
  name = "no_straight_quotes";
  description = "Use LaTeX quotes (`') instead of straight quotes (\")";
  severity = Warning;
  category = "quotes";
  check = fun tokens ->
    let issues = ref [] in
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 34 -> (* " *)
          issues := {
            rule_id = "QUOTE-002";
            message = "Straight quote \" found";
            location = loc;
            suggestion = Some "Use `` for opening or '' for closing";
            confidence = 0.95;
          } :: !issues
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Smart quote commands *)
let quote_command_rule = {
  id = "QUOTE-003";
  name = "quote_commands";
  description = "Prefer \\enquote{} for nested quotes";
  severity = Info;
  category = "quotes";
  check = fun tokens ->
    let issues = ref [] in
    let nested_level = ref 0 in
    
    Array.iteri (fun i tok ->
      match tok with
      | TChar (uc, loc) when Uchar.to_int uc = 96 ->
          (* Check for `` *)
          if i < Array.length tokens - 1 then
            match tokens.(i+1) with
            | TChar (next_uc, _) when Uchar.to_int next_uc = 96 ->
                incr nested_level;
                if !nested_level > 1 then
                  issues := {
                    rule_id = "QUOTE-003";
                    message = "Nested quotes detected";
                    location = loc;
                    suggestion = Some "Consider \\enquote{} for automatic nesting";
                    confidence = 0.7;
                  } :: !issues
            | _ -> ()
      | TChar (uc, _) when Uchar.to_int uc = 39 ->
          (* Check for '' *)
          if i < Array.length tokens - 1 then
            match tokens.(i+1) with
            | TChar (next_uc, _) when Uchar.to_int next_uc = 39 ->
                if !nested_level > 0 then
                  decr nested_level
            | _ -> ()
      | _ -> ()
    ) tokens;
    List.rev !issues
}

(** Rule: Language-specific quotes *)
let language_quotes_rule = {
  id = "QUOTE-004";
  name = "language_quotes";
  description = "Use language-appropriate quote styles";
  severity = Info;
  category = "quotes";
  check = fun tokens ->
    let issues = ref [] in
    let found_babel = ref false in
    let found_german = ref false in
    let found_french = ref false in
    
    (* Check for babel/polyglossia *)
    Array.iter (fun tok ->
      match tok with
      | TCmd ((_, name), _) when name = "usepackage" -> found_babel := true
      | TCmd ((_, name), _) when name = "selectlanguage" -> found_babel := true
      | TChar (uc, _) ->
          let code = Uchar.to_int uc in
          (* Check for German quotes „" */
          if code = 0x201E || code = 0x201C then found_german := true;
          (* Check for French quotes «» *)
          if code = 0xAB || code = 0xBB then found_french := true
      | _ -> ()
    ) tokens;
    
    if found_german && not found_babel then
      issues := {
        rule_id = "QUOTE-004";
        message = "German quotes found without babel";
        location = Location.dummy;
        suggestion = Some "Add \\usepackage[german]{babel}";
        confidence = 0.8;
      } :: !issues;
      
    if found_french && not found_babel then
      issues := {
        rule_id = "QUOTE-004";
        message = "French quotes found without babel";
        location = Location.dummy;
        suggestion = Some "Add \\usepackage[french]{babel}";
        confidence = 0.8;
      } :: !issues;
    
    List.rev !issues
}

(** Rule: Consistent quote style *)
let consistent_style_rule = {
  id = "QUOTE-005";
  name = "consistent_quotes";
  description = "Maintain consistent quote style throughout document";
  severity = Warning;
  category = "quotes";
  check = fun tokens ->
    let issues = ref [] in
    let latex_quotes = ref 0 in
    let unicode_quotes = ref 0 in
    let straight_quotes = ref 0 in
    
    Array.iter (fun tok ->
      match tok with
      | TChar (uc, loc) ->
          let code = Uchar.to_int uc in
          if code = 96 || code = 39 then incr latex_quotes
          else if code = 34 then incr straight_quotes
          else if code >= 0x2018 && code <= 0x201F then incr unicode_quotes
      | _ -> ()
    ) tokens;
    
    let styles_used = 
      (if !latex_quotes > 0 then 1 else 0) +
      (if !unicode_quotes > 0 then 1 else 0) +
      (if !straight_quotes > 0 then 1 else 0) in
    
    if styles_used > 1 then
      issues := {
        rule_id = "QUOTE-005";
        message = Printf.sprintf "Mixed quote styles: LaTeX=%d, Unicode=%d, Straight=%d" 
          !latex_quotes !unicode_quotes !straight_quotes;
        location = Location.dummy;
        suggestion = Some "Use consistent quote style throughout";
        confidence = 0.85;
      } :: !issues;
    
    List.rev !issues
}

(** Collect all quote rules *)
let all_rules = [
  balanced_quotes_rule;
  no_straight_quotes_rule;
  quote_command_rule;
  language_quotes_rule;
  consistent_style_rule;
]

(** Get rule by ID *)
let get_rule id =
  List.find_opt (fun r -> r.id = id) all_rules

(** Run all quote validators *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    issues @ acc
  ) [] all_rules