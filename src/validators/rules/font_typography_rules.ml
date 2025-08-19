(* Font and Typography Enhancement Rules - LaTeX Perfectionist v25 *)
(* Additional rules for proper font usage and advanced typography *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

type validation_issue = {
  rule_id: string;
  message: string;
  location: Location.t;
  suggestion: string option;
  confidence: float;
}

type rule_severity = Info | Warning | Error

type validation_rule = {
  id: string;
  name: string;
  description: string;
  severity: rule_severity;
  category: string;
  check: token array -> validation_issue list;
}

(** Font selection and consistency rules **)
module FontSelectionRules = struct
  
  (* Rule: Font family consistency *)
  let font_family_consistency = {
    id = "FONT-001";
    name = "font_family_consistency";
    description = "Use consistent font families";
    severity = Info;
    category = "font";
    check = fun tokens ->
      let font_commands = ["fontfamily"; "rmfamily"; "sffamily"; "ttfamily"] in
      let font_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name font_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if font_count > 3 then
        [{
          rule_id = "FONT-001";
          message = "Multiple font family changes detected";
          location = Location.make 0 0;
          suggestion = Some "Use consistent font families throughout document";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Modern font packages *)
  let modern_font_packages = {
    id = "FONT-002";
    name = "modern_font_packages";
    description = "Consider using modern font packages";
    severity = Info;
    category = "font";
    check = fun tokens ->
      let modern_fonts = ["fontspec"; "lmodern"; "libertine"; "mathpazo"; "fourier"] in
      let has_modern = Array.exists (function
        | TMacro name when List.mem name modern_fonts -> true
        | _ -> false
      ) tokens in
      
      if not has_modern then
        [{
          rule_id = "FONT-002";
          message = "Consider using modern font packages for better typography";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage{lmodern} or similar modern font package";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Math font compatibility *)
  let math_font_compatibility = {
    id = "FONT-003";
    name = "math_font_compatibility";
    description = "Ensure math font compatibility with text font";
    severity = Warning;
    category = "font";
    check = fun tokens ->
      let text_fonts = ["times"; "palatino"; "bookman"; "charter"] in
      let math_fonts = ["mathptmx"; "mathpazo"; "fourier"; "mathdesign"] in
      
      let has_text_font = Array.exists (function
        | TMacro name when List.mem name text_fonts -> true
        | _ -> false
      ) tokens in
      
      let has_math_font = Array.exists (function
        | TMacro name when List.mem name math_fonts -> true
        | _ -> false
      ) tokens in
      
      if has_text_font && not has_math_font then
        [{
          rule_id = "FONT-003";
          message = "Text font without matching math font";
          location = Location.make 0 0;
          suggestion = Some "Add compatible math font package";
          confidence = 0.8;
        }]
      else []
  }
end

(** Typography enhancement rules **)
module TypographyEnhancementRules = struct
  
  (* Rule: Microtype package *)
  let microtype_usage = {
    id = "TYPO-001";
    name = "microtype_usage";
    description = "Use microtype package for better typography";
    severity = Info;
    category = "typography";
    check = fun tokens ->
      let has_microtype = 
        let rec check_microtype i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "microtype", TGroupClose) -> true
            | _ -> check_microtype (i + 1))
          | _ -> check_microtype (i + 1)
        in check_microtype 0 in
      
      if not has_microtype then
        [{
          rule_id = "TYPO-001";
          message = "Consider using microtype package for improved typography";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage{microtype} for micro-adjustments";
          confidence = 0.9;
        }]
      else []
  }
  
  (* Rule: Ligature handling *)
  let ligature_handling = {
    id = "TYPO-002";
    name = "ligature_handling";
    description = "Proper handling of ligatures";
    severity = Info;
    category = "typography";
    check = fun tokens ->
      let problematic_sequences = ["ffi"; "ffl"; "ff"; "fi"; "fl"] in
      let issues = ref [] in
      
      (* This is simplified - real implementation would need better text extraction *)
      Array.iter (function
        | TMacro text -> 
            List.iter (fun seq ->
              if String.contains text (String.get seq 0) then
                issues := {
                  rule_id = "TYPO-002";
                  message = "Check ligature handling in text";
                  location = Location.make 0 0;
                  suggestion = Some "Ensure proper ligature rendering";
                  confidence = 0.4;
                } :: !issues
            ) problematic_sequences
        | _ -> ()
      ) tokens;
      
      List.rev !issues
  }
end

(** Collect all font and typography rules *)
let all_rules = [
  (* Font selection *)
  FontSelectionRules.font_family_consistency;
  FontSelectionRules.modern_font_packages;
  FontSelectionRules.math_font_compatibility;
  
  (* Typography enhancement *)
  TypographyEnhancementRules.microtype_usage;
  TypographyEnhancementRules.ligature_handling;
]

(** Validation functions *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    acc @ List.map (fun issue -> (rule, issue)) issues
  ) [] all_rules

let rule_count () = List.length all_rules

let rules_by_category category =
  List.filter (fun r -> r.category = category) all_rules