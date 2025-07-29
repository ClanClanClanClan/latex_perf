(** Example Validator Patterns
    
    This module demonstrates the Validator Pattern DSL with concrete examples
    from each major family. These serve as templates for automated generation.
*)

open Validator_patterns
open PatternBuilder

(** MATH Family - Mathematics notation validators *)
module MathValidators = struct
  
  (** MATH-001: Detect unmatched math delimiters *)
  let unmatched_math_delimiters = make_pattern
    ~family:"MATH"
    ~id_prefix:"MATH-001"
    ~name:"Unmatched Math Delimiters"
    ~description:"Detects opening $ without closing $ or vice versa"
    ~matcher:(regex "\\$[^$]*$")  (* Opening $ without closing *)
    ~severity:Critical
    ~fix_generator:(simple_fix "$incomplete" "$complete$")
    ~proof_template:[Auto; Apply "math_delimiter_balance"]
    ~test_cases:[
      ("$x = 1", false);  (* Valid *)
      ("$x = 1$", true);  (* Valid *)
      ("$x = ", false);   (* Invalid - should match *)
      ("x = 1$", false);  (* Invalid - should match *)
    ]
    ~tags:["math"; "delimiters"; "syntax"]
    ~priority:9
    ()
  
  (** MATH-002: Prefer \cdot over * in math mode *)
  let prefer_cdot = make_pattern
    ~family:"MATH"
    ~id_prefix:"MATH-002"
    ~name:"Prefer \\cdot over *"
    ~description:"Suggests using \\cdot instead of * for multiplication in math mode"
    ~matcher:(with_context 
      (token_sequence [TMathShift; TText "*"; TMathShift])
      ~required:[TMathShift]
      ~forbidden:[])
    ~severity:Suggestion
    ~fix_generator:(simple_fix "*" "\\cdot")
    ~proof_template:[Auto]
    ~test_cases:[
      ("$a * b$", true);   (* Should match *)
      ("$a \\cdot b$", false); (* Should not match *)
      ("a * b", false);    (* Outside math - should not match *)
    ]
    ~tags:["math"; "style"; "typography"]
    ~priority:3
    ()
  
  (** MATH-003: Detect deprecated commands *)
  let deprecated_math_commands = make_pattern
    ~family:"MATH"
    ~id_prefix:"MATH-003"
    ~name:"Deprecated Math Commands"
    ~description:"Detects use of deprecated math commands like \\over"
    ~matcher:(token_sequence [TCommand "over"])
    ~severity:Warning
    ~fix_generator:(template_fix "{$1 \\over $2}" [("replacement", "\\frac{$1}{$2}")])
    ~proof_template:[Rewrite ["deprecated_commands"]; Auto]
    ~test_cases:[
      ("$a \\over b$", true);
      ("$\\frac{a}{b}$", false);
    ]
    ~tags:["math"; "deprecated"; "modernization"]
    ~priority:6
    ()
  
  let all_patterns = [
    unmatched_math_delimiters;
    prefer_cdot;
    deprecated_math_commands;
  ]
end

(** TYPO Family - Typography and spelling validators *)
module TypoValidators = struct
  
  (** TYPO-001: Common LaTeX command typos *)
  let common_command_typos = make_pattern
    ~family:"TYPO"
    ~id_prefix:"TYPO-001"
    ~name:"Common Command Typos"
    ~description:"Detects common misspellings of LaTeX commands"
    ~matcher:(regex "\\\\(documetnclass|begn|ned|LaTexT)")
    ~severity:Critical
    ~fix_generator:(template_fix "typo_map" [
      ("documetnclass", "documentclass");
      ("begn", "begin");
      ("ned", "end");
      ("LaTexT", "LaTeX");
    ])
    ~proof_template:[Cases "typo_pattern"; Auto]
    ~test_cases:[
      ("\\documetnclass{article}", true);
      ("\\documentclass{article}", false);
      ("\\begn{document}", true);
      ("\\begin{document}", false);
    ]
    ~tags:["typo"; "commands"; "spelling"]
    ~priority:8
    ()
  
  (** TYPO-002: Missing space after periods *)
  let missing_space_after_period = make_pattern
    ~family:"TYPO"
    ~id_prefix:"TYPO-002"
    ~name:"Missing Space After Period"
    ~description:"Detects missing space after sentence-ending periods"
    ~matcher:(regex "\\.[A-Z]")  (* Period followed immediately by capital *)
    ~severity:Warning
    ~fix_generator:(simple_fix ".([A-Z])" ". $1")
    ~proof_template:[Auto]
    ~test_cases:[
      ("This is good. This too.", false);
      ("This is bad.This too.", true);
      ("Mr.Smith", false);  (* Not sentence-ending *)
    ]
    ~tags:["typo"; "spacing"; "punctuation"]
    ~priority:4
    ()
  
  let all_patterns = [
    common_command_typos;
    missing_space_after_period;
  ]
end

(** STYLE Family - Style and formatting validators *)
module StyleValidators = struct
  
  (** STYLE-001: prefer semantic markup *)
  let prefer_semantic_markup = make_pattern
    ~family:"STYLE"
    ~id_prefix:"STYLE-001"
    ~name:"Prefer Semantic Markup"
    ~description:"Suggests semantic commands over formatting commands"
    ~matcher:(token_sequence [TCommand "textit"; TBeginGroup; TText "emphasis"; TEndGroup])
    ~severity:Suggestion
    ~fix_generator:(simple_fix "\\textit{emphasis}" "\\emph{emphasis}")
    ~proof_template:[Auto]
    ~test_cases:[
      ("\\textit{important}", true);
      ("\\emph{important}", false);
    ]
    ~tags:["style"; "semantic"; "accessibility"]
    ~priority:2
    ()
  
  (** STYLE-002: Consistent quote usage *)
  let consistent_quotes = make_pattern
    ~family:"STYLE" 
    ~id_prefix:"STYLE-002"
    ~name:"Consistent Quote Usage"
    ~description:"Enforces LaTeX quote conventions (`text' not \"text\")"
    ~matcher:(regex "\"([^\"]+)\"")
    ~severity:Warning
    ~fix_generator:(simple_fix "\"([^\"]+)\"" "`$1'")
    ~proof_template:[Auto]
    ~test_cases:[
      ("\"quoted text\"", true);
      ("`quoted text'", false);
      ("``quoted text''", false);
    ]
    ~tags:["style"; "typography"; "quotes"]
    ~priority:5
    ()
  
  let all_patterns = [
    prefer_semantic_markup;
    consistent_quotes;
  ]
end

(** DELIM Family - Delimiter and grouping validators *)
module DelimValidators = struct
  
  (** DELIM-001: Unmatched braces *)
  let unmatched_braces = make_pattern
    ~family:"DELIM"
    ~id_prefix:"DELIM-001"
    ~name:"Unmatched Braces"
    ~description:"Detects unmatched { } braces"
    ~matcher:(CompositePattern {
      primary = token_sequence [TBeginGroup];
      secondary = [token_sequence [TEndGroup]];
      logic = `And;
    })
    ~severity:Critical
    ~fix_generator:NoFix  (* Complex fix, needs manual intervention *)
    ~proof_template:[Induction "brace_balance"; Auto]
    ~test_cases:[
      ("{matched}", false);
      ("{unmatched", true);
      ("unmatched}", true);
    ]
    ~tags:["delim"; "braces"; "syntax"]
    ~priority:10
    ()
  
  (** DELIM-002: Mismatched parentheses **)
  let mismatched_parentheses = make_pattern
    ~family:"DELIM"
    ~id_prefix:"DELIM-002"
    ~name:"Mismatched Parentheses"
    ~description:"Detects unmatched ( ) parentheses in text and math"
    ~matcher:(regex "\\([^)]*$|[^(]*\\)")  (* Opening ( without closing ) or vice versa *)
    ~severity:Critical
    ~fix_generator:NoFix
    ~proof_template:[Induction "paren_balance"; Auto]
    ~test_cases:[
      ("(matched)", false);
      ("(unmatched", true);
      ("unmatched)", true);
    ]
    ~tags:["delim"; "parentheses"; "syntax"]
    ~priority:9
    ()
  
  (** DELIM-003: Mismatched square brackets **)
  let mismatched_brackets = make_pattern
    ~family:"DELIM"
    ~id_prefix:"DELIM-003" 
    ~name:"Mismatched Square Brackets"
    ~description:"Detects unmatched [ ] square brackets"
    ~matcher:(regex "\\[[^\\]]*$|[^\\[]*\\]")
    ~severity:Critical
    ~fix_generator:NoFix
    ~proof_template:[Induction "bracket_balance"; Auto]
    ~test_cases:[
      ("[matched]", false);
      ("[unmatched", true);
      ("unmatched]", true);
    ]
    ~tags:["delim"; "brackets"; "syntax"]
    ~priority:9
    ()

  let all_patterns = [
    unmatched_braces;
    mismatched_parentheses;
    mismatched_brackets;
  ]
end

(** Pattern families collection *)
let all_families = [
  {
    name = "MATH";
    description = "Mathematics notation and formula validation";
    patterns = MathValidators.all_patterns;
    common_proof_tactics = [Apply "math_wellformed"; Auto];
  };
  {
    name = "TYPO";
    description = "Typography and spelling error detection";
    patterns = TypoValidators.all_patterns;
    common_proof_tactics = [Cases "typo_categories"; Auto];
  };
  {
    name = "STYLE";
    description = "Style and formatting consistency";
    patterns = StyleValidators.all_patterns;
    common_proof_tactics = [Auto];
  };
  {
    name = "DELIM";
    description = "Delimiter matching and grouping";
    patterns = DelimValidators.all_patterns;
    common_proof_tactics = [Induction "delimiter_structure"; Auto];
  };
]

(** Get all patterns across all families *)
let all_patterns = 
  let extract_patterns (family : Validator_patterns.pattern_family) = family.patterns in
  List.flatten (List.map extract_patterns all_families)

(** Family lookup *)
let get_family name = 
  List.find_opt (fun f -> f.name = name) all_families

(** Pattern statistics *)
let pattern_stats () = {|
Validator Pattern Examples Statistics:
=====================================
Total Families: |} ^ (string_of_int (List.length all_families)) ^ {|
Total Patterns: |} ^ (string_of_int (List.length all_patterns)) ^ {|

By Family:
|} ^ (String.concat "\n" (List.map (fun f -> 
  Printf.sprintf "  %s: %d patterns" f.name (List.length f.patterns)
) all_families)) ^ {|

By Severity:
|} ^ (
  let count_severity sev = 
    List.length (List.filter (fun p -> p.severity = sev) all_patterns)
  in
  Printf.sprintf "  Critical: %d\n  Warning: %d\n  Suggestion: %d\n  Info: %d"
    (count_severity Critical)
    (count_severity Warning) 
    (count_severity Suggestion)
    (count_severity Info)
) ^ {|
|}

(** Test all pattern examples *)
let test_all_patterns () =
  Printf.printf "Testing all validator pattern examples...\n\n";
  
  let total_tests = ref 0 in
  let passed_tests = ref 0 in
  
  List.iter (fun family ->
    Printf.printf "=== %s Family ===\n" family.name;
    
    List.iter (fun (pattern : Validator_patterns.validator_pattern) ->
      Printf.printf "Testing %s: " pattern.name;
      
      let pattern_passed = ref true in
      List.iter (fun (test_input, should_match) ->
        incr total_tests;
        (* Simplified test - in real implementation would use compiled detector *)
        let matches = match pattern.matcher with
          | Validator_patterns.TokenSequence _ -> String.length test_input > 0  (* Placeholder *)
          | Validator_patterns.TokenRegex _ -> String.length test_input > 0     (* Placeholder *)
          | _ -> false
        in
        if matches = should_match then
          incr passed_tests
        else
          pattern_passed := false
      ) pattern.test_cases;
      
      if !pattern_passed then
        Printf.printf "✅ PASS\n"
      else
        Printf.printf "❌ FAIL\n"
        
    ) family.patterns;
    
    Printf.printf "\n"
  ) all_families;
  
  Printf.printf "=== Test Summary ===\n";
  Printf.printf "Total tests: %d\n" !total_tests;
  Printf.printf "Passed: %d\n" !passed_tests;
  Printf.printf "Failed: %d\n" (!total_tests - !passed_tests);
  
  if !passed_tests = !total_tests then
    Printf.printf "✅ All pattern examples valid!\n"
  else
    Printf.printf "❌ Some pattern examples need fixes\n"