(* Validation Rules Registry - LaTeX Perfectionist v25 *)
(* Central registry for all validation rules *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

(* Import all rule modules *)
module Typography = Typography_rules
module DocumentStructure = Document_structure_rules  
module MathNotation = Math_notation_rules
module Language = Language_rules
module Bibliography = Bibliography_rules
module FigureTable = Figure_table_rules
module CodeVerbatim = Code_verbatim_rules
module Accessibility = Accessibility_rules
module PageLayout = Page_layout_rules
module FontTypography = Font_typography_rules

type validation_summary = {
  total_rules: int;
  rules_by_category: (string * int) list;
  rules_by_severity: (string * int) list;
}

(** Collect all validation rules from all modules *)
let all_validation_rules = [
  (* Typography rules - 10 rules *)
  Typography.all_rules;
  
  (* Document structure rules - 10 rules *)
  DocumentStructure.all_rules;
  
  (* Math notation rules - 7 rules *)
  MathNotation.all_rules;
  
  (* Language and localization rules - 7 rules *)
  Language.all_rules;
  
  (* Bibliography and citation rules - 11 rules *)
  Bibliography.all_rules;
  
  (* Figure and table rules - 12 rules *)
  FigureTable.all_rules;
  
  (* Code and verbatim rules - 13 rules *)
  CodeVerbatim.all_rules;
  
  (* Accessibility and semantic rules - 15 rules *)
  Accessibility.all_rules;
  
  (* Page layout rules - 20 rules *)
  PageLayout.all_rules;
  
  (* Font and typography enhancement rules - 5 rules *)
  FontTypography.all_rules;
] |> List.flatten

(** Get total rule count *)
let total_rule_count () = List.length all_validation_rules

(** Get rules by category *)
let rules_by_category category = 
  List.filter (fun rule -> rule.category = category) all_validation_rules

(** Get all categories *)
let all_categories () =
  all_validation_rules
  |> List.map (fun rule -> rule.category)
  |> List.sort_uniq String.compare

(** Get rules by severity *)
let rules_by_severity severity =
  List.filter (fun rule -> rule.severity = severity) all_validation_rules

(** Generate validation summary *)
let generate_summary () =
  let categories = all_categories () in
  let category_counts = List.map (fun cat -> 
    (cat, List.length (rules_by_category cat))
  ) categories in
  
  let severities = ["Error"; "Warning"; "Info"] in
  let severity_map = [
    ("Error", Typography_rules.Error);
    ("Warning", Typography_rules.Warning); 
    ("Info", Typography_rules.Info);
  ] in
  let severity_counts = List.map (fun (sev_name, sev_val) ->
    (sev_name, List.length (rules_by_severity sev_val))
  ) severity_map in
  
  {
    total_rules = total_rule_count ();
    rules_by_category = category_counts;
    rules_by_severity = severity_counts;
  }

(** Run validation using all rules *)
let validate_document tokens =
  let all_results = List.map (fun rule ->
    let issues = rule.check tokens in
    List.map (fun issue -> (rule, issue)) issues
  ) all_validation_rules in
  List.flatten all_results

(** Get detailed rule information *)
let rule_details rule_id =
  List.find_opt (fun rule -> rule.id = rule_id) all_validation_rules

(** Print validation summary *)
let print_summary () =
  let summary = generate_summary () in
  Printf.printf "📊 VALIDATION RULES SUMMARY\n";
  Printf.printf "===========================\n\n";
  
  Printf.printf "🎯 TOTAL RULES: %d / 623 target (%.1f%% complete)\n\n"
    summary.total_rules
    (float summary.total_rules /. 623.0 *. 100.0);
  
  Printf.printf "📋 BY CATEGORY:\n";
  Printf.printf "---------------\n";
  List.iter (fun (category, count) ->
    Printf.printf "  %-15s: %2d rules\n" category count
  ) summary.rules_by_category;
  
  Printf.printf "\n⚠️  BY SEVERITY:\n";
  Printf.printf "----------------\n";
  List.iter (fun (severity, count) ->
    let icon = match severity with
      | "Error" -> "🔴"
      | "Warning" -> "🟡"
      | "Info" -> "🔵"
      | _ -> "⭕"
    in
    Printf.printf "  %s %-7s: %2d rules\n" icon severity count
  ) summary.rules_by_severity;
  
  Printf.printf "\n📈 PROGRESS:\n";
  Printf.printf "------------\n";
  Printf.printf "  Target:    623 rules\n";
  Printf.printf "  Current:   %d rules\n" summary.total_rules;
  Printf.printf "  Remaining: %d rules\n" (623 - summary.total_rules);
  Printf.printf "  Progress:  %.1f%%\n" (float summary.total_rules /. 623.0 *. 100.0);
  
  Printf.printf "\n🎯 WEEK 3 TARGETS:\n";
  Printf.printf "------------------\n";
  Printf.printf "  Week 2 End:  %d rules ✅\n" summary.total_rules;
  Printf.printf "  Week 3 Goal: 110+ rules\n";
  Printf.printf "  Needed:      %d more rules\n" (max 0 (110 - summary.total_rules))

(** Module breakdown for progress tracking *)
let module_breakdown () = [
  ("Typography", Typography.rule_count ());
  ("DocumentStructure", DocumentStructure.rule_count ());
  ("MathNotation", MathNotation.rule_count ());
  ("Language", Language.rule_count ());
  ("Bibliography", Bibliography.rule_count ());
  ("FigureTable", FigureTable.rule_count ());
  ("CodeVerbatim", CodeVerbatim.rule_count ());
  ("Accessibility", Accessibility.rule_count ());
  ("PageLayout", PageLayout.rule_count ());
  ("FontTypography", FontTypography.rule_count ());
]