(* Simple CARC test to demonstrate classification *)
open Ast

let create_test_rules () = [
  {
    id = "TEST-001";
    description = "Missing backslash before command";
    precondition = L0_Lexer;
    default_severity = Error;
    maturity = Stable;
    owner = "@test";
    fix = None;
    classification = None;
    confidence = None;
    pattern_analysis = [];
  };
  {
    id = "TEST-002";
    description = "Unmatched begin environment";
    precondition = L2_Ast;
    default_severity = Error;
    maturity = Stable;
    owner = "@test";
    fix = None;
    classification = None;
    confidence = None;
    pattern_analysis = [];
  };
  {
    id = "TEST-003";
    description = "Undefined reference to label";
    precondition = L3_Semantics;
    default_severity = Warning;
    maturity = Draft;
    owner = "@test";
    fix = None;
    classification = None;
    confidence = None;
    pattern_analysis = [];
  };
]

let () =
  Printf.printf "CARC Simple Test - Demonstrating Classification\n";
  Printf.printf "===============================================\n\n";
  
  let rules = create_test_rules () in
  Printf.printf "Created %d test rules\n\n" (List.length rules);
  
  let classifications = Classify.classify_rules rules in
  let report = Classify.generate_report classifications in
  
  Printf.printf "Classification Results:\n";
  List.iter (fun c ->
    Printf.printf "  %s: %s (confidence: %.2f) - %s\n" 
      c.rule_id 
      (match c.classification with REG -> "REG" | VPL -> "VPL" | CST -> "CST")
      c.confidence
      c.reasoning
  ) classifications;
  
  Printf.printf "\nStatistics:\n";
  Printf.printf "  REG: %d, VPL: %d, CST: %d\n" 
    report.reg_count 
    report.vpl_count 
    report.cst_count;
  Printf.printf "  Average confidence: %.3f\n" report.avg_confidence;