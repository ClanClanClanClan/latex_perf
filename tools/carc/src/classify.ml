(* CARC Classification Module - Core Classification Engine *)
(* Following External AI CARC specification: Phase 1-3 classification *)

open Ast

(** * Phase 1: Syntactic Filter (REG Detection) *)
let phase1_regex_only rule =
  let desc_lower = String.lowercase_ascii rule.description in
  let precond_is_lexer = rule.precondition = L0_Lexer in
  
  (* Regex indicators *)
  let has_regex_chars = 
    String.contains desc_lower '\\' ||
    String.contains desc_lower '{' ||
    String.contains desc_lower '}' ||
    String.contains desc_lower '[' ||
    String.contains desc_lower ']'
  in
  
  (* Simple pattern indicators *)
  let simple_patterns = [
    "character"; "char"; "ascii"; "utf"; "encoding";
    "whitespace"; "space"; "tab"; "newline";
    "punctuation"; "digit"; "letter"; "symbol"
  ] in
  
  let has_simple_pattern = 
    List.exists (fun pattern -> 
      Ast.contains_substring desc_lower pattern
    ) simple_patterns
  in
  
  if precond_is_lexer && (has_regex_chars || has_simple_pattern) then
    Some (REG, 0.9, "Lexer-level regex pattern detected")
  else
    None

(** * Phase 2: Balanced-Token Detector (VPL Detection) *)
let phase2_balanced_tokens rule =
  let desc_lower = String.lowercase_ascii rule.description in
  
  (* Balanced construct indicators *)
  let balanced_keywords = [
    "begin"; "end"; "\\begin"; "\\end";
    "open"; "close"; "opening"; "closing"; 
    "pair"; "match"; "matching"; "balanced";
    "brace"; "bracket"; "parenthes";
    "environment"; "group"; "block"
  ] in
  
  let has_balanced = 
    List.exists (fun keyword ->
      Ast.contains_substring desc_lower keyword
    ) balanced_keywords
  in
  
  (* Structural analysis indicators *)
  let structural_keywords = [
    "structure"; "nest"; "nesting"; "hierarchy";
    "level"; "depth"; "stack"; "push"; "pop"
  ] in
  
  let has_structural = 
    List.exists (fun keyword ->
      Ast.contains_substring desc_lower keyword  
    ) structural_keywords
  in
  
  (* AST-level precondition suggests structural pattern *)
  let ast_level = rule.precondition = L2_Ast in
  
  if has_balanced || (ast_level && has_structural) then
    Some (VPL, 0.8, "Balanced construct or structural pattern detected")
  else
    None

(** * Phase 3: Context-Sensitive Detector (CST Detection) *)
let phase3_context_sensitive rule =
  let desc_lower = String.lowercase_ascii rule.description in
  
  (* Cross-reference indicators *)
  let cross_ref_keywords = [
    "ref"; "reference"; "label"; "cite"; "citation";
    "undefined"; "unresolved"; "missing"; "duplicate";
    "cross"; "link"; "pointer"; "target"; "source"
  ] in
  
  let has_cross_ref = 
    List.exists (fun keyword ->
      Ast.contains_substring desc_lower keyword
    ) cross_ref_keywords
  in
  
  (* Semantic analysis indicators *)  
  let semantic_keywords = [
    "semantic"; "meaning"; "definition"; "scope";
    "binding"; "resolution"; "lookup"; "symbol";
    "table"; "environment"; "context"; "global"
  ] in
  
  let has_semantic = 
    List.exists (fun keyword ->
      Ast.contains_substring desc_lower keyword
    ) semantic_keywords
  in
  
  (* High-level preconditions suggest context sensitivity *)
  let high_level = 
    rule.precondition = L3_Semantics || 
    rule.precondition = L4_Style
  in
  
  if has_cross_ref || has_semantic || high_level then
    Some (CST, 0.85, "Context-sensitive or semantic analysis required")
  else
    None

(** * Main Classification Algorithm *)
let classify_single_rule rule =
  (* Apply phases in order of specificity *)
  match phase1_regex_only rule with
  | Some result -> result
  | None -> 
      begin match phase2_balanced_tokens rule with
      | Some result -> result  
      | None ->
          begin match phase3_context_sensitive rule with
          | Some result -> result
          | None -> 
              (* Default fallback - conservative approach *)
              (CST, 0.6, "Default to context-sensitive for safety")
          end
      end

(** * Batch Classification *)
let classify_rules rules =
  let classify_and_update rule =
    let (classification, confidence, reasoning) = classify_single_rule rule in
    let patterns = analyze_patterns rule in
    
    rule.classification <- Some classification;
    rule.confidence <- Some confidence;  
    rule.pattern_analysis <- patterns;
    
    {
      rule_id = rule.id;
      classification;
      confidence;
      reasoning;
      pattern_types = patterns;
    }
  in
  
  List.map classify_and_update rules

(** * Statistical Analysis *)
let generate_report classifications =
  let total = List.length classifications in
  let reg_count = List.length (List.filter (fun c -> c.classification = REG) classifications) in
  let vpl_count = List.length (List.filter (fun c -> c.classification = VPL) classifications) in  
  let cst_count = List.length (List.filter (fun c -> c.classification = CST) classifications) in
  
  let avg_confidence = 
    let sum = List.fold_left (fun acc c -> acc +. c.confidence) 0.0 classifications in
    if total > 0 then sum /. (float_of_int total) else 0.0
  in
  
  {
    total_rules = total;
    reg_count;
    vpl_count;
    cst_count; 
    avg_confidence;
    classifications;
  }

(** * Confidence Analysis *)
let analyze_confidence classifications =
  let high_conf = List.filter (fun c -> c.confidence >= 0.8) classifications in
  let med_conf = List.filter (fun c -> c.confidence >= 0.6 && c.confidence < 0.8) classifications in
  let low_conf = List.filter (fun c -> c.confidence < 0.6) classifications in
  
  Printf.printf "\nConfidence Analysis:\n";
  Printf.printf "  High confidence (≥0.8): %d rules (%.1f%%)\n" 
    (List.length high_conf) 
    (float_of_int (List.length high_conf) *. 100.0 /. float_of_int (List.length classifications));
  Printf.printf "  Medium confidence (0.6-0.8): %d rules (%.1f%%)\n"
    (List.length med_conf)
    (float_of_int (List.length med_conf) *. 100.0 /. float_of_int (List.length classifications));
  Printf.printf "  Low confidence (<0.6): %d rules (%.1f%%)\n"
    (List.length low_conf)
    (float_of_int (List.length low_conf) *. 100.0 /. float_of_int (List.length classifications));
  
  (* Report low confidence rules for review *)
  if List.length low_conf > 0 then (
    Printf.printf "\nLow confidence rules requiring review:\n";
    List.iter (fun c ->
      Printf.printf "  %s: %s (%.2f)\n" c.rule_id c.reasoning c.confidence
    ) (let rec take n lst = match n, lst with
         | 0, _ | _, [] -> []
         | n, x :: xs -> x :: take (n-1) xs
       in take 10 low_conf)  (* Show first 10 *)
  )