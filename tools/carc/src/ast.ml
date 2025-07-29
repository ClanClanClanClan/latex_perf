(* CARC AST Module - Rule Abstract Syntax Tree *)
(* Following External AI CARC specification for rule classification *)

(** * Rule Categories *)
type rule_class = 
  | REG  (** Regular patterns - DFA processable *)
  | VPL  (** Visibly pushdown - VPA processable *) 
  | CST  (** Context-sensitive - Symbol table processable *)

(** * Rule Precondition Levels *)
type precondition =
  | L0_Lexer     (** Character-level patterns *)
  | L1_Expanded  (** Post-macro expansion *)
  | L2_Ast       (** AST-level analysis *)
  | L3_Semantics (** Semantic analysis *)
  | L4_Style     (** Style checking *)

(** * Rule Severity *)
type severity =
  | Error
  | Warning  
  | Info

(** * Rule Maturity *)
type maturity =
  | Draft
  | Beta
  | Stable

(** * Rule Pattern Analysis *)
type pattern_type =
  | CharPattern of char
  | StringPattern of string
  | RegexPattern of string
  | BalancedPattern of char * char  (** Open/close pairs *)
  | ContextPattern of string        (** Cross-reference patterns *)

(** * Rule Record *)
type rule = {
  id: string;
  description: string;
  precondition: precondition;
  default_severity: severity;
  maturity: maturity;
  owner: string;
  fix: string option;
  (* Classification fields - computed by CARC *)
  mutable classification: rule_class option;
  mutable confidence: float option;
  mutable pattern_analysis: pattern_type list;
}

(** * Rule Classification Result *)
type classification_result = {
  rule_id: string;
  classification: rule_class;
  confidence: float;
  reasoning: string;
  pattern_types: pattern_type list;
}

(** * CARC Classification Report *)
type carc_report = {
  total_rules: int;
  reg_count: int;
  vpl_count: int; 
  cst_count: int;
  avg_confidence: float;
  classifications: classification_result list;
}

(** * Utility Functions *)

let string_of_precondition = function
  | L0_Lexer -> "L0_Lexer"
  | L1_Expanded -> "L1_Expanded" 
  | L2_Ast -> "L2_Ast"
  | L3_Semantics -> "L3_Semantics"
  | L4_Style -> "L4_Style"

let precondition_of_string = function
  | "L0_Lexer" -> L0_Lexer
  | "L1_Expanded" -> L1_Expanded
  | "L2_Ast" -> L2_Ast
  | "L3_Semantics" -> L3_Semantics
  | "L4_Style" -> L4_Style
  | s -> failwith ("Unknown precondition: " ^ s)

let string_of_severity = function
  | Error -> "Error"
  | Warning -> "Warning"
  | Info -> "Info"

let severity_of_string = function
  | "Error" -> Error
  | "Warning" -> Warning
  | "Info" -> Info
  | s -> failwith ("Unknown severity: " ^ s)

let string_of_maturity = function
  | Draft -> "Draft"
  | Beta -> "Beta" 
  | Stable -> "Stable"

let maturity_of_string = function
  | "Draft" -> Draft
  | "Beta" -> Beta
  | "Stable" -> Stable
  | s -> failwith ("Unknown maturity: " ^ s)

(** * Classification Helpers *)

let contains_substring s sub =
  let len_s = String.length s in
  let len_sub = String.length sub in
  let rec check i =
    if i + len_sub > len_s then false
    else if String.sub s i len_sub = sub then true
    else check (i + 1)
  in
  if len_sub = 0 then true else check 0

let is_regex_only_pattern description =
  (* Phase 1: Syntactic filter for regex-only patterns *)
  let description_lower = String.lowercase_ascii description in
  List.exists (fun keyword -> 
    String.contains description_lower keyword
  ) ['\\'; '{'; '}'; '['; ']'; '*'; '+'; '?'; '^'; '$']

let is_balanced_pattern description =
  (* Phase 2: Balanced-token detector *)
  let description_lower = String.lowercase_ascii description in
  List.exists (fun phrase ->
    contains_substring description_lower phrase 
  ) ["begin"; "end"; "open"; "close"; "pair"; "match"; "balance"]

let is_context_sensitive description =
  (* Phase 3: Free-identifier analysis *)
  let description_lower = String.lowercase_ascii description in
  List.exists (fun phrase ->
    contains_substring description_lower phrase
  ) ["ref"; "label"; "cite"; "cross"; "reference"; "undefined"; "duplicate"]

(** * Classification Algorithm *)
let classify_rule rule =
  let desc = rule.description in
  
  (* Apply classification phases in order *)
  if is_regex_only_pattern desc && rule.precondition = L0_Lexer then
    (REG, 0.9, "Regex-only pattern at lexer level")
  else if is_balanced_pattern desc then
    (VPL, 0.8, "Balanced construct pattern detected")
  else if is_context_sensitive desc || rule.precondition = L3_Semantics then
    (CST, 0.85, "Context-sensitive or semantic analysis required")
  else if rule.precondition = L2_Ast then
    (VPL, 0.7, "AST-level analysis suggests structural pattern") 
  else
    (CST, 0.6, "Default to context-sensitive for safety")

(** * Pattern Analysis *)
let analyze_patterns rule =
  let desc = rule.description in
  let patterns = ref [] in
  
  (* Detect character patterns *)
  if String.contains desc '\\' then
    patterns := CharPattern '\\' :: !patterns;
  
  (* Detect string patterns *) 
  if String.contains desc '{' && String.contains desc '}' then
    patterns := BalancedPattern ('{', '}') :: !patterns;
    
  (* Detect regex patterns *)
  if is_regex_only_pattern desc then
    patterns := RegexPattern desc :: !patterns;
    
  (* Detect context patterns *)
  if is_context_sensitive desc then
    patterns := ContextPattern desc :: !patterns;
    
  !patterns