(** Validator Pattern DSL - Core Type Definitions
    
    This module defines the foundation types for the Validator Pattern DSL
    that will enable automated generation of the 623 validation rules needed
    for LaTeX Perfectionist v25.
    
    Design Goal: Enable 15x productivity improvement from 0.77 to 10-12 validators/week
*)

(* Forward declaration of token type from Types module *)
type token = 
  | TText of string
  | TCommand of string  
  | TMathShift
  | TBeginGroup
  | TEndGroup
  | TSpace
  | TNewline
  | TComment of string

type position = {
  line: int;
  column: int;
  byte_offset: int;
}

let token_to_string = function
  | TText s -> Printf.sprintf "Text(\"%s\")" s
  | TCommand s -> Printf.sprintf "Command(\\%s)" s
  | TMathShift -> "MathShift($)"
  | TBeginGroup -> "BeginGroup({)"
  | TEndGroup -> "EndGroup(})"
  | TSpace -> "Space"
  | TNewline -> "Newline"
  | TComment s -> Printf.sprintf "Comment(%s)" s

(** Issue severity levels *)
type severity = 
  | Critical    (** Must fix - breaks compilation *)
  | Warning     (** Should fix - affects quality *)
  | Suggestion  (** Could fix - style improvement *)
  | Info        (** Informational - no fix needed *)

(** Issue location in document *)
type issue_location = {
  start_pos: position;
  end_pos: position;
  line: int;
  column: int;
}

(** Validation issue detected by a rule *)
type validation_issue = {
  id: string;                    (** Unique identifier like MATH-001 *)
  family: string;                (** Rule family: MATH, TYPO, STYLE, etc *)
  severity: severity;
  title: string;                 (** Short description *)
  message: string;               (** Detailed explanation *)
  location: issue_location;
  suggested_fix: string option;  (** Auto-fix suggestion if available *)
  confidence: float;             (** 0.0-1.0 confidence in detection *)
}

(** Pattern matching strategies *)
type pattern_matcher = 
  | TokenSequence of token list              (** Exact token sequence *)
  | TokenRegex of string                     (** Regex over token strings *)
  | ASTPattern of string                     (** Pattern over parsed AST *)
  | ContextualPattern of {
      pattern: pattern_matcher;
      required_context: token list;
      forbidden_context: token list;
    }
  | CompositePattern of {
      primary: pattern_matcher;
      secondary: pattern_matcher list;
      logic: [`And | `Or | `Not];
    }

(** Fix generation strategies *)
type fix_generator = 
  | SimpleReplace of {
      target: string;
      replacement: string;
    }
  | TemplateReplace of {
      template: string;
      variables: (string * string) list;
    }
  | CustomFix of {
      fixer: token list -> token list;
      description: string;
    }
  | NoFix                                    (** Issue detection only *)

(** Proof generation for formal verification *)
type proof_tactic = 
  | Auto                                     (** Try automatic proof *)
  | Rewrite of string list                   (** Apply rewrite rules *)
  | Induction of string                      (** Proof by induction *)
  | Cases of string                          (** Case analysis *)
  | Apply of string                          (** Apply theorem *)
  | Custom of string                         (** Custom Ltac code *)

(** Validator pattern definition - core of the DSL *)
type validator_pattern = {
  (* Identification *)
  family: string;                            (** MATH, TYPO, STYLE, etc *)
  id_prefix: string;                         (** MATH-001, TYPO-002, etc *)
  name: string;                              (** Human-readable name *)
  description: string;                       (** What this validator checks *)
  
  (* Detection *)
  matcher: pattern_matcher;                  (** How to find issues *)
  severity: severity;                        (** Issue severity *)
  
  (* Resolution *)
  fix_generator: fix_generator;              (** How to fix issues *)
  
  (* Verification *)
  proof_template: proof_tactic list;         (** Proof automation *)
  
  (* Quality *)
  test_cases: (string * bool) list;          (** (input, should_match) pairs *)
  confidence_threshold: float;               (** Minimum confidence to report *)
  
  (* Metadata *)
  tags: string list;                         (** Categorization tags *)
  priority: int;                             (** Execution priority 1-10 *)
  enabled: bool;                             (** Can be disabled *)
}

(** Collection of related patterns *)
type pattern_family = {
  name: string;                              (** Family name like "MATH" *)
  description: string;                       (** Family description *)
  patterns: validator_pattern list;          (** Patterns in this family *)
  common_proof_tactics: proof_tactic list;  (** Shared proof strategies *)
}

(** DSL compilation result *)
type compiled_validator = {
  pattern: validator_pattern;
  detector: token array -> validation_issue list;  (** Compiled detection function *)
  fixer: token array -> validation_issue -> token array option;  (** Compiled fix function *)
  proof: string;                             (** Generated Coq proof *)
}

(** DSL compiler state *)
type dsl_compiler = {
  patterns: validator_pattern list;
  compiled: compiled_validator list;
  proof_context: string list;                (** Active proof assumptions *)
  optimization_level: int;                   (** 0=debug, 3=max optimization *)
}

(** Ground truth data for pattern mining *)
type ground_truth_entry = {
  document: string;                          (** LaTeX source *)
  tokens: token array;                       (** Tokenized version *)
  issues: validation_issue list;             (** Known issues in document *)
  metadata: (string * string) list;         (** Additional annotations *)
}

type ground_truth_corpus = {
  entries: ground_truth_entry list;
  total_documents: int;
  total_issues: int;
  families_covered: string list;
}

(** Pattern mining results *)
type mined_pattern = {
  pattern: pattern_matcher;
  confidence: float;
  support: int;                              (** Number of occurrences *)
  examples: string list;                     (** Example matches *)
  suggested_family: string;
}

(** Utility functions for pattern construction *)
module PatternBuilder = struct
  
  (** Create a simple token sequence pattern *)
  let token_sequence tokens = TokenSequence tokens
  
  (** Create a regex pattern *)
  let regex pattern = TokenRegex pattern
  
  (** Create a pattern that requires specific context *)
  let with_context pattern ~required ~forbidden =
    ContextualPattern {
      pattern;
      required_context = required;
      forbidden_context = forbidden;
    }
  
  (** Combine patterns with AND logic *)
  let and_patterns primary secondary_list =
    CompositePattern {
      primary;
      secondary = secondary_list;
      logic = `And;
    }
  
  (** Create a simple replacement fix *)
  let simple_fix target replacement =
    SimpleReplace { target; replacement }
  
  (** Create a template-based fix *)
  let template_fix template variables =
    TemplateReplace { template; variables }
  
  (** Create a basic validator pattern *)
  let make_pattern ~family ~id_prefix ~name ~description ~matcher ~severity ?(fix_generator=NoFix) ?(proof_template=[Auto]) ?(test_cases=[]) ?(confidence_threshold=0.8) ?(tags=[]) ?(priority=5) ?(enabled=true) () =
    {
      family; id_prefix; name; description;
      matcher; severity; fix_generator; proof_template;
      test_cases; confidence_threshold; tags; priority; enabled;
    }
end

(** String conversion utilities for debugging *)
module Display = struct
  
  let severity_to_string = function
    | Critical -> "CRITICAL"
    | Warning -> "WARNING" 
    | Suggestion -> "SUGGESTION"
    | Info -> "INFO"
  
  let rec pattern_matcher_to_string = function
    | TokenSequence tokens -> 
        Printf.sprintf "TokenSeq[%s]" 
          (String.concat "; " (List.map token_to_string (Array.to_list (Array.of_list tokens))))
    | TokenRegex regex -> Printf.sprintf "Regex(%s)" regex
    | ASTPattern pattern -> Printf.sprintf "AST(%s)" pattern
    | ContextualPattern { pattern; _ } -> 
        Printf.sprintf "Contextual(%s)" (pattern_matcher_to_string pattern)
    | CompositePattern { primary; secondary; logic } ->
        let logic_str = match logic with `And -> "AND" | `Or -> "OR" | `Not -> "NOT" in
        Printf.sprintf "Composite(%s %s [%d more])" 
          (pattern_matcher_to_string primary) logic_str (List.length secondary)
  
  let validator_pattern_to_string pattern =
    Printf.sprintf "%s-%s: %s (%s, %s)" 
      pattern.family pattern.id_prefix pattern.name
      (severity_to_string pattern.severity)
      (pattern_matcher_to_string pattern.matcher)
end