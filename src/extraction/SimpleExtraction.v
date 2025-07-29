(** * SIMPLE VALIDATOR EXTRACTION - Working Version
    
    This extracts simplified validators that compile correctly
    for immediate testing of the extraction pipeline.
**)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.
Require Import String List Bool Arith.

(* Import from correct paths *)
From src.core.lexer Require Import LatexLexer.
From src.rules.phase1_5 Require Import PostExpansionRules SimpleValidators.

(** ** OCaml Extraction Setup **)

(** Extract basic types **)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" ; "(::)" ].
Extract Inductive nat => "int" [ "0" ; "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(** Extract strings **)
Extract Inductive string => "string" [ """" "String.make 1"].

(** Extract LaTeX token types **)
Extract Inductive latex_token => "latex_token" [
  "TCommand" "TBeginGroup" "TEndGroup" "TMathShift" "TAlignment" "TNewline" 
  "TWhitespace" "TComment" "TText" "TEOF"
].

(** Extract validation types **)
Extract Inductive severity => "severity" ["Error" "Warning" "Info"].

Extract Inductive validation_issue => "validation_issue" 
  "{ rule_id : string; issue_severity : severity; message : string; 
     loc : (int * int) option; suggested_fix : string option; rule_owner : string }".

(** Extract document layer types **)
Extract Inductive layer => "layer" ["L0_Lexer" "L1_Expanded" "L2_Ast" "L3_Semantics" "L4_Style"].

Extract Inductive document_state => "document_state"
  "{ tokens : latex_token list; expanded_tokens : latex_token list option; 
     ast : string option; semantics : string option; filename : string; doc_layer : layer }".

(** ** Extract Simple Validators **)

(** Core simple validators **)
Extraction "simple_validators.ml" 
  delim_001_validator_simple
  math_009_validator_simple
  ref_001_validator_simple
  run_simple_validators.

(** Lexer **)
Extraction "simple_lexer.ml"
  lex_string
  initial_state.