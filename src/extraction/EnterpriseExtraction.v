(**
 * Enterprise-Scale OCaml Extraction for LaTeX Perfectionist v24
 * Simplified extraction focusing on core validators
 *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import rules.phase1.TypoRules.
Require Import core.validation.ValidationTypes.
Require Import core.lexer.LatexLexer.

(** Set extraction language *)
Extraction Language OCaml.

(** Create enterprise validators module *)
Extraction "enterprise_validators.ml" 
  (* Core validation infrastructure *)
  all_l0_rules execute_rule execute_rules_bucketed
  make_issue rule_applicable
  
  (* Document state creation *)
  create_doc_state validate_document
  
  (* Individual rule validators *)
  typo_001_validator typo_002_validator typo_003_validator typo_004_validator typo_005_validator
  enc_001_validator enc_002_validator enc_003_validator enc_004_validator enc_005_validator
  char_001_validator char_002_validator char_003_validator char_004_validator char_005_validator
  math_001_validator math_002_validator math_003_validator math_004_validator math_005_validator
  env_001_validator env_002_validator env_003_validator env_004_validator env_005_validator
  struct_001_validator struct_002_validator struct_003_validator struct_004_validator struct_005_validator
  struct_006_validator struct_007_validator struct_008_validator struct_009_validator struct_010_validator
  ref_001_validator ref_002_validator ref_003_validator ref_004_validator ref_005_validator
  ref_006_validator ref_007_validator ref_008_validator ref_009_validator ref_010_validator
  style_001_validator style_002_validator style_003_validator style_004_validator style_005_validator
  style_006_validator style_007_validator style_008_validator style_009_validator style_010_validator
  
  (* Lexer integration *)
  lex.