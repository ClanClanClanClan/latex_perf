(** * VALIDATOR EXTRACTION - Convert Coq to Executable OCaml
    
    This extracts our REAL semantic validators to executable code
    for authentic corpus testing. NO MORE TOY IMPLEMENTATIONS.
**)

From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.
Require Import String List Bool Arith.

(* Import from correct paths based on actual file structure *)
From lexer Require Import LatexCatcodes LatexLexer.
From expander Require Import ExpanderTypes MacroCatalog ExpanderAlgorithm.
From phase1_5 Require Import PostExpansionRules RealValidators.

(** ** OCaml Extraction Setup **)

(** Extract basic types **)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Let Coq handle string extraction automatically *)

(** Extract LaTeX token types - matching actual LatexLexer.v **)
Extract Inductive latex_token => "latex_token" [
  "TCommand" "TBeginGroup" "TEndGroup" "TMathShift" "TAlignment" 
  "TParameter" "TSuperscript" "TSubscript" "TText" "TSpace" 
  "TComment" "TNewline" "TEOF"
].

(** Extract validation types **)
Extract Inductive severity => "severity" ["Error" "Warning" "Info"].

(** Extract document layer types **)
Extract Inductive layer => "layer" ["L0_Lexer" "L1_Expanded" "L2_Ast" "L3_Semantics" "L4_Style"].

(** ** Extract Just Basic Types First **)

Extraction "extracted_validators.ml" 
  severity
  layer
  validation_issue
  document_state
  delim_001_validator_real
  delim_002_validator_real
  delim_003_validator_real
  delim_004_validator_real
  delim_005_validator_real
  delim_006_validator_real
  delim_007_validator_real
  delim_008_validator_real
  delim_009_validator_real
  delim_010_validator_real
  post_028_validator_real
  post_029_validator_real
  post_030_validator_real
  post_031_validator_real
  post_032_validator_real
  post_033_validator_real
  post_034_validator_real
  post_035_validator_real
  post_036_validator_real
  post_037_validator_real
  post_038_validator_real
  post_039_validator_real
  post_040_validator_real
  math_002_validator_real
  math_003_validator_real
  math_004_validator_real
  math_005_validator_real
  math_006_validator_real
  math_007_validator_real
  math_009_validator_real
  math_010_validator_real
  math_011_validator_real
  math_012_validator_real
  math_013_validator_real
  math_014_validator_real
  math_015_validator_real
  math_016_validator_real
  math_017_validator_real
  math_018_validator_real
  math_019_validator_real
  math_020_validator_real
  ref_001_validator_real
  ref_002_validator_real
  ref_003_validator_real
  ref_004_validator_real
  ref_005_validator_real
  ref_006_validator_real
  script_001_validator_real
  script_002_validator_real
  cmd_001_validator_real
  cmd_002_validator_real
  cmd_003_validator_real
  cmd_004_validator_real
  cmd_005_validator_real
  ref_007_validator_real
  ref_009_validator_real
  script_003_validator_real
  script_005_validator_real
  script_006_validator_real
  script_007_validator_real
  ref_008_validator_real
  ref_010_validator_real
  script_004_validator_real
  script_008_validator_real
  script_009_validator_real
  script_010_validator_real
  math_001_validator_real
  math_008_validator_real
  math_021_validator_real
  math_022_validator_real
  math_023_validator_real
  math_024_validator_real
  math_025_validator_real
  math_026_validator_real
  math_027_validator_real
  math_028_validator_real
  math_029_validator_real
  math_030_validator_real
  math_031_validator_real
  math_032_validator_real.

(** Lexer and document processing **)
Extraction "latex_processor.ml"
  lex_string
  initial_state.

(** 🎉 COMPLETE VALIDATOR RUNNER - 80/80 validators (100% COMPLIANCE!) **)
Definition run_all_validators (doc : document_state) : list validation_issue :=
  app (delim_001_validator_real doc)
  (app (delim_002_validator_real doc)
  (app (delim_003_validator_real doc)
  (app (delim_004_validator_real doc)
  (app (delim_005_validator_real doc)
  (app (delim_006_validator_real doc)
  (app (delim_007_validator_real doc)
  (app (delim_008_validator_real doc)
  (app (delim_009_validator_real doc)
  (app (delim_010_validator_real doc)
  (app (post_028_validator_real doc)
  (app (post_029_validator_real doc)
  (app (post_030_validator_real doc)
  (app (post_031_validator_real doc)
  (app (post_032_validator_real doc)
  (app (post_033_validator_real doc)
  (app (post_034_validator_real doc)
  (app (post_035_validator_real doc)
  (app (post_036_validator_real doc)
  (app (post_037_validator_real doc)
  (app (post_038_validator_real doc)
  (app (post_039_validator_real doc)
  (app (post_040_validator_real doc)
  (app (math_002_validator_real doc)
  (app (math_003_validator_real doc)
  (app (math_004_validator_real doc)
  (app (math_005_validator_real doc)
  (app (math_006_validator_real doc)
  (app (math_007_validator_real doc)
  (app (math_009_validator_real doc)
  (app (math_010_validator_real doc)
  (app (math_011_validator_real doc)
  (app (math_012_validator_real doc)
  (app (math_013_validator_real doc)
  (app (math_014_validator_real doc)
  (app (math_015_validator_real doc)
  (app (math_016_validator_real doc)
  (app (math_017_validator_real doc)
  (app (math_018_validator_real doc)
  (app (math_019_validator_real doc)
  (app (math_020_validator_real doc)
  (app (ref_001_validator_real doc)
  (app (ref_002_validator_real doc)
  (app (ref_003_validator_real doc)
  (app (ref_004_validator_real doc)
  (app (ref_005_validator_real doc)
  (app (ref_006_validator_real doc)
  (app (script_001_validator_real doc)
  (app (script_002_validator_real doc)
  (app (cmd_001_validator_real doc)
  (app (cmd_002_validator_real doc)
  (app (cmd_003_validator_real doc)
  (app (cmd_004_validator_real doc)
  (app (cmd_005_validator_real doc)
  (app (ref_007_validator_real doc)
  (app (ref_009_validator_real doc)
  (app (script_003_validator_real doc)
  (app (script_005_validator_real doc)
  (app (script_006_validator_real doc)
  (app (script_007_validator_real doc)
  (app (ref_008_validator_real doc)
  (app (ref_010_validator_real doc)
  (app (script_004_validator_real doc)
  (app (script_008_validator_real doc)
  (app (script_009_validator_real doc)
  (app (script_010_validator_real doc)
  (app (math_001_validator_real doc)
  (app (math_008_validator_real doc)
  (app (math_021_validator_real doc)
  (app (math_022_validator_real doc)
  (app (math_023_validator_real doc)
  (app (math_024_validator_real doc)
  (app (math_025_validator_real doc)
  (app (math_026_validator_real doc)
  (app (math_027_validator_real doc)
  (app (math_028_validator_real doc)
  (app (math_029_validator_real doc)
  (app (math_030_validator_real doc)
  (app (math_031_validator_real doc)
  (math_032_validator_real doc))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Extraction "validator_runner.ml" run_all_validators.