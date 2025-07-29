From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.
Require Import String List Bool Arith.

From lexer Require Import LatexCatcodes LatexLexer.
From expander Require Import ExpanderTypes MacroCatalog ExpanderAlgorithm.
From phase1_5 Require Import PostExpansionRules RealValidators.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive latex_token => "latex_token" [
  "TCommand" "TBeginGroup" "TEndGroup" "TMathShift" "TAlignment" 
  "TParameter" "TSuperscript" "TSubscript" "TText" "TSpace" 
  "TComment" "TNewline" "TEOF"
].

Extract Inductive severity => "severity" ["Error" "Warning" "Info"].
Extract Inductive layer => "layer" ["L0_Lexer" "L1_Expanded" "L2_Ast" "L3_Semantics" "L4_Style"].

Extraction "test_delim_001.ml" delim_001_validator_real.