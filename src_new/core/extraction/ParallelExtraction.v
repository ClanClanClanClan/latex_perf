(**
 * Parallel Extraction for Enterprise LaTeX Validator
 * Extracts parallel execution functions to OCaml
 *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import core.lexer.LatexLexer.
Require Import core.validation.ValidationTypes.
Require Import rules.phase1.TypoRules.
Require Import ParallelValidator.

(** Set extraction language *)
Extraction Language OCaml.

(** Main parallel validator extraction *)
Extraction "parallel_validator.ml" 
  parallel_execute_spec
  parallel_execute_prioritized
  parallel_execute_early_termination
  enterprise_parallel_execute
  create_chunks
  optimal_chunk_size
  balance_chunks
  execute_chunk
  combine_results
  get_rule_priority
  filter_by_priority
  estimate_parallel_speedup
  parallel_all_l0_rules
  all_parallel_functions.

(** Export helper functions *)
Extraction "parallel_helpers.ml"
  execute_rule
  execute_rules_bucketed
  rule_applicable
  create_doc_state
  validate_document
  all_l0_rules
  lex.