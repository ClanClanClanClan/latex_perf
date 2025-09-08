(* Expander Types interface for Coq proofs *)

Require Import String List.
Require Import LaTeXPerfectionist.Core.Lexer.

(* Expansion types *)
Inductive expansion_type : Type :=
  | SimpleText : string -> expansion_type
  | StyleCommand : string -> expansion_type
  | MathSymbol : string -> expansion_type
  | BuiltinSpace : string -> expansion_type.

Record macro_entry : Type := {
  pattern : string;
  expansion : expansion_type;
  priority : nat
}.

Definition macro_table := list macro_entry.

(* Expansion context *)
Record expansion_context : Type := {
  macros : macro_table;
  depth : nat;
  max_depth : nat
}.

Definition expand_result := option token_list.