(* Macro Catalog interface for Coq proofs *)

Require Import String List.
Require Import LaTeXPerfectionist.Core.Lexer.
Require Import LaTeXPerfectionist.Core.ExpanderTypes.

(* Catalog operations *)
Definition find_macro (pat : string) (catalog : macro_table) : option macro_entry :=
  List.find (fun entry => String.eqb entry.(pattern) pat) catalog.

Definition catalog_size (catalog : macro_table) : nat :=
  List.length catalog.

(* Catalog invariants *)
Definition valid_catalog (catalog : macro_table) : Prop :=
  forall entry, In entry catalog -> 
    String.length entry.(pattern) > 0 /\ entry.(priority) <= 100.

(* Well-formed catalog property *)
Definition wf_catalog (catalog : macro_table) : Prop :=
  valid_catalog catalog /\ 
  NoDup (List.map (fun entry => entry.(pattern)) catalog).