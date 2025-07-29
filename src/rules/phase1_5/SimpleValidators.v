(** * Simple Validators for Testing Extraction
    
    Minimal validators that compile without complex dependencies
    for initial testing of the extraction system.
**)

From Coq Require Import String List Bool Arith.
From src.core.lexer Require Import LatexLexer.
From src.rules.phase1_5 Require Import PostExpansionRules.
Import ListNotations.

(** ** Simple Context *)
Record simple_context : Type := {
  brace_depth : nat;
  current_line : nat
}.

Definition init_simple_context : simple_context := {|
  brace_depth := 0;
  current_line := 1
|}.

(** ** Simple Validators *)

(** DELIM-001: Simple brace balance checking *)
Definition delim_001_validator_simple : document_state -> list validation_issue :=
  fun doc =>
    match doc.(expanded_tokens) with
    | Some tokens =>
        let final_depth := fold_left (fun depth tok =>
          match tok with
          | TBeginGroup => S depth
          | TEndGroup => if depth =? 0 then depth else pred depth
          | _ => depth
          end) tokens 0 in
        if final_depth =? 0 then []
        else [{| rule_id := "DELIM-001"; issue_severity := Error;
                 message := "Unmatched braces detected";
                 loc := None; suggested_fix := Some "balance_braces";
                 rule_owner := "@delim-team" |}]
    | None => []
    end.

(** MATH-009: Simple bare function detection *)
Definition math_009_validator_simple : document_state -> list validation_issue :=
  fun doc =>
    match doc.(expanded_tokens) with
    | Some tokens =>
        flat_map (fun tok => match tok with
          | TText s => 
              if (substring 0 3 s =? "sin") || (substring 0 3 s =? "cos") then
                [{| rule_id := "MATH-009"; issue_severity := Warning;
                    message := "Bare function name detected";
                    loc := None; suggested_fix := Some "add_backslash";
                    rule_owner := "@math-team" |}]
              else []
          | _ => []
          end) tokens
    | None => []
    end.

(** REF-001: Simple undefined reference check *)
Definition ref_001_validator_simple : document_state -> list validation_issue :=
  fun doc =>
    match doc.(expanded_tokens) with
    | Some tokens =>
        (* Just check if there are any \ref commands *)
        if existsb (fun tok => match tok with
          | TCommand s => String.eqb s "ref"
          | _ => false
          end) tokens then
          [{| rule_id := "REF-001"; issue_severity := Warning;
              message := "Reference found - check if label exists";
              loc := None; suggested_fix := Some "verify_labels";
              rule_owner := "@ref-team" |}]
        else []
    | None => []
    end.

(** ** Extraction-ready validator list *)
Definition simple_validators : list (document_state -> list validation_issue) := [
  delim_001_validator_simple;
  math_009_validator_simple;
  ref_001_validator_simple
].

Definition run_simple_validators (doc : document_state) : list validation_issue :=
  flat_map (fun validator => validator doc) simple_validators.