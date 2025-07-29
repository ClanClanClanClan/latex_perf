From Coq Require Import String List Bool Arith Lia.
From src.core.lexer Require Import LatexLexer.
From src.rules.phase1_5 Require Import PostExpansionRules.
Import ListNotations.

(** Get expanded tokens from document state *)
Definition get_expanded_tokens (doc : document_state) : list latex_token :=
  match doc.(expanded_tokens) with
  | Some tokens => tokens
  | None => doc.(tokens)
  end.

(** Check if document is in expanded state *)
Definition is_expanded (doc : document_state) : bool :=
  match doc.(expanded_tokens) with
  | Some _ => true
  | None => false
  end.

(** Test the problematic POST-037 validator *)
Definition post_037_test : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      
      (* Test the misplaced_math part *)
      let misplaced_math := flat_map (fun tok => match tok with
        | TCommand cmd =>
            if existsb (fun math_cmd => 
              match string_dec cmd math_cmd with
              | left _ => true
              | right _ => false
              end) ["alpha"; "beta"; "gamma"] then
              [{| rule_id := "POST-037"; issue_severity := Warning;
                  message := "Math command used outside math environment";
                  loc := None; suggested_fix := Some "wrap_in_math_mode";
                  rule_owner := "@math-team" |}]
            else []
        | _ => []
        end) expanded in
        
      (* Simple return *)
      misplaced_math
    else [].