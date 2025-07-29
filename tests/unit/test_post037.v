From Coq Require Import String List Bool Arith Lia.
Require Import Coq.Arith.Compare_dec.
From src.core.lexer Require Import LatexLexer.
From src.rules.phase1_5 Require Import PostExpansionRules.
Import ListNotations.

(** Check if string contains substring *)
Fixpoint string_contains_substring (s : string) (sub : string) : bool :=
  match s with
  | EmptyString => String.eqb sub EmptyString
  | String c rest => 
      if String.prefix sub s then true
      else string_contains_substring rest sub
  end.

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

(** Step 2: Add obsolete_math part *)
Definition post_037_step2 : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      
      let misplaced_math := flat_map (fun tok => match tok with
        | TCommand cmd =>
            if existsb (fun math_cmd => 
              String.eqb cmd math_cmd
              ) ["alpha"; "beta"; "gamma"] then
              [{| rule_id := "POST-037"; issue_severity := Warning;
                  message := "Math command used outside math environment";
                  loc := None; suggested_fix := Some "wrap_in_math_mode";
                  rule_owner := "@math-team" |}]
            else []
        | _ => []
        end) expanded in
        
      let obsolete_math := flat_map (fun tok => match tok with
        | TText s =>
            if string_contains_substring s "$$" then
              [{| rule_id := "POST-037"; issue_severity := Error;
                  message := "Obsolete $$ display math - use \\[ \\] or equation environment";
                  loc := None; suggested_fix := Some "replace_dollar_math";
                  rule_owner := "@math-team" |}]
            else []
        | _ => []
        end) expanded in
        
      let obsolete_math := flat_map (fun tok => match tok with
        | TText s =>
            if string_contains_substring s "$$" then
              [{| rule_id := "POST-037"; issue_severity := Error;
                  message := "Obsolete $$ display math - use \\[ \\] or equation environment";
                  loc := None; suggested_fix := Some "replace_dollar_math";
                  rule_owner := "@math-team" |}]
            else []
        | _ => []
        end) expanded in
        
      app misplaced_math obsolete_math
    else [].