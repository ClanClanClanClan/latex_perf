(** * Working Validators - Extraction Ready
    
    Minimal set of validators that compile successfully for testing
    the Coq-to-OCaml extraction pipeline.
**)

From Coq Require Import String List Bool Arith.
From src.core.lexer Require Import LatexLexer.
From src.rules.phase1_5 Require Import PostExpansionRules.
Import ListNotations.

(** ** Core Validation Functions *)

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

(** ** Working Validator Implementations *)

(** DELIM-001: Brace balance checking *)
Definition delim_001_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let tokens := get_expanded_tokens doc in
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
    else [].

(** DELIM-003: Left/right delimiter matching *)
Definition delim_003_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let tokens := get_expanded_tokens doc in
      let left_count := fold_left (fun count tok =>
        match tok with
        | TCommand s => if String.eqb s "left" then S count else count
        | _ => count
        end) tokens 0 in
      let right_count := fold_left (fun count tok =>
        match tok with
        | TCommand s => if String.eqb s "right" then S count else count
        | _ => count
        end) tokens 0 in
      if left_count =? right_count then []
      else [{| rule_id := "DELIM-003"; issue_severity := Error;
               message := "Unmatched \\left/\\right delimiters";
               loc := None; suggested_fix := Some "balance_left_right";
               rule_owner := "@delim-team" |}]
    else [].

(** MATH-009: Bare function name detection *)
Definition math_009_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let tokens := get_expanded_tokens doc in
      flat_map (fun tok => match tok with
        | TText s => 
            if (String.eqb s "sin") || (String.eqb s "cos") || (String.eqb s "tan") then
              [{| rule_id := "MATH-009"; issue_severity := Warning;
                  message := "Bare function name '" ++ s ++ "' - use \\" ++ s;
                  loc := None; suggested_fix := Some "add_backslash_to_function";
                  rule_owner := "@math-team" |}]
            else []
        | _ => []
        end) tokens
    else [].

(** REF-001: Undefined reference detection *)
Definition ref_001_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let tokens := get_expanded_tokens doc in
      
      (* Extract all label definitions *)
      let labels_defined := flat_map (fun tok => match tok with
        | TCommand s => if String.eqb s "label" then ["unknown_label"] else []
        | _ => []
        end) tokens in
        
      (* Extract all references *)  
      let refs_used := flat_map (fun tok => match tok with
        | TCommand s => if String.eqb s "ref" then ["unknown_ref"] else []
        | _ => []
        end) tokens in
      
      (* Simple check: if there are refs but no labels, report issue *)
      if (List.length refs_used >? 0) && (List.length labels_defined =? 0) then
        [{| rule_id := "REF-001"; issue_severity := Error;
            message := "References found but no labels defined";
            loc := None; suggested_fix := Some "add_missing_labels";
            rule_owner := "@ref-team" |}]
      else []
    else [].

(** ** Combined Validator Runner *)
Definition run_working_validators (doc : document_state) : list validation_issue :=
  delim_001_validator_real doc ++
  delim_003_validator_real doc ++
  math_009_validator_real doc ++
  ref_001_validator_real doc.