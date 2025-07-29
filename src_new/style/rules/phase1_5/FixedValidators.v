(** * FIXED VALIDATORS - Correcting the 5 broken validators *)

From Coq Require Import String List Bool Arith.
From validation Require Import ValidationTypes ValidationRules.
From expander Require Import ExpanderTypes.
From lexer Require Import LatexLexer.
Import ListNotations.
Open Scope string_scope.

(** ** DELIM-008: Empty \left\right pairs (ANY empty pairs, not just dots) *)
Fixpoint check_empty_left_right_fixed (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "left" :: TCommand "right" :: rest =>
      (* Direct \left\right with nothing between *)
      {| rule_id := "DELIM-008"; issue_severity := Info;
         message := "Empty \\left\\right pair is redundant";
         loc := None; suggested_fix := Some "remove_empty_delimiters";
         rule_owner := "@lint-team" |} :: check_empty_left_right_fixed rest
  | TCommand "left" :: TText "." :: TCommand "right" :: TText "." :: rest =>
      (* \left. \right. case *)
      {| rule_id := "DELIM-008"; issue_severity := Info;
         message := "Empty \\left. \\right. pair is redundant";
         loc := None; suggested_fix := Some "remove_empty_delimiters";
         rule_owner := "@lint-team" |} :: check_empty_left_right_fixed rest
  | _ :: rest => check_empty_left_right_fixed rest
  end.

Definition delim_008_validator_fixed : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_empty_left_right_fixed expanded
    else [].

(** ** MATH-009: Misplaced math commands (used outside math mode) *)
Fixpoint in_math_mode (tokens : list latex_token) (math_depth : nat) : list (latex_token * bool) :=
  match tokens with
  | [] => []
  | TMathShift :: rest => 
      (* Toggle math mode *)
      let new_depth := if Nat.eqb math_depth 0 then 1 else 0 in
      (TMathShift, Nat.ltb 0 math_depth) :: in_math_mode rest new_depth
  | tok :: rest =>
      (tok, Nat.ltb 0 math_depth) :: in_math_mode rest math_depth
  end.

Definition math_009_validator_fixed : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      let tokens_with_mode := in_math_mode expanded 0 in
      
      (* Math commands that require math mode *)
      let math_commands := ["frac"; "sqrt"; "sum"; "prod"; "int"; "lim"; 
                           "infty"; "alpha"; "beta"; "gamma"; "theta"] in
      
      flat_map (fun pair =>
        match pair with
        | (TCommand cmd, false) => (* Command outside math mode *)
            if existsb (String.eqb cmd) math_commands then
              [{| rule_id := "MATH-009"; issue_severity := Warning;
                  message := String.append "Math command \\" (String.append cmd " used outside math mode");
                  loc := None; suggested_fix := Some "wrap_in_math_mode";
                  rule_owner := "@lint-team" |}]
            else []
        | _ => []
        end
      ) tokens_with_mode
    else [].

(** ** MATH-010: Middle dot · instead of \cdot *)
Fixpoint check_middle_dot (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText s :: rest =>
      (* Check if text contains middle dot character *)
      if string_contains_substring s "·" then
        [{| rule_id := "MATH-010"; issue_severity := Warning;
            message := "Division symbol · detected - use \\frac{a}{b} or / instead";
            loc := None; suggested_fix := Some "use_cdot_command";
            rule_owner := "@lint-team" |}]
      else check_middle_dot rest
  | _ :: rest => check_middle_dot rest
  end.

Definition math_010_validator_fixed : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_middle_dot expanded
    else [].

(** ** SCRIPT-001: Multi-letter subscripts without braces *)
Fixpoint check_subscripts_fixed (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TSubscript :: TText sub :: rest =>
      if Nat.ltb 1 (String.length sub) then  (* Multi-character subscript *)
        {| rule_id := "SCRIPT-001"; issue_severity := Warning;
           message := String.append "Multi-character subscript '" 
                     (String.append sub "' should be in braces: _{" 
                     (String.append sub "}"));
           loc := None; suggested_fix := Some "wrap_subscript_in_braces";
           rule_owner := "@lint-team" |} :: check_subscripts_fixed rest
      else check_subscripts_fixed rest
  | _ :: rest => check_subscripts_fixed rest
  end.

Definition script_001_validator_fixed : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_subscripts_fixed expanded
    else [].

(** ** CMD-001: Obsolete commands *)
Definition cmd_001_validator_fixed : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      
      (* List of obsolete commands and their replacements *)
      let obsolete_commands := [
        ("bf", "textbf");
        ("it", "textit");
        ("rm", "textrm");
        ("sf", "textsf");
        ("tt", "texttt");
        ("sc", "textsc");
        ("em", "emph");
        ("cal", "mathcal");
        ("centerline", "centering");
        ("over", "frac")
      ] in
      
      flat_map (fun tok =>
        match tok with
        | TCommand cmd =>
            match find (fun pair => String.eqb (fst pair) cmd) obsolete_commands with
            | Some (obs, repl) =>
                [{| rule_id := "CMD-001"; issue_severity := Info;
                    message := String.append "Obsolete command \\" 
                              (String.append obs " - use \\" 
                              (String.append repl " instead"));
                    loc := None; suggested_fix := Some (String.append "use_" repl);
                    rule_owner := "@lint-team" |}]
            | None => []
            end
        | _ => []
        end
      ) expanded
    else [].