(** * MATH VALIDATORS - Implementation of remaining MATH rules *)

From Coq Require Import String List Bool Arith.
Require Import Coq.Strings.Ascii.
(* Match the import style from RealValidators.v *)
From lexer Require Import LatexLexer.
From expander Require Import ExpanderTypes.
Require Import PostExpansionRules.
Require Import RealValidators.
Import ListNotations.
Open Scope string_scope.

(** Helper functions **)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

(** ** MATH-012: Multi-letter functions need \operatorname *)
Fixpoint check_multi_letter_functions_real (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText s :: rest => 
      let multi_funcs := ["sin"; "cos"; "tan"; "log"; "ln"; "exp"; "max"; "min"; 
                         "lim"; "sup"; "inf"; "det"; "dim"; "ker"; "rank"] in
      if existsb (String.eqb s) multi_funcs then
        {| rule_id := "MATH-012"; issue_severity := Warning;
           message := String.append (String.append (String.append (String.append "Multi-letter function '" s) "' should use \\operatorname{") s) "}";
           loc := None; suggested_fix := Some "wrap_operatorname";
           rule_owner := "@math-rules" |} :: check_multi_letter_functions_real rest
      else check_multi_letter_functions_real rest
  | _ :: rest => check_multi_letter_functions_real rest
  end.

Definition math_012_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_multi_letter_functions_real expanded
    else [].

(** ** MATH-013: Differential 'd' should be in roman *)
Fixpoint check_differential_d_real (tokens : list latex_token) (in_math : bool) : list validation_issue :=
  match tokens with
  | [] => []
  | TMathShift :: rest => check_differential_d_real rest (negb in_math)
  | TText "d" :: TText var :: rest =>
      if in_math && (String.length var =? 1) then
        (* Looks like dx, dy, dt etc *)
        {| rule_id := "MATH-013"; issue_severity := Info;
           message := String.append "Differential d in 'd" 
                     (String.append var "' should be typeset in roman: \\mathrm{d}" 
                     var);
           loc := None; suggested_fix := Some "use_mathrm_d";
           rule_owner := "@math-rules" |} :: check_differential_d_real rest in_math
      else check_differential_d_real rest in_math
  | _ :: rest => check_differential_d_real rest in_math
  end.

Definition math_013_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_differential_d_real expanded false
    else [].

(** ** MATH-014: Inline fraction \frac in text mode *)
Fixpoint check_inline_frac (tokens : list latex_token) (in_math : bool) : list validation_issue :=
  match tokens with
  | [] => []
  | TMathShift :: rest => check_inline_frac rest (negb in_math)
  | TCommand "frac" :: rest =>
      if negb in_math then
        {| rule_id := "MATH-014"; issue_severity := Info;
           message := "Inline fraction \\frac used in text - consider using a/b notation";
           loc := None; suggested_fix := Some "use_slash_notation";
           rule_owner := "@math-rules" |} :: check_inline_frac rest in_math
      else check_inline_frac rest in_math
  | _ :: rest => check_inline_frac rest in_math
  end.

Definition math_014_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_inline_frac expanded false
    else [].

(** ** MATH-015: \stackrel deprecated, use \overset *)
Definition math_015_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "stackrel" =>
            [{| rule_id := "MATH-015"; issue_severity := Warning;
                message := "\\stackrel is deprecated - use \\overset instead";
                loc := None; suggested_fix := Some "use_overset";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-016: Nested subscripts without braces *)
Fixpoint check_nested_subscripts_real (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText x :: TSubscript :: TText i :: TSubscript :: TText j :: rest =>
      {| rule_id := "MATH-016"; issue_severity := Warning;
         message := String.append "Nested subscripts " 
                   (String.append x "_{" 
                   (String.append i "}_{" 
                   (String.append j "} should use braces: " 
                   (String.append x "_{" 
                   (String.append i j "}")))));
         loc := None; suggested_fix := Some "fix_nested_subscripts";
         rule_owner := "@math-rules" |} :: check_nested_subscripts_real rest
  | _ :: rest => check_nested_subscripts_real rest
  end.

Definition math_016_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_nested_subscripts_real expanded
    else [].

(** ** MATH-017: Mismatched delimiter types \left{ ... \right] *)
Fixpoint check_delimiter_matching (tokens : list latex_token) (stack : list string) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "left" :: TText delim :: rest =>
      check_delimiter_matching rest (delim :: stack)
  | TCommand "right" :: TText delim :: rest =>
      match stack with
      | [] => (* No matching left *)
          {| rule_id := "MATH-017"; issue_severity := Error;
             message := String.append "\\right" (String.append delim " without matching \\left");
             loc := None; suggested_fix := Some "fix_delimiter_mismatch";
             rule_owner := "@math-rules" |} :: check_delimiter_matching rest stack
      | left_delim :: stack' =>
          let matching_pairs := [("(", ")"); ("[", "]"); ("{", "}"); ("|", "|"); 
                                ("\\{", "\\}"); ("\\langle", "\\rangle")] in
          let matches := existsb (fun pair => 
            andb (String.eqb (fst pair) left_delim) (String.eqb (snd pair) delim)
          ) matching_pairs in
          if negb matches && negb (String.eqb left_delim ".") && negb (String.eqb delim ".") then
            {| rule_id := "MATH-017"; issue_severity := Error;
               message := String.append "Mismatched delimiters: \\left" 
                         (String.append left_delim " ... \\right" delim);
               loc := None; suggested_fix := Some "fix_delimiter_mismatch";
               rule_owner := "@math-rules" |} :: check_delimiter_matching rest stack'
          else check_delimiter_matching rest stack'
      end
  | _ :: rest => check_delimiter_matching rest stack
  end.

Definition math_017_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_delimiter_matching expanded []
    else [].

(** ** MATH-018: Pi typed as 3.14 instead of \pi *)
Definition math_018_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TText s =>
            if String.eqb s "3.14" || String.eqb s "3.141" || String.eqb s "3.1415" then
              [{| rule_id := "MATH-018"; issue_severity := Info;
                  message := "Pi typed as numeric value - use \\pi instead";
                  loc := None; suggested_fix := Some "use_pi_symbol";
                  rule_owner := "@math-rules" |}]
            else []
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-019: Wrong order for combined sub/superscripts *)
Fixpoint check_script_order (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText base :: TSuperscript :: TText sup :: TSubscript :: TText sub :: rest =>
      (* x^a_b format - warn about order *)
      {| rule_id := "MATH-019"; issue_severity := Warning;
         message := String.append "Script order " 
                   (String.append base "^{" 
                   (String.append sup "}_{" 
                   (String.append sub "} - consider " 
                   (String.append base "_{" 
                   (String.append sub "}^{" 
                   (String.append sup "} for better spacing"))))));
         loc := None; suggested_fix := Some "reorder_scripts";
         rule_owner := "@math-rules" |} :: check_script_order rest
  | _ :: rest => check_script_order rest
  end.

Definition math_019_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_script_order expanded
    else [].

(** ** MATH-020: Missing \cdot between scalar and vector *)
Fixpoint check_scalar_vector_mult_real (tokens : list latex_token) (in_math : bool) : list validation_issue :=
  match tokens with
  | [] => []
  | TMathShift :: rest => check_scalar_vector_mult_real rest (negb in_math)
  | TText scalar :: TCommand "mathbf" :: rest =>
      if in_math && (forallb (fun c => (Nat.leb 48 (Ascii.nat_of_ascii c)) && 
                                       (Nat.leb (Ascii.nat_of_ascii c) 57)) 
                            (string_to_list scalar)) then
        (* Scalar number followed by vector *)
        {| rule_id := "MATH-020"; issue_severity := Info;
           message := String.append "Missing \\cdot between scalar " 
                     (String.append scalar " and vector");
           loc := None; suggested_fix := Some "add_cdot";
           rule_owner := "@math-rules" |} :: check_scalar_vector_mult_real rest in_math
      else check_scalar_vector_mult_real rest in_math
  | _ :: rest => check_scalar_vector_mult_real rest in_math
  end.

Definition math_020_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_scalar_vector_mult_real expanded false
    else [].