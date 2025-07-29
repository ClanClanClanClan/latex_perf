(** * EXTENDED MATH VALIDATORS - MATH-021 to MATH-040 *)

From Coq Require Import String List Bool Arith.
From validation Require Import ValidationTypes ValidationRules.
From expander Require Import ExpanderTypes.
From lexer Require Import LatexLexer.
Import ListNotations.
Open Scope string_scope.

(** ** MATH-021: Absolute value bars | | instead of \lvert \rvert *)
Fixpoint check_absolute_value_bars (tokens : list latex_token) (in_math : bool) : list validation_issue :=
  match tokens with
  | [] => []
  | TMathShift :: rest => check_absolute_value_bars rest (negb in_math)
  | TText "|" :: TText content :: TText "|" :: rest =>
      if in_math then
        {| rule_id := "MATH-021"; issue_severity := Info;
           message := String.append "Absolute value using | " 
                     (String.append content " | - use \\lvert " 
                     (String.append content " \\rvert instead"));
           loc := None; suggested_fix := Some "use_lvert_rvert";
           rule_owner := "@math-rules" |} :: check_absolute_value_bars rest in_math
      else check_absolute_value_bars rest in_math
  | _ :: rest => check_absolute_value_bars rest in_math
  end.

Definition math_021_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_absolute_value_bars expanded false
    else [].

(** ** MATH-022: Bold math without \bm or \mathbf *)
Definition math_022_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "bf" => (* Old-style bold in math *)
            [{| rule_id := "MATH-022"; issue_severity := Info;
                message := "Bold in math using \\bf - use \\mathbf{} or \\bm{} instead";
                loc := None; suggested_fix := Some "use_mathbf";
                rule_owner := "@math-rules" |}]
        | TCommand "textbf" => (* Text bold used in math context *)
            [{| rule_id := "MATH-022"; issue_severity := Info;
                message := "\\textbf in math mode - use \\mathbf{} for upright or \\bm{} for italic";
                loc := None; suggested_fix := Some "use_math_bold";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-025: Sum/product limits in inline math *)
Fixpoint check_inline_limits (tokens : list latex_token) (in_display : bool) : list validation_issue :=
  match tokens with
  | [] => []
  | TMathShift :: TMathShift :: rest => (* $$ starts display math *)
      check_inline_limits rest true
  | TMathShift :: rest => (* Single $ toggles inline math *)
      check_inline_limits rest false
  | TCommand "sum" :: TSubscript :: rest =>
      if negb in_display then
        {| rule_id := "MATH-025"; issue_severity := Info;
           message := "Sum with limits in inline math - consider display math";
           loc := None; suggested_fix := Some "use_display_math";
           rule_owner := "@math-rules" |} :: check_inline_limits rest in_display
      else check_inline_limits rest in_display
  | TCommand "prod" :: TSubscript :: rest =>
      if negb in_display then
        {| rule_id := "MATH-025"; issue_severity := Info;
           message := "Product with limits in inline math - consider display math";
           loc := None; suggested_fix := Some "use_display_math";
           rule_owner := "@math-rules" |} :: check_inline_limits rest in_display
      else check_inline_limits rest in_display
  | _ :: rest => check_inline_limits rest in_display
  end.

Definition math_025_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_inline_limits expanded false
    else [].

(** ** MATH-026: \subset vs \subseteq confusion *)
Definition math_026_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "subset" =>
            [{| rule_id := "MATH-026"; issue_severity := Info;
                message := "\\subset used - did you mean \\subseteq (subset or equal)?";
                loc := None; suggested_fix := Some "consider_subseteq";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-027: Double subscripts without grouping *)
Fixpoint check_double_subscripts (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText base :: TSubscript :: TText i :: TText j :: rest =>
      (* x_ij without braces *)
      {| rule_id := "MATH-027"; issue_severity := Warning;
         message := String.append "Double subscript " 
                   (String.append base "_" 
                   (String.append i j " should use braces: " 
                   (String.append base "_{" 
                   (String.append i j "}"))));
         loc := None; suggested_fix := Some "add_subscript_braces";
         rule_owner := "@math-rules" |} :: check_double_subscripts rest
  | _ :: rest => check_double_subscripts rest
  end.

Definition math_027_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_double_subscripts expanded
    else [].

(** ** MATH-028: Tilde ~ for similarity without \sim *)
Definition math_028_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TText "~" =>
            [{| rule_id := "MATH-028"; issue_severity := Warning;
                message := "Tilde ~ used for similarity - use \\sim instead";
                loc := None; suggested_fix := Some "use_sim";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-029: Prime notation x' vs x^{\prime} *)
Definition math_029_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "prime" =>
            [{| rule_id := "MATH-029"; issue_severity := Info;
                message := "\\prime used - consider using ' notation instead";
                loc := None; suggested_fix := Some "use_apostrophe";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-030: Ellipsis ... vs \ldots vs \cdots *)
Fixpoint check_ellipsis_usage (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText "." :: TText "." :: TText "." :: rest =>
      {| rule_id := "MATH-030"; issue_severity := Info;
         message := "Three dots ... used - consider \\ldots (baseline) or \\cdots (centered)";
         loc := None; suggested_fix := Some "use_dots_command";
         rule_owner := "@math-rules" |} :: check_ellipsis_usage rest
  | _ :: rest => check_ellipsis_usage rest
  end.

Definition math_030_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_ellipsis_usage expanded
    else [].

(** ** MATH-031: \limits on non-operator *)
Definition math_031_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      let rec check_limits (toks : list latex_token) : list validation_issue :=
        match toks with
        | [] => []
        | TCommand cmd :: TCommand "limits" :: rest =>
            let operators := ["sum"; "prod"; "int"; "oint"; "bigcup"; "bigcap"; 
                             "bigvee"; "bigwedge"; "coprod"] in
            if negb (existsb (String.eqb cmd) operators) then
              {| rule_id := "MATH-031"; issue_severity := Warning;
                 message := String.append "\\limits used on non-operator \\" cmd;
                 loc := None; suggested_fix := Some "remove_limits";
                 rule_owner := "@math-rules" |} :: check_limits rest
            else check_limits rest
        | _ :: rest => check_limits rest
        end in
      check_limits expanded
    else [].

(** ** MATH-032: Matrix without proper environment *)
Definition math_032_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "matrix" =>
            [{| rule_id := "MATH-032"; issue_severity := Info;
                message := "Plain \\matrix - consider pmatrix, bmatrix, or vmatrix";
                loc := None; suggested_fix := Some "use_specific_matrix";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-033: \over instead of \frac *)
Definition math_033_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "over" =>
            [{| rule_id := "MATH-033"; issue_severity := Warning;
                message := "\\over is plain TeX - use \\frac{}{} instead";
                loc := None; suggested_fix := Some "use_frac";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-034: Missing \, thin space in dx *)
Fixpoint check_differential_spacing (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "int" :: rest =>
      (* Look for pattern like \int f(x)dx without space before dx *)
      let rec scan_for_dx (toks : list latex_token) (depth : nat) : list validation_issue :=
        match toks with
        | [] => []
        | TText "d" :: TText var :: rest' =>
            if (depth >? 0) && (String.length var =? 1) then
              {| rule_id := "MATH-034"; issue_severity := Info;
                 message := String.append "Missing thin space before d" 
                           (String.append var " - use \\, d" var);
                 loc := None; suggested_fix := Some "add_thin_space";
                 rule_owner := "@math-rules" |} :: check_differential_spacing rest'
            else check_differential_spacing rest'
        | TCommand "int" :: rest' => scan_for_dx rest' depth (* Nested integral *)
        | _ :: rest' => 
            if depth <? 10 then scan_for_dx rest' (depth + 1)
            else check_differential_spacing rest'
        end in
      scan_for_dx rest 0
  | _ :: rest => check_differential_spacing rest
  end.

Definition math_034_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_differential_spacing expanded
    else [].

(** ** MATH-035: \choose instead of \binom *)
Definition math_035_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "choose" =>
            [{| rule_id := "MATH-035"; issue_severity := Warning;
                message := "\\choose is plain TeX - use \\binom{}{} instead";
                loc := None; suggested_fix := Some "use_binom";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-036: log without argument parentheses *)
Fixpoint check_log_parentheses (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "log" :: TText x :: rest =>
      (* Check if x is not "(" *)
      if negb (String.eqb x "(") && negb (String.eqb x "\\left") then
        {| rule_id := "MATH-036"; issue_severity := Info;
           message := String.append "\\log " (String.append x " - consider \\log(" 
                     (String.append x ")"));
           loc := None; suggested_fix := Some "add_log_parentheses";
           rule_owner := "@math-rules" |} :: check_log_parentheses rest
      else check_log_parentheses rest
  | _ :: rest => check_log_parentheses rest
  end.

Definition math_036_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_log_parentheses expanded
    else [].

(** ** MATH-037: \mod without proper spacing *)
Definition math_037_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      flat_map (fun tok =>
        match tok with
        | TCommand "mod" =>
            [{| rule_id := "MATH-037"; issue_severity := Info;
                message := "\\mod used - consider \\bmod for binary operator or \\pmod{} for parenthetical";
                loc := None; suggested_fix := Some "use_bmod_or_pmod";
                rule_owner := "@math-rules" |}]
        | _ => []
        end
      ) expanded
    else [].

(** ** MATH-038: := used instead of \coloneqq *)
Fixpoint check_colon_equals (tokens : list latex_token) : list validation_issue :=
  match tokens with
  | [] => []
  | TText ":" :: TText "=" :: rest =>
      {| rule_id := "MATH-038"; issue_severity := Info;
         message := "Definition operator := - consider using \\coloneqq";
         loc := None; suggested_fix := Some "use_coloneqq";
         rule_owner := "@math-rules" |} :: check_colon_equals rest
  | _ :: rest => check_colon_equals rest
  end.

Definition math_038_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_colon_equals expanded
    else [].

(** ** MATH-039: Large operators in inline math *)
Fixpoint check_large_ops_inline (tokens : list latex_token) (inline_math : bool) : list validation_issue :=
  match tokens with
  | [] => []
  | TMathShift :: TMathShift :: rest => (* Display math *)
      check_large_ops_inline rest false
  | TMathShift :: rest => (* Toggle inline math *)
      check_large_ops_inline rest (negb inline_math)
  | TCommand op :: rest =>
      let large_ops := ["sum"; "prod"; "int"; "oint"; "iint"; "iiint"; 
                       "bigcup"; "bigcap"; "bigoplus"; "bigotimes"] in
      if inline_math && (existsb (String.eqb op) large_ops) then
        {| rule_id := "MATH-039"; issue_severity := Info;
           message := String.append "Large operator \\" 
                     (String.append op " in inline math - consider display style");
           loc := None; suggested_fix := Some "use_displaystyle";
           rule_owner := "@math-rules" |} :: check_large_ops_inline rest inline_math
      else check_large_ops_inline rest inline_math
  | _ :: rest => check_large_ops_inline rest inline_math
  end.

Definition math_039_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_large_ops_inline expanded false
    else [].

(** ** MATH-040: Complex fractions need better formatting *)
Fixpoint check_complex_fractions (tokens : list latex_token) (depth : nat) : list validation_issue :=
  match tokens with
  | [] => []
  | TCommand "frac" :: rest =>
      (* Check if we're inside another frac *)
      if depth >? 0 then
        {| rule_id := "MATH-040"; issue_severity := Info;
           message := "Nested fraction detected - consider \\cfrac or restructuring";
           loc := None; suggested_fix := Some "use_cfrac";
           rule_owner := "@math-rules" |} :: check_complex_fractions rest (depth + 1)
      else check_complex_fractions rest (depth + 1)
  | TBeginGroup :: rest => check_complex_fractions rest depth
  | TEndGroup :: rest => 
      if depth >? 0 then check_complex_fractions rest (depth - 1)
      else check_complex_fractions rest depth
  | _ :: rest => check_complex_fractions rest depth
  end.

Definition math_040_validator_real : document_state -> list validation_issue :=
  fun doc =>
    if is_expanded doc then
      let expanded := get_expanded_tokens doc in
      check_complex_fractions expanded 0
    else [].