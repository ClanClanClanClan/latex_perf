(* SIGMA Rules - L1_Expanded *)
(* Auto-generated from rules_unified.yaml *)

Require Import Coq.Strings.String.
Require Import LatexAST.
Require Import ValidationTypes.

(* Rule: CHEM-001 *)
(* Missing \\ce{} wrapper for chemical formula *)
Module Rule_CHEM_001.
  
  Definition id := "CHEM-001".
  Definition description := "Missing \\ce{} wrapper for chemical formula".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_CHEM_001.

(* Rule: CHEM-002 *)
(* Oxidation state superscript missing braces *)
Module Rule_CHEM_002.
  
  Definition id := "CHEM-002".
  Definition description := "Oxidation state superscript missing braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHEM_002.

(* Rule: CHEM-003 *)
(* Isotope mass number subscripted not superscripted *)
Module Rule_CHEM_003.
  
  Definition id := "CHEM-003".
  Definition description := "Isotope mass number subscripted not superscripted".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHEM_003.

(* Rule: CHEM-004 *)
(* Charge written as ^- instead of ^{-} *)
Module Rule_CHEM_004.
  
  Definition id := "CHEM-004".
  Definition description := "Charge written as ^- instead of ^{-}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHEM_004.

(* Rule: CHEM-005 *)
(* Chemical arrow typed as -> not \\rightarrow *)
Module Rule_CHEM_005.
  
  Definition id := "CHEM-005".
  Definition description := "Chemical arrow typed as -> not \\rightarrow".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_CHEM_005.

(* Rule: CHEM-006 *)
(* Stoichiometry coefficient inside \\ce missing *)
Module Rule_CHEM_006.
  
  Definition id := "CHEM-006".
  Definition description := "Stoichiometry coefficient inside \\ce missing".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHEM_006.

(* Rule: CHEM-007 *)
(* Reaction conditions not in \\text above arrow *)
Module Rule_CHEM_007.
  
  Definition id := "CHEM-007".
  Definition description := "Reaction conditions not in \\text above arrow".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHEM_007.

(* Rule: CHEM-008 *)
(* State symbols (aq) not in \\text *)
Module Rule_CHEM_008.
  
  Definition id := "CHEM-008".
  Definition description := "State symbols (aq) not in \\text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHEM_008.

(* Rule: CHEM-009 *)
(* Equilibrium arrow typed as <> *)
Module Rule_CHEM_009.
  
  Definition id := "CHEM-009".
  Definition description := "Equilibrium arrow typed as <>".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_CHEM_009.

(* Rule: CJK-008 *)
(* Full‑width space U+3000 inside math mode *)
Module Rule_CJK_008.
  
  Definition id := "CJK-008".
  Definition description := "Full‑width space U+3000 inside math mode".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    Some (remove_char_fix input).

  
End Rule_CJK_008.

(* Rule: CJK-015 *)
(* Chinese punctuation U+3001 inside math mode *)
Module Rule_CJK_015.
  
  Definition id := "CJK-015".
  Definition description := "Chinese punctuation U+3001 inside math mode".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CJK_015.

(* Rule: CMD-001 *)
(* Command \\newcommand defined but never used *)
Module Rule_CMD_001.
  
  Definition id := "CMD-001".
  Definition description := "Command \\newcommand defined but never used".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_001.

(* Rule: CMD-003 *)
(* User command name clashes with package macro *)
Module Rule_CMD_003.
  
  Definition id := "CMD-003".
  Definition description := "User command name clashes with package macro".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_003.

(* Rule: CMD-007 *)
(* Optional argument not used in definition body *)
Module Rule_CMD_007.
  
  Definition id := "CMD-007".
  Definition description := "Optional argument not used in definition body".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_007.

(* Rule: CMD-010 *)
(* More than three successive macro renewals *)
Module Rule_CMD_010.
  
  Definition id := "CMD-010".
  Definition description := "More than three successive macro renewals".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_010.

(* Rule: DELIM-001 *)
(* Unmatched delimiters { … } after macro expansion *)
Module Rule_DELIM_001.
  
  Definition id := "DELIM-001".
  Definition description := "Unmatched delimiters { … } after macro expansion".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_001.

(* Rule: DELIM-002 *)
(* Extra closing } detected *)
Module Rule_DELIM_002.
  
  Definition id := "DELIM-002".
  Definition description := "Extra closing } detected".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_002.

(* Rule: DELIM-003 *)
(* Unmatched \\left without \\right *)
Module Rule_DELIM_003.
  
  Definition id := "DELIM-003".
  Definition description := "Unmatched \\left without \\right".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_003.

(* Rule: DELIM-004 *)
(* Unmatched \\right without \\left *)
Module Rule_DELIM_004.
  
  Definition id := "DELIM-004".
  Definition description := "Unmatched \\right without \\left".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_004.

(* Rule: DELIM-005 *)
(* Mismatched parenthesis sizes (\\big vs \\Bigg) *)
Module Rule_DELIM_005.
  
  Definition id := "DELIM-005".
  Definition description := "Mismatched parenthesis sizes (\\big vs \\Bigg)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_005.

(* Rule: DELIM-006 *)
(* \\big delimiters used outside display math *)
Module Rule_DELIM_006.
  
  Definition id := "DELIM-006".
  Definition description := "\\big delimiters used outside display math".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_006.

(* Rule: DELIM-007 *)
(* Angle bracket \\langle without matching \\rangle *)
Module Rule_DELIM_007.
  
  Definition id := "DELIM-007".
  Definition description := "Angle bracket \\langle without matching \\rangle".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_007.

(* Rule: DELIM-008 *)
(* Empty \\left. … \\right. pair – redundant *)
Module Rule_DELIM_008.
  
  Definition id := "DELIM-008".
  Definition description := "Empty \\left. … \\right. pair – redundant".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_008.

(* Rule: DELIM-009 *)
(* Nested delimiters: {...( )...} *)
Module Rule_DELIM_009.
  
  Definition id := "DELIM-009".
  Definition description := "Nested delimiters: {...( )...}".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_009.

(* Rule: DELIM-010 *)
(* Display math uses \\big instead of \\Big *)
Module Rule_DELIM_010.
  
  Definition id := "DELIM-010".
  Definition description := "Display math uses \\big instead of \\Big".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_DELIM_010.

(* Rule: FONT-001 *)
(* Small‑caps applied to all‑caps word *)
Module Rule_FONT_001.
  
  Definition id := "FONT-001".
  Definition description := "Small‑caps applied to all‑caps word".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_FONT_001.

(* Rule: FONT-004 *)
(* Font change inside math via \\textit instead of \\mathit *)
Module Rule_FONT_004.
  
  Definition id := "FONT-004".
  Definition description := "Font change inside math via \\textit instead of \\mathit".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_FONT_004.

(* Rule: L3-001 *)
(* LaTeX3 macro \\tl_new:N in preamble mixed with 2e macros *)
Module Rule_L3_001.
  
  Definition id := "L3-001".
  Definition description := "LaTeX3 macro \\tl_new:N in preamble mixed with 2e macros".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_001.

(* Rule: L3-002 *)
(* Expl3 variable declared after \\begin{document} *)
Module Rule_L3_002.
  
  Definition id := "L3-002".
  Definition description := "Expl3 variable declared after \\begin{document}".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_002.

(* Rule: L3-003 *)
(* Expl3 and etoolbox patch macros combined *)
Module Rule_L3_003.
  
  Definition id := "L3-003".
  Definition description := "Expl3 and etoolbox patch macros combined".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_003.

(* Rule: L3-004 *)
(* Undocumented \\__module_internal:N used *)
Module Rule_L3_004.
  
  Definition id := "L3-004".
  Definition description := "Undocumented \\__module_internal:N used".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_004.

(* Rule: L3-005 *)
(* Missing \\ExplSyntaxOn guard around expl3 code *)
Module Rule_L3_005.
  
  Definition id := "L3-005".
  Definition description := "Missing \\ExplSyntaxOn guard around expl3 code".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_005.

(* Rule: L3-006 *)
(* Expl3 variable clobbers package macro name *)
Module Rule_L3_006.
  
  Definition id := "L3-006".
  Definition description := "Expl3 variable clobbers package macro name".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_006.

(* Rule: L3-007 *)
(* Mix of camelCase and snake_case in expl3 variable names *)
Module Rule_L3_007.
  
  Definition id := "L3-007".
  Definition description := "Mix of camelCase and snake_case in expl3 variable names".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_007.

(* Rule: L3-009 *)
(* LaTeX3 function deprecated _n: variant used *)
Module Rule_L3_009.
  
  Definition id := "L3-009".
  Definition description := "LaTeX3 function deprecated _n: variant used".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_L3_009.

(* Rule: MATH-009 *)
(* Bare 'sin', 'log', 'exp' inside math; use \\sin, \\log, \\exp *)
Module Rule_MATH_009.
  
  Definition id := "MATH-009".
  Definition description := "Bare 'sin', 'log', 'exp' inside math; use \\sin, \\log, \\exp".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_009.

(* Rule: MATH-010 *)
(* Division symbol ÷ used; prefer \\frac or / *)
Module Rule_MATH_010.
  
  Definition id := "MATH-010".
  Definition description := "Division symbol ÷ used; prefer \\frac or /".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_010.

(* Rule: MATH-011 *)
(* Vector notation inconsistent within equation *)
Module Rule_MATH_011.
  
  Definition id := "MATH-011".
  Definition description := "Vector notation inconsistent within equation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_011.

(* Rule: MATH-012 *)
(* Roman font for multi‑letter function missing (\\operatorname{}) *)
Module Rule_MATH_012.
  
  Definition id := "MATH-012".
  Definition description := "Roman font for multi‑letter function missing (\\operatorname{})".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_012.

(* Rule: MATH-013 *)
(* Differential d not typeset in roman *)
Module Rule_MATH_013.
  
  Definition id := "MATH-013".
  Definition description := "Differential d not typeset in roman".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_013.

(* Rule: MATH-014 *)
(* Inline fraction \\frac in text *)
Module Rule_MATH_014.
  
  Definition id := "MATH-014".
  Definition description := "Inline fraction \\frac in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_014.

(* Rule: MATH-015 *)
(* Stackrel used; prefer \\overset *)
Module Rule_MATH_015.
  
  Definition id := "MATH-015".
  Definition description := "Stackrel used; prefer \\overset".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_015.

(* Rule: MATH-016 *)
(* Nested subscripts without braces *)
Module Rule_MATH_016.
  
  Definition id := "MATH-016".
  Definition description := "Nested subscripts without braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_016.

(* Rule: MATH-017 *)
(* Mis‑matched \\left\\{ ... \\right] *)
Module Rule_MATH_017.
  
  Definition id := "MATH-017".
  Definition description := "Mis‑matched \\left\\{ ... \\right]".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_017.

(* Rule: MATH-018 *)
(* Pi typed as 3.14 instead of \\pi *)
Module Rule_MATH_018.
  
  Definition id := "MATH-018".
  Definition description := "Pi typed as 3.14 instead of \\pi".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_018.

(* Rule: MATH-019 *)
(* Inline stacked sub‑superscript ^_ order wrong *)
Module Rule_MATH_019.
  
  Definition id := "MATH-019".
  Definition description := "Inline stacked sub‑superscript ^_ order wrong".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_019.

(* Rule: MATH-020 *)
(* Missing \\cdot between scalar and vector *)
Module Rule_MATH_020.
  
  Definition id := "MATH-020".
  Definition description := "Missing \\cdot between scalar and vector".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_020.

(* Rule: MATH-021 *)
(* Absolute value bars used instead of \\lvert/\\rvert *)
Module Rule_MATH_021.
  
  Definition id := "MATH-021".
  Definition description := "Absolute value bars used instead of \\lvert/\\rvert".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_021.

(* Rule: MATH-022 *)
(* Bold math italic without \\bm or \\mathbf *)
Module Rule_MATH_022.
  
  Definition id := "MATH-022".
  Definition description := "Bold math italic without \\bm or \\mathbf".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_022.

(* Rule: MATH-030 *)
(* Overuse of \\displaystyle in inline math *)
Module Rule_MATH_030.
  
  Definition id := "MATH-030".
  Definition description := "Overuse of \\displaystyle in inline math".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_030.

(* Rule: MATH-031 *)
(* Operator spacing error: missing \\; before \\text *)
Module Rule_MATH_031.
  
  Definition id := "MATH-031".
  Definition description := "Operator spacing error: missing \\; before \\text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_031.

(* Rule: MATH-033 *)
(* Use of \\pm where ± symbol required in text *)
Module Rule_MATH_033.
  
  Definition id := "MATH-033".
  Definition description := "Use of \\pm where ± symbol required in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_033.

(* Rule: MATH-034 *)
(* Spacing before differential in integral missing \\, *)
Module Rule_MATH_034.
  
  Definition id := "MATH-034".
  Definition description := "Spacing before differential in integral missing \\,".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_034.

(* Rule: MATH-035 *)
(* Multiple subscripts stacked vertically without braces *)
Module Rule_MATH_035.
  
  Definition id := "MATH-035".
  Definition description := "Multiple subscripts stacked vertically without braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_035.

(* Rule: MATH-036 *)
(* Superfluous \\mathrm{} around single letter *)
Module Rule_MATH_036.
  
  Definition id := "MATH-036".
  Definition description := "Superfluous \\mathrm{} around single letter".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_036.

(* Rule: MATH-037 *)
(* xfrac package fraction used outside text mode *)
Module Rule_MATH_037.
  
  Definition id := "MATH-037".
  Definition description := "xfrac package fraction used outside text mode".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_037.

(* Rule: MATH-038 *)
(* Nested \\frac three levels deep *)
Module Rule_MATH_038.
  
  Definition id := "MATH-038".
  Definition description := "Nested \\frac three levels deep".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_038.

(* Rule: MATH-039 *)
(* Stacked relational operators without \\atop *)
Module Rule_MATH_039.
  
  Definition id := "MATH-039".
  Definition description := "Stacked relational operators without \\atop".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_039.

(* Rule: MATH-040 *)
(* Ellipsis \\ldots used between vertical alignment *)
Module Rule_MATH_040.
  
  Definition id := "MATH-040".
  Definition description := "Ellipsis \\ldots used between vertical alignment".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_040.

(* Rule: MATH-041 *)
(* Integral limits written inline; use displaystyle \\int *)
Module Rule_MATH_041.
  
  Definition id := "MATH-041".
  Definition description := "Integral limits written inline; use displaystyle \\int".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_041.

(* Rule: MATH-042 *)
(* Missing \\, between numbers and units in math *)
Module Rule_MATH_042.
  
  Definition id := "MATH-042".
  Definition description := "Missing \\, between numbers and units in math".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_042.

(* Rule: MATH-043 *)
(* Use of \\text instead of \\operatorname for function *)
Module Rule_MATH_043.
  
  Definition id := "MATH-043".
  Definition description := "Use of \\text instead of \\operatorname for function".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_043.

(* Rule: MATH-044 *)
(* Binary relation typed as text char (e.g. < for \\le) *)
Module Rule_MATH_044.
  
  Definition id := "MATH-044".
  Definition description := "Binary relation typed as text char (e.g. < for \\le)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_044.

(* Rule: MATH-045 *)
(* Math italic capital Greek without \\mathrm *)
Module Rule_MATH_045.
  
  Definition id := "MATH-045".
  Definition description := "Math italic capital Greek without \\mathrm".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_045.

(* Rule: MATH-046 *)
(* Ellipsis \\ldots used on relation axis; prefer \\cdots *)
Module Rule_MATH_046.
  
  Definition id := "MATH-046".
  Definition description := "Ellipsis \\ldots used on relation axis; prefer \\cdots".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_046.

(* Rule: MATH-047 *)
(* Double superscript without braces a^b^c *)
Module Rule_MATH_047.
  
  Definition id := "MATH-047".
  Definition description := "Double superscript without braces a^b^c".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_047.

(* Rule: MATH-048 *)
(* Boldface digits via \\mathbf in math – avoid *)
Module Rule_MATH_048.
  
  Definition id := "MATH-048".
  Definition description := "Boldface digits via \\mathbf in math – avoid".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_048.

(* Rule: MATH-049 *)
(* Spacing around \\times missing *)
Module Rule_MATH_049.
  
  Definition id := "MATH-049".
  Definition description := "Spacing around \\times missing".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_049.

(* Rule: MATH-050 *)
(* Circumflex accent ^\\hat on multi‑letter *)
Module Rule_MATH_050.
  
  Definition id := "MATH-050".
  Definition description := "Circumflex accent ^\\hat on multi‑letter".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_050.

(* Rule: MATH-051 *)
(* Radical \\sqrt nested two levels *)
Module Rule_MATH_051.
  
  Definition id := "MATH-051".
  Definition description := "Radical \\sqrt nested two levels".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_051.

(* Rule: MATH-052 *)
(* \\over brace used; prefer \\frac *)
Module Rule_MATH_052.
  
  Definition id := "MATH-052".
  Definition description := "\\over brace used; prefer \\frac".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_052.

(* Rule: MATH-053 *)
(* Space after \\left( at line start *)
Module Rule_MATH_053.
  
  Definition id := "MATH-053".
  Definition description := "Space after \\left( at line start".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    Some (remove_space_fix input).

  
End Rule_MATH_053.

(* Rule: MATH-055 *)
(* Math font change \\mathcal for single character only *)
Module Rule_MATH_055.
  
  Definition id := "MATH-055".
  Definition description := "Math font change \\mathcal for single character only".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_055.

(* Rule: MATH-056 *)
(* \\operatorname duplicated for same function *)
Module Rule_MATH_056.
  
  Definition id := "MATH-056".
  Definition description := "\\operatorname duplicated for same function".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_056.

(* Rule: MATH-057 *)
(* Empty fraction numerator or denominator *)
Module Rule_MATH_057.
  
  Definition id := "MATH-057".
  Definition description := "Empty fraction numerator or denominator".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_057.

(* Rule: MATH-058 *)
(* Nested \\text inside \\text *)
Module Rule_MATH_058.
  
  Definition id := "MATH-058".
  Definition description := "Nested \\text inside \\text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_058.

(* Rule: MATH-059 *)
(* Math accent \\bar on group expression needs braces *)
Module Rule_MATH_059.
  
  Definition id := "MATH-059".
  Definition description := "Math accent \\bar on group expression needs braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_059.

(* Rule: MATH-060 *)
(* Differential d typeset italic *)
Module Rule_MATH_060.
  
  Definition id := "MATH-060".
  Definition description := "Differential d typeset italic".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_060.

(* Rule: MATH-061 *)
(* Log base missing braces in \\log_10x *)
Module Rule_MATH_061.
  
  Definition id := "MATH-061".
  Definition description := "Log base missing braces in \\log_10x".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_MATH_061.

(* Rule: MATH-065 *)
(* Manual spacing \\hspace in math detected *)
Module Rule_MATH_065.
  
  Definition id := "MATH-065".
  Definition description := "Manual spacing \\hspace in math detected".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_065.

(* Rule: MATH-066 *)
(* \\phantom used; suggest \\hphantom or \\vphantom *)
Module Rule_MATH_066.
  
  Definition id := "MATH-066".
  Definition description := "\\phantom used; suggest \\hphantom or \\vphantom".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_066.

(* Rule: MATH-067 *)
(* Stacked limits on non‑operator *)
Module Rule_MATH_067.
  
  Definition id := "MATH-067".
  Definition description := "Stacked limits on non‑operator".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_067.

(* Rule: MATH-068 *)
(* Spacing around \\mid missing *)
Module Rule_MATH_068.
  
  Definition id := "MATH-068".
  Definition description := "Spacing around \\mid missing".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_068.

(* Rule: MATH-069 *)
(* Bold sans‑serif math font used *)
Module Rule_MATH_069.
  
  Definition id := "MATH-069".
  Definition description := "Bold sans‑serif math font used".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_069.

(* Rule: MATH-070 *)
(* Multiline subscripts lack \\substack *)
Module Rule_MATH_070.
  
  Definition id := "MATH-070".
  Definition description := "Multiline subscripts lack \\substack".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_070.

(* Rule: MATH-071 *)
(* Overuse of \\cancel in equations *)
Module Rule_MATH_071.
  
  Definition id := "MATH-071".
  Definition description := "Overuse of \\cancel in equations".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_071.

(* Rule: MATH-072 *)
(* Unknown math operator name *)
Module Rule_MATH_072.
  
  Definition id := "MATH-072".
  Definition description := "Unknown math operator name".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_072.

(* Rule: MATH-073 *)
(* xcolor macro \\color used inside math *)
Module Rule_MATH_073.
  
  Definition id := "MATH-073".
  Definition description := "xcolor macro \\color used inside math".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_073.

(* Rule: MATH-074 *)
(* TikZ node inside math without math mode set *)
Module Rule_MATH_074.
  
  Definition id := "MATH-074".
  Definition description := "TikZ node inside math without math mode set".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_074.

(* Rule: MATH-077 *)
(* Alignment point & outside alignment environment *)
Module Rule_MATH_077.
  
  Definition id := "MATH-077".
  Definition description := "Alignment point & outside alignment environment".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_077.

(* Rule: MATH-078 *)
(* Long arrow typed as --> instead of \\longrightarrow *)
Module Rule_MATH_078.
  
  Definition id := "MATH-078".
  Definition description := "Long arrow typed as --> instead of \\longrightarrow".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    Some (auto_replace_fix input).

  
End Rule_MATH_078.

(* Rule: MATH-079 *)
(* \\displaystyle inside display math – redundant *)
Module Rule_MATH_079.
  
  Definition id := "MATH-079".
  Definition description := "\\displaystyle inside display math – redundant".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_079.

(* Rule: MATH-081 *)
(* Improper kerning f(x) – suggest f\\!\\left(x\\right) *)
Module Rule_MATH_081.
  
  Definition id := "MATH-081".
  Definition description := "Improper kerning f(x) – suggest f\\!\\left(x\\right)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_081.

(* Rule: MATH-082 *)
(* Negative thin space \\! misused twice consecutively *)
Module Rule_MATH_082.
  
  Definition id := "MATH-082".
  Definition description := "Negative thin space \\! misused twice consecutively".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_082.

(* Rule: MATH-084 *)
(* Displaystyle \\sum in inline math *)
Module Rule_MATH_084.
  
  Definition id := "MATH-084".
  Definition description := "Displaystyle \\sum in inline math".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_084.

(* Rule: MATH-085 *)
(* Use of \\eqcirc – rarely acceptable *)
Module Rule_MATH_085.
  
  Definition id := "MATH-085".
  Definition description := "Use of \\eqcirc – rarely acceptable".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_085.

(* Rule: MATH-086 *)
(* Nested root \\sqrt{\\sqrt{…}} depth >2 *)
Module Rule_MATH_086.
  
  Definition id := "MATH-086".
  Definition description := "Nested root \\sqrt{\\sqrt{…}} depth >2".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_086.

(* Rule: MATH-087 *)
(* Maths uses fake bold via \\mathbf on digits *)
Module Rule_MATH_087.
  
  Definition id := "MATH-087".
  Definition description := "Maths uses fake bold via \\mathbf on digits".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_MATH_087.

(* Rule: REF-001 *)
(* Undefined \\ref / \\eqref label after expansion *)
Module Rule_REF_001.
  
  Definition id := "REF-001".
  Definition description := "Undefined \\ref / \\eqref label after expansion".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_001.

(* Rule: REF-002 *)
(* Duplicate label name *)
Module Rule_REF_002.
  
  Definition id := "REF-002".
  Definition description := "Duplicate label name".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_002.

(* Rule: REF-003 *)
(* Label contains spaces *)
Module Rule_REF_003.
  
  Definition id := "REF-003".
  Definition description := "Label contains spaces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_003.

(* Rule: REF-004 *)
(* Label contains uppercase letters *)
Module Rule_REF_004.
  
  Definition id := "REF-004".
  Definition description := "Label contains uppercase letters".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_004.

(* Rule: REF-005 *)
(* Label not prefixed with fig:, tab:, eq:, sec: *)
Module Rule_REF_005.
  
  Definition id := "REF-005".
  Definition description := "Label not prefixed with fig:, tab:, eq:, sec:".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_005.

(* Rule: REF-006 *)
(* Reference to page number uses \\ref not \\pageref *)
Module Rule_REF_006.
  
  Definition id := "REF-006".
  Definition description := "Reference to page number uses \\ref not \\pageref".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_REF_006.

(* Rule: REF-007 *)
(* Cite key contains whitespace *)
Module Rule_REF_007.
  
  Definition id := "REF-007".
  Definition description := "Cite key contains whitespace".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_007.

(* Rule: REF-009 *)
(* Reference appears before label definition (forward ref) *)
Module Rule_REF_009.
  
  Definition id := "REF-009".
  Definition description := "Reference appears before label definition (forward ref)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_REF_009.

(* Rule: RTL-003 *)
(* Unbalanced \\beginR / \\endR primitives *)
Module Rule_RTL_003.
  
  Definition id := "RTL-003".
  Definition description := "Unbalanced \\beginR / \\endR primitives".
  Definition severity := SeverityError.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_RTL_003.

(* Rule: RTL-004 *)
(* Bidirectional punctuation not mirrored in math *)
Module Rule_RTL_004.
  
  Definition id := "RTL-004".
  Definition description := "Bidirectional punctuation not mirrored in math".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_RTL_004.

(* Rule: SCRIPT-001 *)
(* Multi‑char subscript without braces *)
Module Rule_SCRIPT_001.
  
  Definition id := "SCRIPT-001".
  Definition description := "Multi‑char subscript without braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_SCRIPT_001.

(* Rule: SCRIPT-002 *)
(* Superscript dash used instead of \\textsuperscript{--} *)
Module Rule_SCRIPT_002.
  
  Definition id := "SCRIPT-002".
  Definition description := "Superscript dash used instead of \\textsuperscript{--}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_002.

(* Rule: SCRIPT-003 *)
(* Comma separated superscripts without braces *)
Module Rule_SCRIPT_003.
  
  Definition id := "SCRIPT-003".
  Definition description := "Comma separated superscripts without braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_003.

(* Rule: SCRIPT-004 *)
(* Subscript after prime notation mis‑ordered *)
Module Rule_SCRIPT_004.
  
  Definition id := "SCRIPT-004".
  Definition description := "Subscript after prime notation mis‑ordered".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_004.

(* Rule: SCRIPT-005 *)
(* Superscript uses letter l instead of \\ell *)
Module Rule_SCRIPT_005.
  
  Definition id := "SCRIPT-005".
  Definition description := "Superscript uses letter l instead of \\ell".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_SCRIPT_005.

(* Rule: SCRIPT-006 *)
(* Degree symbol typed as ° instead of ^\\circ *)
Module Rule_SCRIPT_006.
  
  Definition id := "SCRIPT-006".
  Definition description := "Degree symbol typed as ° instead of ^\\circ".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_SCRIPT_006.

(* Rule: SCRIPT-007 *)
(* Subscript text not in \\text{} *)
Module Rule_SCRIPT_007.
  
  Definition id := "SCRIPT-007".
  Definition description := "Subscript text not in \\text{}".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_SCRIPT_007.

(* Rule: SCRIPT-008 *)
(* Chemical formula lacks \\mathrm{} in subscript *)
Module Rule_SCRIPT_008.
  
  Definition id := "SCRIPT-008".
  Definition description := "Chemical formula lacks \\mathrm{} in subscript".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_008.

(* Rule: SCRIPT-009 *)
(* Isotope notation missing superscript mass number *)
Module Rule_SCRIPT_009.
  
  Definition id := "SCRIPT-009".
  Definition description := "Isotope notation missing superscript mass number".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_009.

(* Rule: SCRIPT-010 *)
(* Use of \\limits on inline operator *)
Module Rule_SCRIPT_010.
  
  Definition id := "SCRIPT-010".
  Definition description := "Use of \\limits on inline operator".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_010.

(* Rule: SCRIPT-011 *)
(* Nested superscript three levels deep *)
Module Rule_SCRIPT_011.
  
  Definition id := "SCRIPT-011".
  Definition description := "Nested superscript three levels deep".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_011.

(* Rule: SCRIPT-012 *)
(* Prime notation repeated (f''') – consider ^{(3)} *)
Module Rule_SCRIPT_012.
  
  Definition id := "SCRIPT-012".
  Definition description := "Prime notation repeated (f''') – consider ^{(3)}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_012.

(* Rule: SCRIPT-013 *)
(* Plus/minus in subscript – use \\pm outside index *)
Module Rule_SCRIPT_013.
  
  Definition id := "SCRIPT-013".
  Definition description := "Plus/minus in subscript – use \\pm outside index".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_013.

(* Rule: SCRIPT-014 *)
(* Logarithm base subscript not italic *)
Module Rule_SCRIPT_014.
  
  Definition id := "SCRIPT-014".
  Definition description := "Logarithm base subscript not italic".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_014.

(* Rule: SCRIPT-015 *)
(* Time derivative dot notation mis‑aligned *)
Module Rule_SCRIPT_015.
  
  Definition id := "SCRIPT-015".
  Definition description := "Time derivative dot notation mis‑aligned".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_015.

(* Rule: SCRIPT-016 *)
(* Prime on Greek letter should use ^\\prime *)
Module Rule_SCRIPT_016.
  
  Definition id := "SCRIPT-016".
  Definition description := "Prime on Greek letter should use ^\\prime".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_SCRIPT_016.

(* Rule: SCRIPT-017 *)
(* Inconsistent order of sub‑superscripts *)
Module Rule_SCRIPT_017.
  
  Definition id := "SCRIPT-017".
  Definition description := "Inconsistent order of sub‑superscripts".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_017.

(* Rule: SCRIPT-018 *)
(* Degree symbol typed in superscript without braces *)
Module Rule_SCRIPT_018.
  
  Definition id := "SCRIPT-018".
  Definition description := "Degree symbol typed in superscript without braces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_018.

(* Rule: SCRIPT-019 *)
(* Double prime typed as '' instead of ^{\\prime\\prime} *)
Module Rule_SCRIPT_019.
  
  Definition id := "SCRIPT-019".
  Definition description := "Double prime typed as '' instead of ^{\\prime\\prime}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
  (* Fix function *)
  Definition fix (input : latex_token_list) : option latex_token_list :=
    None (* TODO: Implement fix *).

  
End Rule_SCRIPT_019.

(* Rule: SCRIPT-020 *)
(* Subscript uses italic text instead of \\mathrm *)
Module Rule_SCRIPT_020.
  
  Definition id := "SCRIPT-020".
  Definition description := "Subscript uses italic text instead of \\mathrm".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondExpanded.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SCRIPT_020.

