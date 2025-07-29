(* SIGMA Rules - L2_Ast *)
(* Auto-generated from rules_unified.yaml *)

Require Import Coq.Strings.String.
Require Import LatexAST.
Require Import ValidationTypes.

(* Rule: ACCESS-001 *)
(* Alt text shorter than 5 characters *)
Module Rule_ACCESS_001.
  
  Definition id := "ACCESS-001".
  Definition description := "Alt text shorter than 5 characters".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\includegraphics.*\[.*alt\s*=\s*[^,\]]{0,5}.*\]").
  
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

  
End Rule_ACCESS_001.

(* Rule: ACCESS-002 *)
(* Alt text identical to caption *)
Module Rule_ACCESS_002.
  
  Definition id := "ACCESS-002".
  Definition description := "Alt text identical to caption".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_ACCESS_002.

(* Rule: ACCESS-005 *)
(* Hyperlink text 'click here' *)
Module Rule_ACCESS_005.
  
  Definition id := "ACCESS-005".
  Definition description := "Hyperlink text 'click here'".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_ACCESS_005.

(* Rule: ACCESS-008 *)
(* Math in alt text – screen readers may fail *)
Module Rule_ACCESS_008.
  
  Definition id := "ACCESS-008".
  Definition description := "Math in alt text – screen readers may fail".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_ACCESS_008.

(* Rule: ACCESS-009 *)
(* Table lacks \\caption* for screen readers *)
Module Rule_ACCESS_009.
  
  Definition id := "ACCESS-009".
  Definition description := "Table lacks \\caption* for screen readers".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_ACCESS_009.

(* Rule: BIB-001 *)
(* Bibliography style unspecified *)
Module Rule_BIB_001.
  
  Definition id := "BIB-001".
  Definition description := "Bibliography style unspecified".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_BIB_001.

(* Rule: BIB-002 *)
(* Citation key not in UTF‑8 NFC *)
Module Rule_BIB_002.
  
  Definition id := "BIB-002".
  Definition description := "Citation key not in UTF‑8 NFC".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_BIB_002.

(* Rule: BIB-004 *)
(* Legacy BibTeX entrytype misc detected *)
Module Rule_BIB_004.
  
  Definition id := "BIB-004".
  Definition description := "Legacy BibTeX entrytype misc detected".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_BIB_004.

(* Rule: BIB-006 *)
(* Bibliography file path outside project root *)
Module Rule_BIB_006.
  
  Definition id := "BIB-006".
  Definition description := "Bibliography file path outside project root".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_BIB_006.

(* Rule: BIB-010 *)
(* Multiple bibliography styles declared *)
Module Rule_BIB_010.
  
  Definition id := "BIB-010".
  Definition description := "Multiple bibliography styles declared".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_BIB_010.

(* Rule: CJK-004 *)
(* xeCJK package missing when CJK glyphs detected *)
Module Rule_CJK_004.
  
  Definition id := "CJK-004".
  Definition description := "xeCJK package missing when CJK glyphs detected".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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
    Some (insert_usepackage_fix input).

  
End Rule_CJK_004.

(* Rule: CJK-006 *)
(* Ruby annotation without ruby package *)
Module Rule_CJK_006.
  
  Definition id := "CJK-006".
  Definition description := "Ruby annotation without ruby package".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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
    Some (insert_usepackage_fix input).

  
End Rule_CJK_006.

(* Rule: COL-006 *)
(* xcolor option dvipsnames used with pdfLaTeX *)
Module Rule_COL_006.
  
  Definition id := "COL-006".
  Definition description := "xcolor option dvipsnames used with pdfLaTeX".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_COL_006.

(* Rule: DOC-001 *)
(* Title missing \\maketitle *)
Module Rule_DOC_001.
  
  Definition id := "DOC-001".
  Definition description := "Title missing \\maketitle".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_DOC_001.

(* Rule: DOC-002 *)
(* Abstract environment missing *)
Module Rule_DOC_002.
  
  Definition id := "DOC-002".
  Definition description := "Abstract environment missing".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_DOC_002.

(* Rule: DOC-003 *)
(* Keywords missing *)
Module Rule_DOC_003.
  
  Definition id := "DOC-003".
  Definition description := "Keywords missing".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_DOC_003.

(* Rule: DOC-004 *)
(* Acknowledgment section before conclusion *)
Module Rule_DOC_004.
  
  Definition id := "DOC-004".
  Definition description := "Acknowledgment section before conclusion".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_DOC_004.

(* Rule: FIG-001 *)
(* Figure without caption *)
Module Rule_FIG_001.
  
  Definition id := "FIG-001".
  Definition description := "Figure without caption".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_001.

(* Rule: FIG-002 *)
(* Figure without label *)
Module Rule_FIG_002.
  
  Definition id := "FIG-002".
  Definition description := "Figure without label".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_002.

(* Rule: FIG-003 *)
(* Label before caption in figure *)
Module Rule_FIG_003.
  
  Definition id := "FIG-003".
  Definition description := "Label before caption in figure".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_003.

(* Rule: FIG-007 *)
(* Figure lacks alt text for accessibility *)
Module Rule_FIG_007.
  
  Definition id := "FIG-007".
  Definition description := "Figure lacks alt text for accessibility".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_007.

(* Rule: FIG-009 *)
(* Float position specifier ! used excessively *)
Module Rule_FIG_009.
  
  Definition id := "FIG-009".
  Definition description := "Float position specifier ! used excessively".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_009.

(* Rule: FIG-010 *)
(* Subfigure environment without \\subcaption *)
Module Rule_FIG_010.
  
  Definition id := "FIG-010".
  Definition description := "Subfigure environment without \\subcaption".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_010.

(* Rule: FIG-012 *)
(* Figure listed in LoF but not referenced *)
Module Rule_FIG_012.
  
  Definition id := "FIG-012".
  Definition description := "Figure listed in LoF but not referenced".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_012.

(* Rule: FIG-013 *)
(* Graphicx option scale used instead of width *)
Module Rule_FIG_013.
  
  Definition id := "FIG-013".
  Definition description := "Graphicx option scale used instead of width".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_013.

(* Rule: FIG-014 *)
(* Figure caption exceeds 300 characters *)
Module Rule_FIG_014.
  
  Definition id := "FIG-014".
  Definition description := "Figure caption exceeds 300 characters".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_014.

(* Rule: FIG-017 *)
(* Sidewaysfigure used with portrait page layout *)
Module Rule_FIG_017.
  
  Definition id := "FIG-017".
  Definition description := "Sidewaysfigure used with portrait page layout".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_017.

(* Rule: FIG-019 *)
(* Subcaption label missing (a), (b)… *)
Module Rule_FIG_019.
  
  Definition id := "FIG-019".
  Definition description := "Subcaption label missing (a), (b)…".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FIG_019.

(* Rule: FONT-006 *)
(* Missing \\microtypesetup{expansion=true} *)
Module Rule_FONT_006.
  
  Definition id := "FONT-006".
  Definition description := "Missing \\microtypesetup{expansion=true}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FONT_006.

(* Rule: FONT-007 *)
(* Obsolete \\usepackage[T1]{fontenc} under XeLaTeX *)
Module Rule_FONT_007.
  
  Definition id := "FONT-007".
  Definition description := "Obsolete \\usepackage[T1]{fontenc} under XeLaTeX".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FONT_007.

(* Rule: FONT-008 *)
(* Multiple \\setmainfont declarations *)
Module Rule_FONT_008.
  
  Definition id := "FONT-008".
  Definition description := "Multiple \\setmainfont declarations".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_FONT_008.

(* Rule: L3-008 *)
(* Expl3 module lacks \\ProvidesExplPackage *)
Module Rule_L3_008.
  
  Definition id := "L3-008".
  Definition description := "Expl3 module lacks \\ProvidesExplPackage".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_L3_008.

(* Rule: L3-010 *)
(* ExplSyntaxOff missing at end of file *)
Module Rule_L3_010.
  
  Definition id := "L3-010".
  Definition description := "ExplSyntaxOff missing at end of file".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_L3_010.

(* Rule: LANG-001 *)
(* \\usepackage[british]{babel} but US spelling detected *)
Module Rule_LANG_001.
  
  Definition id := "LANG-001".
  Definition description := "\\usepackage[british]{babel} but US spelling detected".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_LANG_001.

(* Rule: LANG-002 *)
(* babel language option missing *)
Module Rule_LANG_002.
  
  Definition id := "LANG-002".
  Definition description := "babel language option missing".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_LANG_002.

(* Rule: LANG-004 *)
(* Polyglossia loaded with babel simultaneously *)
Module Rule_LANG_004.
  
  Definition id := "LANG-004".
  Definition description := "Polyglossia loaded with babel simultaneously".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_LANG_004.

(* Rule: LANG-006 *)
(* Non‑English abstract before \\selectlanguage *)
Module Rule_LANG_006.
  
  Definition id := "LANG-006".
  Definition description := "Non‑English abstract before \\selectlanguage".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_LANG_006.

(* Rule: LANG-007 *)
(* babel shorthand \" used instead of \\og/\\fg *)
Module Rule_LANG_007.
  
  Definition id := "LANG-007".
  Definition description := "babel shorthand \"" used instead of \\og/\\fg".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_LANG_007.

(* Rule: MATH-023 *)
(* Equation label missing when referenced *)
Module Rule_MATH_023.
  
  Definition id := "MATH-023".
  Definition description := "Equation label missing when referenced".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_023.

(* Rule: MATH-024 *)
(* Equation has label but is never referenced *)
Module Rule_MATH_024.
  
  Definition id := "MATH-024".
  Definition description := "Equation has label but is never referenced".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_024.

(* Rule: MATH-025 *)
(* Align environment with single column – prefer equation *)
Module Rule_MATH_025.
  
  Definition id := "MATH-025".
  Definition description := "Align environment with single column – prefer equation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_025.

(* Rule: MATH-028 *)
(* Array environment inside math lacks {c} alignment *)
Module Rule_MATH_028.
  
  Definition id := "MATH-028".
  Definition description := "Array environment inside math lacks {c} alignment".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_028.

(* Rule: MATH-029 *)
(* Use of eqnarray* instead of align* *)
Module Rule_MATH_029.
  
  Definition id := "MATH-029".
  Definition description := "Use of eqnarray* instead of align*".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_029.

(* Rule: MATH-032 *)
(* Incorrect small matrix brackets *)
Module Rule_MATH_032.
  
  Definition id := "MATH-032".
  Definition description := "Incorrect small matrix brackets".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_032.

(* Rule: MATH-054 *)
(* Equation labelled 'eq:' without environment *)
Module Rule_MATH_054.
  
  Definition id := "MATH-054".
  Definition description := "Equation labelled 'eq:' without environment".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_054.

(* Rule: MATH-062 *)
(* Multiline equation lacks alignment character & *)
Module Rule_MATH_062.
  
  Definition id := "MATH-062".
  Definition description := "Multiline equation lacks alignment character &".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_062.

(* Rule: MATH-063 *)
(* Equation array with >1 alignment point *)
Module Rule_MATH_063.
  
  Definition id := "MATH-063".
  Definition description := "Equation array with >1 alignment point".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_063.

(* Rule: MATH-064 *)
(* Use of \\eqalign – obsolete *)
Module Rule_MATH_064.
  
  Definition id := "MATH-064".
  Definition description := "Use of \\eqalign – obsolete".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_064.

(* Rule: MATH-075 *)
(* Equation number suppressed with \\nonumber but referenced *)
Module Rule_MATH_075.
  
  Definition id := "MATH-075".
  Definition description := "Equation number suppressed with \\nonumber but referenced".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_075.

(* Rule: MATH-080 *)
(* Equation exceeds 3 alignment columns *)
Module Rule_MATH_080.
  
  Definition id := "MATH-080".
  Definition description := "Equation exceeds 3 alignment columns".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MATH_080.

(* Rule: MENV-001 *)
(* \\begin{eqnarray} is obsolete; use {align} *)
Module Rule_MENV_001.
  
  Definition id := "MENV-001".
  Definition description := "\\begin{eqnarray} is obsolete; use {align}".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_MENV_001.

(* Rule: META-002 *)
(* Revision hash missing from \\date field *)
Module Rule_META_002.
  
  Definition id := "META-002".
  Definition description := "Revision hash missing from \\date field".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_META_002.

(* Rule: PKG-001 *)
(* Package duplicate inclusion detected *)
Module Rule_PKG_001.
  
  Definition id := "PKG-001".
  Definition description := "Package duplicate inclusion detected".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_001.

(* Rule: PKG-002 *)
(* geometry loaded after hyperref – must precede *)
Module Rule_PKG_002.
  
  Definition id := "PKG-002".
  Definition description := "geometry loaded after hyperref – must precede".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_002.

(* Rule: PKG-004 *)
(* Package loaded after \\begin{document} *)
Module Rule_PKG_004.
  
  Definition id := "PKG-004".
  Definition description := "Package loaded after \\begin{document}".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_004.

(* Rule: PKG-005 *)
(* Unknown option for geometry package *)
Module Rule_PKG_005.
  
  Definition id := "PKG-005".
  Definition description := "Unknown option for geometry package".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_005.

(* Rule: PKG-007 *)
(* hyperref loaded before geometry *)
Module Rule_PKG_007.
  
  Definition id := "PKG-007".
  Definition description := "hyperref loaded before geometry".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_007.

(* Rule: PKG-008 *)
(* xcolor loaded without dvipsnames option *)
Module Rule_PKG_008.
  
  Definition id := "PKG-008".
  Definition description := "xcolor loaded without dvipsnames option".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_008.

(* Rule: PKG-009 *)
(* TikZ libraries loaded inside document body *)
Module Rule_PKG_009.
  
  Definition id := "PKG-009".
  Definition description := "TikZ libraries loaded inside document body".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_009.

(* Rule: PKG-010 *)
(* biblatex loaded with deprecated backend=biber option *)
Module Rule_PKG_010.
  
  Definition id := "PKG-010".
  Definition description := "biblatex loaded with deprecated backend=biber option".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_010.

(* Rule: PKG-011 *)
(* booktabs package required but not loaded for \\toprule *)
Module Rule_PKG_011.
  
  Definition id := "PKG-011".
  Definition description := "booktabs package required but not loaded for \\toprule".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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
    Some (insert_usepackage_fix input).

  
End Rule_PKG_011.

(* Rule: PKG-012 *)
(* csquotes missing when \\enquote used *)
Module Rule_PKG_012.
  
  Definition id := "PKG-012".
  Definition description := "csquotes missing when \\enquote used".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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
    Some (insert_usepackage_fix input).

  
End Rule_PKG_012.

(* Rule: PKG-013 *)
(* microtype not loaded in XeLaTeX path *)
Module Rule_PKG_013.
  
  Definition id := "PKG-013".
  Definition description := "microtype not loaded in XeLaTeX path".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_013.

(* Rule: PKG-014 *)
(* siunitx outdated v2 API *)
Module Rule_PKG_014.
  
  Definition id := "PKG-014".
  Definition description := "siunitx outdated v2 API".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_014.

(* Rule: PKG-015 *)
(* Inputenc package loaded under XeLaTeX/LuaLaTeX *)
Module Rule_PKG_015.
  
  Definition id := "PKG-015".
  Definition description := "Inputenc package loaded under XeLaTeX/LuaLaTeX".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_015.

(* Rule: PKG-016 *)
(* Graphicx option pdftex in incompatible engine *)
Module Rule_PKG_016.
  
  Definition id := "PKG-016".
  Definition description := "Graphicx option pdftex in incompatible engine".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_016.

(* Rule: PKG-017 *)
(* fontspec loaded in pdfLaTeX *)
Module Rule_PKG_017.
  
  Definition id := "PKG-017".
  Definition description := "fontspec loaded in pdfLaTeX".
  Definition severity := SeverityError.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_017.

(* Rule: PKG-020 *)
(* tikz external library not loaded with externalization *)
Module Rule_PKG_020.
  
  Definition id := "PKG-020".
  Definition description := "tikz external library not loaded with externalization".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_PKG_020.

(* Rule: RTL-005 *)
(* Polyglossia RTL font not specified *)
Module Rule_RTL_005.
  
  Definition id := "RTL-005".
  Definition description := "Polyglossia RTL font not specified".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_RTL_005.

(* Rule: STRUCT-001 *)
(* Section level jumps more than one (e.g. section → subsubsection) *)
Module Rule_STRUCT_001.
  
  Definition id := "STRUCT-001".
  Definition description := "Section level jumps more than one (e.g. section → subsubsection)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_001.

(* Rule: STRUCT-002 *)
(* Section with no content *)
Module Rule_STRUCT_002.
  
  Definition id := "STRUCT-002".
  Definition description := "Section with no content".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_002.

(* Rule: STRUCT-003 *)
(* Subsection immediately followed by subsubsection without text *)
Module Rule_STRUCT_003.
  
  Definition id := "STRUCT-003".
  Definition description := "Subsection immediately followed by subsubsection without text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_003.

(* Rule: STRUCT-004 *)
(* Duplicate section titles *)
Module Rule_STRUCT_004.
  
  Definition id := "STRUCT-004".
  Definition description := "Duplicate section titles".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_004.

(* Rule: STRUCT-005 *)
(* Unnumbered section referenced with \\ref *)
Module Rule_STRUCT_005.
  
  Definition id := "STRUCT-005".
  Definition description := "Unnumbered section referenced with \\ref".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_005.

(* Rule: STRUCT-006 *)
(* Section level deeper than \\paragraph *)
Module Rule_STRUCT_006.
  
  Definition id := "STRUCT-006".
  Definition description := "Section level deeper than \\paragraph".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_006.

(* Rule: STRUCT-007 *)
(* Section heading ends with punctuation *)
Module Rule_STRUCT_007.
  
  Definition id := "STRUCT-007".
  Definition description := "Section heading ends with punctuation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_007.

(* Rule: STRUCT-008 *)
(* Appendix section before \\appendix command *)
Module Rule_STRUCT_008.
  
  Definition id := "STRUCT-008".
  Definition description := "Appendix section before \\appendix command".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_008.

(* Rule: STRUCT-009 *)
(* More than two consecutive sectionless paragraphs *)
Module Rule_STRUCT_009.
  
  Definition id := "STRUCT-009".
  Definition description := "More than two consecutive sectionless paragraphs".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_STRUCT_009.

(* Rule: TAB-001 *)
(* Table has no caption *)
Module Rule_TAB_001.
  
  Definition id := "TAB-001".
  Definition description := "Table has no caption".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_001.

(* Rule: TAB-002 *)
(* Caption below table in journal style requiring above *)
Module Rule_TAB_002.
  
  Definition id := "TAB-002".
  Definition description := "Caption below table in journal style requiring above".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_002.

(* Rule: TAB-003 *)
(* Column spec lacks decimal alignment in tabular *)
Module Rule_TAB_003.
  
  Definition id := "TAB-003".
  Definition description := "Column spec lacks decimal alignment in tabular".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_003.

(* Rule: TAB-005 *)
(* Vertical rules present in tabular *)
Module Rule_TAB_005.
  
  Definition id := "TAB-005".
  Definition description := "Vertical rules present in tabular".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_005.

(* Rule: TAB-006 *)
(* Horizontal lines \\hline double‑stacked *)
Module Rule_TAB_006.
  
  Definition id := "TAB-006".
  Definition description := "Horizontal lines \\hline double‑stacked".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_006.

(* Rule: TAB-007 *)
(* Text in numeric column not \\multicolumn *)
Module Rule_TAB_007.
  
  Definition id := "TAB-007".
  Definition description := "Text in numeric column not \\multicolumn".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_007.

(* Rule: TAB-008 *)
(* More than 30 rows in single table – suggest longtable *)
Module Rule_TAB_008.
  
  Definition id := "TAB-008".
  Definition description := "More than 30 rows in single table – suggest longtable".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_008.

(* Rule: TAB-009 *)
(* Table floating without \\label *)
Module Rule_TAB_009.
  
  Definition id := "TAB-009".
  Definition description := "Table floating without \\label".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_009.

(* Rule: TAB-010 *)
(* Footnote inside table environment *)
Module Rule_TAB_010.
  
  Definition id := "TAB-010".
  Definition description := "Footnote inside table environment".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TAB_010.

(* Rule: TIKZ-001 *)
(* TikZ picture declared outside figure environment *)
Module Rule_TIKZ_001.
  
  Definition id := "TIKZ-001".
  Definition description := "TikZ picture declared outside figure environment".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_001.

(* Rule: TIKZ-003 *)
(* pgfplots axis labels not in math mode *)
Module Rule_TIKZ_003.
  
  Definition id := "TIKZ-003".
  Definition description := "pgfplots axis labels not in math mode".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_003.

(* Rule: TIKZ-004 *)
(* Hard‑coded RGB values instead of xcolor names *)
Module Rule_TIKZ_004.
  
  Definition id := "TIKZ-004".
  Definition description := "Hard‑coded RGB values instead of xcolor names".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_004.

(* Rule: TIKZ-006 *)
(* Missing \\caption in tikzpicture inside figure *)
Module Rule_TIKZ_006.
  
  Definition id := "TIKZ-006".
  Definition description := "Missing \\caption in tikzpicture inside figure".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_006.

(* Rule: TIKZ-007 *)
(* TikZ load order after hyperref *)
Module Rule_TIKZ_007.
  
  Definition id := "TIKZ-007".
  Definition description := "TikZ load order after hyperref".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_007.

(* Rule: TIKZ-009 *)
(* TikZ library arrows.meta missing for arrow tips *)
Module Rule_TIKZ_009.
  
  Definition id := "TIKZ-009".
  Definition description := "TikZ library arrows.meta missing for arrow tips".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_009.

(* Rule: TIKZ-010 *)
(* Deprecated \\pgfplotsset key used *)
Module Rule_TIKZ_010.
  
  Definition id := "TIKZ-010".
  Definition description := "Deprecated \\pgfplotsset key used".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondAst.
  
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

  
End Rule_TIKZ_010.

(* Rule: VERB-014 *)
(* Code block inside caption *)
Module Rule_VERB_014.
  
  Definition id := "VERB-014".
  Definition description := "Code block inside caption".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondAst.
  
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

  
End Rule_VERB_014.

