(* SIGMA Rules - L3_Semantics *)
(* Auto-generated from rules_unified.yaml *)

Require Import Coq.Strings.String.
Require Import LatexAST.
Require Import ValidationTypes.

(* Rule: ACCESS-003 *)
(* No \\pdfstringdef for section with math *)
Module Rule_ACCESS_003.
  
  Definition id := "ACCESS-003".
  Definition description := "No \\pdfstringdef for section with math".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_003.

(* Rule: ACCESS-004 *)
(* Colour contrast ratio < 4.5:1 detected (xcolor) *)
Module Rule_ACCESS_004.
  
  Definition id := "ACCESS-004".
  Definition description := "Colour contrast ratio < 4.5:1 detected (xcolor)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_004.

(* Rule: ACCESS-006 *)
(* PDF lacks /Lang metadata *)
Module Rule_ACCESS_006.
  
  Definition id := "ACCESS-006".
  Definition description := "PDF lacks /Lang metadata".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_006.

(* Rule: ACCESS-007 *)
(* PDF outline depth exceeds 3 *)
Module Rule_ACCESS_007.
  
  Definition id := "ACCESS-007".
  Definition description := "PDF outline depth exceeds 3".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_007.

(* Rule: ACCESS-010 *)
(* PDF/A compliance not declared *)
Module Rule_ACCESS_010.
  
  Definition id := "ACCESS-010".
  Definition description := "PDF/A compliance not declared".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_010.

(* Rule: ACCESS-011 *)
(* No /AltActual on math objects in tagged PDF *)
Module Rule_ACCESS_011.
  
  Definition id := "ACCESS-011".
  Definition description := "No /AltActual on math objects in tagged PDF".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_011.

(* Rule: ACCESS-012 *)
(* Alt text > 100 chars lacks /AltActualLong *)
Module Rule_ACCESS_012.
  
  Definition id := "ACCESS-012".
  Definition description := "Alt text > 100 chars lacks /AltActualLong".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_012.

(* Rule: ACCESS-013 *)
(* /StructureTreeRoot missing in PDF *)
Module Rule_ACCESS_013.
  
  Definition id := "ACCESS-013".
  Definition description := "/StructureTreeRoot missing in PDF".
  Definition severity := SeverityError.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_ACCESS_013.

(* Rule: BIB-003 *)
(* Missing DOI in article entry *)
Module Rule_BIB_003.
  
  Definition id := "BIB-003".
  Definition description := "Missing DOI in article entry".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_003.

(* Rule: BIB-005 *)
(* Year field missing in entry *)
Module Rule_BIB_005.
  
  Definition id := "BIB-005".
  Definition description := "Year field missing in entry".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_005.

(* Rule: BIB-007 *)
(* Redundant author field duplicates editor *)
Module Rule_BIB_007.
  
  Definition id := "BIB-007".
  Definition description := "Redundant author field duplicates editor".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_007.

(* Rule: BIB-008 *)
(* URL present without accessed date *)
Module Rule_BIB_008.
  
  Definition id := "BIB-008".
  Definition description := "URL present without accessed date".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_008.

(* Rule: BIB-009 *)
(* Capitalisation in journal title incorrect *)
Module Rule_BIB_009.
  
  Definition id := "BIB-009".
  Definition description := "Capitalisation in journal title incorrect".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_009.

(* Rule: BIB-011 *)
(* Title sentence‑case but style requires title‑case *)
Module Rule_BIB_011.
  
  Definition id := "BIB-011".
  Definition description := "Title sentence‑case but style requires title‑case".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_011.

(* Rule: BIB-012 *)
(* DOI present but malformed *)
Module Rule_BIB_012.
  
  Definition id := "BIB-012".
  Definition description := "DOI present but malformed".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_012.

(* Rule: BIB-013 *)
(* URL uses http not https *)
Module Rule_BIB_013.
  
  Definition id := "BIB-013".
  Definition description := "URL uses http not https".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_013.

(* Rule: BIB-014 *)
(* Inconsistent en‑dash in page ranges *)
Module Rule_BIB_014.
  
  Definition id := "BIB-014".
  Definition description := "Inconsistent en‑dash in page ranges".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_014.

(* Rule: BIB-015 *)
(* Publisher missing in book entry *)
Module Rule_BIB_015.
  
  Definition id := "BIB-015".
  Definition description := "Publisher missing in book entry".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_015.

(* Rule: BIB-016 *)
(* Month field present where prohibited by style *)
Module Rule_BIB_016.
  
  Definition id := "BIB-016".
  Definition description := "Month field present where prohibited by style".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_016.

(* Rule: BIB-017 *)
(* Author list truncated manually with et al. *)
Module Rule_BIB_017.
  
  Definition id := "BIB-017".
  Definition description := "Author list truncated manually with et al.".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_017.

(* Rule: BIB-018 *)
(* journal field missing capitalisation braces *)
Module Rule_BIB_018.
  
  Definition id := "BIB-018".
  Definition description := "journal field missing capitalisation braces".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_018.

(* Rule: BIB-019 *)
(* BibTeX crossref target missing *)
Module Rule_BIB_019.
  
  Definition id := "BIB-019".
  Definition description := "BibTeX crossref target missing".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_019.

(* Rule: BIB-020 *)
(* Duplicate DOI in two entries *)
Module Rule_BIB_020.
  
  Definition id := "BIB-020".
  Definition description := "Duplicate DOI in two entries".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_BIB_020.

(* Rule: CHEM-010 *)
(* Reaction scheme exceeds page width *)
Module Rule_CHEM_010.
  
  Definition id := "CHEM-010".
  Definition description := "Reaction scheme exceeds page width".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CHEM_010.

(* Rule: CJK-003 *)
(* Japanese kinsoku forbidden line break before small kana *)
Module Rule_CJK_003.
  
  Definition id := "CJK-003".
  Definition description := "Japanese kinsoku forbidden line break before small kana".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_003.

(* Rule: CJK-005 *)
(* Mixed zh/ja CJK fonts in same paragraph *)
Module Rule_CJK_005.
  
  Definition id := "CJK-005".
  Definition description := "Mixed zh/ja CJK fonts in same paragraph".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_005.

(* Rule: CJK-007 *)
(* Kanji glyph not in selected CJK font set *)
Module Rule_CJK_007.
  
  Definition id := "CJK-007".
  Definition description := "Kanji glyph not in selected CJK font set".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_007.

(* Rule: CJK-009 *)
(* Strip Western inter‑word space between CJK glyphs *)
Module Rule_CJK_009.
  
  Definition id := "CJK-009".
  Definition description := "Strip Western inter‑word space between CJK glyphs".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_009.

(* Rule: CJK-011 *)
(* Hiragana prolonged sound mark at line start *)
Module Rule_CJK_011.
  
  Definition id := "CJK-011".
  Definition description := "Hiragana prolonged sound mark at line start".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_011.

(* Rule: CJK-012 *)
(* xeCJK spaceskip not set (expected \\xeCJKsetup) *)
Module Rule_CJK_012.
  
  Definition id := "CJK-012".
  Definition description := "xeCJK spaceskip not set (expected \\xeCJKsetup)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_012.

(* Rule: CJK-013 *)
(* Prohibited line break before full stop U+3002 *)
Module Rule_CJK_013.
  
  Definition id := "CJK-013".
  Definition description := "Prohibited line break before full stop U+3002".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_CJK_013.

(* Rule: COL-001 *)
(* CMYK image in RGB workflow *)
Module Rule_COL_001.
  
  Definition id := "COL-001".
  Definition description := "CMYK image in RGB workflow".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_COL_001.

(* Rule: COL-002 *)
(* ICC profile missing in embedded image *)
Module Rule_COL_002.
  
  Definition id := "COL-002".
  Definition description := "ICC profile missing in embedded image".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_COL_002.

(* Rule: COL-003 *)
(* Transparent PNG in print‑optimised document class *)
Module Rule_COL_003.
  
  Definition id := "COL-003".
  Definition description := "Transparent PNG in print‑optimised document class".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_COL_003.

(* Rule: COL-004 *)
(* PDF contains spot colour separation *)
Module Rule_COL_004.
  
  Definition id := "COL-004".
  Definition description := "PDF contains spot colour separation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_COL_004.

(* Rule: COL-005 *)
(* Excess distinct colours (>256) – potential print issue *)
Module Rule_COL_005.
  
  Definition id := "COL-005".
  Definition description := "Excess distinct colours (>256) – potential print issue".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_COL_005.

(* Rule: FIG-004 *)
(* Raster image exceeds 300 dpi *)
Module Rule_FIG_004.
  
  Definition id := "FIG-004".
  Definition description := "Raster image exceeds 300 dpi".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_004.

(* Rule: FIG-005 *)
(* Figure width > \\linewidth *)
Module Rule_FIG_005.
  
  Definition id := "FIG-005".
  Definition description := "Figure width > \\linewidth".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_005.

(* Rule: FIG-006 *)
(* Bitmap image with transparency channel *)
Module Rule_FIG_006.
  
  Definition id := "FIG-006".
  Definition description := "Bitmap image with transparency channel".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_006.

(* Rule: FIG-008 *)
(* TikZ figure compiled in draft mode *)
Module Rule_FIG_008.
  
  Definition id := "FIG-008".
  Definition description := "TikZ figure compiled in draft mode".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_008.

(* Rule: FIG-011 *)
(* EPS graphic in pdfLaTeX run *)
Module Rule_FIG_011.
  
  Definition id := "FIG-011".
  Definition description := "EPS graphic in pdfLaTeX run".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_011.

(* Rule: FIG-015 *)
(* Figure placed before first reference in text *)
Module Rule_FIG_015.
  
  Definition id := "FIG-015".
  Definition description := "Figure placed before first reference in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_015.

(* Rule: FIG-016 *)
(* Raster image colour profile not sRGB *)
Module Rule_FIG_016.
  
  Definition id := "FIG-016".
  Definition description := "Raster image colour profile not sRGB".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_016.

(* Rule: FIG-018 *)
(* Float figure too far from reference (>3 pages) *)
Module Rule_FIG_018.
  
  Definition id := "FIG-018".
  Definition description := "Float figure too far from reference (>3 pages)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_018.

(* Rule: FIG-020 *)
(* Overfull \\hbox within figure caption *)
Module Rule_FIG_020.
  
  Definition id := "FIG-020".
  Definition description := "Overfull \\hbox within figure caption".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FIG_020.

(* Rule: FONT-002 *)
(* Mixed optical sizes (e.g. 8pt + 12pt) in same paragraph *)
Module Rule_FONT_002.
  
  Definition id := "FONT-002".
  Definition description := "Mixed optical sizes (e.g. 8pt + 12pt) in same paragraph".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FONT_002.

(* Rule: FONT-003 *)
(* Microtype protrusion disabled globally *)
Module Rule_FONT_003.
  
  Definition id := "FONT-003".
  Definition description := "Microtype protrusion disabled globally".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FONT_003.

(* Rule: FONT-005 *)
(* Fontspec fallback to Latin Modern detected *)
Module Rule_FONT_005.
  
  Definition id := "FONT-005".
  Definition description := "Fontspec fallback to Latin Modern detected".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_FONT_005.

(* Rule: LANG-005 *)
(* Wrong hyphenation exception \\hyphenpenalty too low *)
Module Rule_LANG_005.
  
  Definition id := "LANG-005".
  Definition description := "Wrong hyphenation exception \\hyphenpenalty too low".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LANG_005.

(* Rule: LANG-009 *)
(* Raggedright text in non‑Latin script *)
Module Rule_LANG_009.
  
  Definition id := "LANG-009".
  Definition description := "Raggedright text in non‑Latin script".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LANG_009.

(* Rule: LANG-010 *)
(* Arabic digits in RTL context not localised *)
Module Rule_LANG_010.
  
  Definition id := "LANG-010".
  Definition description := "Arabic digits in RTL context not localised".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LANG_010.

(* Rule: LAY-001 *)
(* Overfull \\hbox > 2 pt outside bibliography *)
Module Rule_LAY_001.
  
  Definition id := "LAY-001".
  Definition description := "Overfull \\hbox > 2 pt outside bibliography".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_001.

(* Rule: LAY-002 *)
(* Widow or orphan line detected after compile *)
Module Rule_LAY_002.
  
  Definition id := "LAY-002".
  Definition description := "Widow or orphan line detected after compile".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_002.

(* Rule: LAY-003 *)
(* Section heading at bottom of page *)
Module Rule_LAY_003.
  
  Definition id := "LAY-003".
  Definition description := "Section heading at bottom of page".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_003.

(* Rule: LAY-004 *)
(* Page margin outside geometry limits *)
Module Rule_LAY_004.
  
  Definition id := "LAY-004".
  Definition description := "Page margin outside geometry limits".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_004.

(* Rule: LAY-005 *)
(* Lines per page exceed 66 *)
Module Rule_LAY_005.
  
  Definition id := "LAY-005".
  Definition description := "Lines per page exceed 66".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_005.

(* Rule: LAY-006 *)
(* Float too close to previous float (less than 2 lines) *)
Module Rule_LAY_006.
  
  Definition id := "LAY-006".
  Definition description := "Float too close to previous float (less than 2 lines)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_006.

(* Rule: LAY-007 *)
(* Paragraph indent inconsistent after display math *)
Module Rule_LAY_007.
  
  Definition id := "LAY-007".
  Definition description := "Paragraph indent inconsistent after display math".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_007.

(* Rule: LAY-008 *)
(* Heading left aligned but style requires centred *)
Module Rule_LAY_008.
  
  Definition id := "LAY-008".
  Definition description := "Heading left aligned but style requires centred".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_008.

(* Rule: LAY-009 *)
(* Footnote overlaps bottom margin *)
Module Rule_LAY_009.
  
  Definition id := "LAY-009".
  Definition description := "Footnote overlaps bottom margin".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_009.

(* Rule: LAY-010 *)
(* Page number suppressed on chapter opening page but required *)
Module Rule_LAY_010.
  
  Definition id := "LAY-010".
  Definition description := "Page number suppressed on chapter opening page but required".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_010.

(* Rule: LAY-011 *)
(* Figure overlaps footer (compile log warning) *)
Module Rule_LAY_011.
  
  Definition id := "LAY-011".
  Definition description := "Figure overlaps footer (compile log warning)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_011.

(* Rule: LAY-012 *)
(* Chapter starts on even page but style requires odd *)
Module Rule_LAY_012.
  
  Definition id := "LAY-012".
  Definition description := "Chapter starts on even page but style requires odd".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_012.

(* Rule: LAY-013 *)
(* Empty page without \\thispagestyle{empty} *)
Module Rule_LAY_013.
  
  Definition id := "LAY-013".
  Definition description := "Empty page without \\thispagestyle{empty}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_013.

(* Rule: LAY-014 *)
(* Page break before subsection discouraged *)
Module Rule_LAY_014.
  
  Definition id := "LAY-014".
  Definition description := "Page break before subsection discouraged".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_014.

(* Rule: LAY-015 *)
(* Line spacing <1.0 or >2.0 *)
Module Rule_LAY_015.
  
  Definition id := "LAY-015".
  Definition description := "Line spacing <1.0 or >2.0".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_015.

(* Rule: LAY-016 *)
(* Table spread across page break without \\allowbreak *)
Module Rule_LAY_016.
  
  Definition id := "LAY-016".
  Definition description := "Table spread across page break without \\allowbreak".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_016.

(* Rule: LAY-017 *)
(* Section heading orphaned at page top *)
Module Rule_LAY_017.
  
  Definition id := "LAY-017".
  Definition description := "Section heading orphaned at page top".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_017.

(* Rule: LAY-018 *)
(* Underfull \\vbox warning in log *)
Module Rule_LAY_018.
  
  Definition id := "LAY-018".
  Definition description := "Underfull \\vbox warning in log".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_018.

(* Rule: LAY-019 *)
(* Wide margin note exceeds marginpar width *)
Module Rule_LAY_019.
  
  Definition id := "LAY-019".
  Definition description := "Wide margin note exceeds marginpar width".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_019.

(* Rule: LAY-020 *)
(* Float placement parameters altered (\\setcounter{topnumber}) *)
Module Rule_LAY_020.
  
  Definition id := "LAY-020".
  Definition description := "Float placement parameters altered (\\setcounter{topnumber})".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_LAY_020.

(* Rule: MATH-026 *)
(* Overfull \\hbox in equation detected in log *)
Module Rule_MATH_026.
  
  Definition id := "MATH-026".
  Definition description := "Overfull \\hbox in equation detected in log".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_MATH_026.

(* Rule: MATH-027 *)
(* Displayed equation exceeding page margins after compile *)
Module Rule_MATH_027.
  
  Definition id := "MATH-027".
  Definition description := "Displayed equation exceeding page margins after compile".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_MATH_027.

(* Rule: MATH-076 *)
(* Equation split across pages without \\allowbreak *)
Module Rule_MATH_076.
  
  Definition id := "MATH-076".
  Definition description := "Equation split across pages without \\allowbreak".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_MATH_076.

(* Rule: META-001 *)
(* PDF /Producer string not set to deterministic hash *)
Module Rule_META_001.
  
  Definition id := "META-001".
  Definition description := "PDF /Producer string not set to deterministic hash".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_META_001.

(* Rule: META-003 *)
(* Build timestamp not reproducible *)
Module Rule_META_003.
  
  Definition id := "META-003".
  Definition description := "Build timestamp not reproducible".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_META_003.

(* Rule: PKG-003 *)
(* Incompatible options for microtype with LuaTeX *)
Module Rule_PKG_003.
  
  Definition id := "PKG-003".
  Definition description := "Incompatible options for microtype with LuaTeX".
  Definition severity := SeverityError.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_PKG_003.

(* Rule: PKG-006 *)
(* microtype expansion disabled *)
Module Rule_PKG_006.
  
  Definition id := "PKG-006".
  Definition description := "microtype expansion disabled".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_PKG_006.

(* Rule: PKG-018 *)
(* hyperref option draft left enabled *)
Module Rule_PKG_018.
  
  Definition id := "PKG-018".
  Definition description := "hyperref option draft left enabled".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_PKG_018.

(* Rule: PKG-019 *)
(* geometry package margin < 1 cm *)
Module Rule_PKG_019.
  
  Definition id := "PKG-019".
  Definition description := "geometry package margin < 1 cm".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_PKG_019.

(* Rule: REF-008 *)
(* Cite key duplicated in .bib file *)
Module Rule_REF_008.
  
  Definition id := "REF-008".
  Definition description := "Cite key duplicated in .bib file".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_REF_008.

(* Rule: REF-010 *)
(* Figure referenced before first mention in text *)
Module Rule_REF_010.
  
  Definition id := "REF-010".
  Definition description := "Figure referenced before first mention in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_REF_010.

(* Rule: REF-019 *)
(* Citation key used but not present in .bib *)
Module Rule_REF_019.
  
  Definition id := "REF-019".
  Definition description := "Citation key used but not present in .bib".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_REF_019.

(* Rule: RTL-001 *)
(* Mixture of RTL and LTR digits in same number *)
Module Rule_RTL_001.
  
  Definition id := "RTL-001".
  Definition description := "Mixture of RTL and LTR digits in same number".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_RTL_001.

(* Rule: RTL-002 *)
(* Missing \\textLR around Latin acronym in Arabic text *)
Module Rule_RTL_002.
  
  Definition id := "RTL-002".
  Definition description := "Missing \\textLR around Latin acronym in Arabic text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_RTL_002.

(* Rule: SEC-002 *)
(* Graphic file checksum mismatch vs manifest *)
Module Rule_SEC_002.
  
  Definition id := "SEC-002".
  Definition description := "Graphic file checksum mismatch vs manifest".
  Definition severity := SeverityError.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_SEC_002.

(* Rule: TAB-004 *)
(* Table width exceeds \\textwidth *)
Module Rule_TAB_004.
  
  Definition id := "TAB-004".
  Definition description := "Table width exceeds \\textwidth".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_TAB_004.

(* Rule: TIKZ-002 *)
(* TikZ compile time > 5 s *)
Module Rule_TIKZ_002.
  
  Definition id := "TIKZ-002".
  Definition description := "TikZ compile time > 5 s".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_TIKZ_002.

(* Rule: TIKZ-005 *)
(* TikZ externalisation not enabled for large figures *)
Module Rule_TIKZ_005.
  
  Definition id := "TIKZ-005".
  Definition description := "TikZ externalisation not enabled for large figures".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_TIKZ_005.

(* Rule: TIKZ-008 *)
(* Uncompressed pdf images generated by TikZ *)
Module Rule_TIKZ_008.
  
  Definition id := "TIKZ-008".
  Definition description := "Uncompressed pdf images generated by TikZ".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondSemantics.
  
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

  
End Rule_TIKZ_008.

