(* SIGMA Rules - L4_Style *)
(* Auto-generated from rules_unified.yaml *)

Require Import Coq.Strings.String.
Require Import LatexAST.
Require Import ValidationTypes.

(* Rule: LANG-003 *)
(* Mixed French and English punctuation spacing *)
Module Rule_LANG_003.
  
  Definition id := "LANG-003".
  Definition description := "Mixed French and English punctuation spacing".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_LANG_003.

(* Rule: LANG-008 *)
(* Spell‑checking dictionary differs from babel option *)
Module Rule_LANG_008.
  
  Definition id := "LANG-008".
  Definition description := "Spell‑checking dictionary differs from babel option".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_LANG_008.

(* Rule: STRUCT-010 *)
(* Chapter length imbalance > 3× *)
Module Rule_STRUCT_010.
  
  Definition id := "STRUCT-010".
  Definition description := "Chapter length imbalance > 3×".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STRUCT_010.

(* Rule: STYLE-001 *)
(* Inconsistent Oxford comma usage *)
Module Rule_STYLE_001.
  
  Definition id := "STYLE-001".
  Definition description := "Inconsistent Oxford comma usage".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_001.

(* Rule: STYLE-002 *)
(* Mixed UK and US spelling *)
Module Rule_STYLE_002.
  
  Definition id := "STYLE-002".
  Definition description := "Mixed UK and US spelling".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_002.

(* Rule: STYLE-003 *)
(* Passive voice over 20 % of sentences *)
Module Rule_STYLE_003.
  
  Definition id := "STYLE-003".
  Definition description := "Passive voice over 20 % of sentences".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_003.

(* Rule: STYLE-004 *)
(* Paragraph exceeds 300 words *)
Module Rule_STYLE_004.
  
  Definition id := "STYLE-004".
  Definition description := "Paragraph exceeds 300 words".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_004.

(* Rule: STYLE-005 *)
(* First‑person pronoun 'we' inconsistent *)
Module Rule_STYLE_005.
  
  Definition id := "STYLE-005".
  Definition description := "First‑person pronoun 'we' inconsistent".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_005.

(* Rule: STYLE-006 *)
(* Consecutive sentences start with same word *)
Module Rule_STYLE_006.
  
  Definition id := "STYLE-006".
  Definition description := "Consecutive sentences start with same word".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_006.

(* Rule: STYLE-007 *)
(* Bullet list items inconsistent punctuation *)
Module Rule_STYLE_007.
  
  Definition id := "STYLE-007".
  Definition description := "Bullet list items inconsistent punctuation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_007.

(* Rule: STYLE-008 *)
(* Sentence starts with mathematical symbol *)
Module Rule_STYLE_008.
  
  Definition id := "STYLE-008".
  Definition description := "Sentence starts with mathematical symbol".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_008.

(* Rule: STYLE-009 *)
(* Citation style mixes parenthetical and narrative *)
Module Rule_STYLE_009.
  
  Definition id := "STYLE-009".
  Definition description := "Citation style mixes parenthetical and narrative".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_009.

(* Rule: STYLE-010 *)
(* First person singular 'I' in multi‑author paper *)
Module Rule_STYLE_010.
  
  Definition id := "STYLE-010".
  Definition description := "First person singular 'I' in multi‑author paper".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_010.

(* Rule: STYLE-011 *)
(* Hyphen vs en‑dash inconsistency in ranges *)
Module Rule_STYLE_011.
  
  Definition id := "STYLE-011".
  Definition description := "Hyphen vs en‑dash inconsistency in ranges".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_011.

(* Rule: STYLE-012 *)
(* That/which relative clause misuse *)
Module Rule_STYLE_012.
  
  Definition id := "STYLE-012".
  Definition description := "That/which relative clause misuse".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_012.

(* Rule: STYLE-013 *)
(* Sentence starts with numeric figure *)
Module Rule_STYLE_013.
  
  Definition id := "STYLE-013".
  Definition description := "Sentence starts with numeric figure".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_013.

(* Rule: STYLE-014 *)
(* Contraction (don't, isn't) in formal text *)
Module Rule_STYLE_014.
  
  Definition id := "STYLE-014".
  Definition description := "Contraction (don't, isn't) in formal text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_014.

(* Rule: STYLE-015 *)
(* Double space after period *)
Module Rule_STYLE_015.
  
  Definition id := "STYLE-015".
  Definition description := "Double space after period".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_STYLE_015.

(* Rule: STYLE-016 *)
(* Latin abbreviations (e.g., i.e., etc.) without comma *)
Module Rule_STYLE_016.
  
  Definition id := "STYLE-016".
  Definition description := "Latin abbreviations (e.g., i.e., etc.) without comma".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_016.

(* Rule: STYLE-017 *)
(* Sentence exceeding 40 words *)
Module Rule_STYLE_017.
  
  Definition id := "STYLE-017".
  Definition description := "Sentence exceeding 40 words".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_017.

(* Rule: STYLE-018 *)
(* Dangling reference word 'this' *)
Module Rule_STYLE_018.
  
  Definition id := "STYLE-018".
  Definition description := "Dangling reference word 'this'".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_018.

(* Rule: STYLE-019 *)
(* Multiple consecutive headings without text *)
Module Rule_STYLE_019.
  
  Definition id := "STYLE-019".
  Definition description := "Multiple consecutive headings without text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_019.

(* Rule: STYLE-020 *)
(* Acronym defined but never used *)
Module Rule_STYLE_020.
  
  Definition id := "STYLE-020".
  Definition description := "Acronym defined but never used".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_020.

(* Rule: STYLE-021 *)
(* Acronym used before definition *)
Module Rule_STYLE_021.
  
  Definition id := "STYLE-021".
  Definition description := "Acronym used before definition".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_021.

(* Rule: STYLE-022 *)
(* Serial comma missing in three‑item list *)
Module Rule_STYLE_022.
  
  Definition id := "STYLE-022".
  Definition description := "Serial comma missing in three‑item list".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_022.

(* Rule: STYLE-023 *)
(* Percent sign in text not escaped *)
Module Rule_STYLE_023.
  
  Definition id := "STYLE-023".
  Definition description := "Percent sign in text not escaped".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_STYLE_023.

(* Rule: STYLE-024 *)
(* Ampersand in author list not escaped \\& *)
Module Rule_STYLE_024.
  
  Definition id := "STYLE-024".
  Definition description := "Ampersand in author list not escaped \\&".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_STYLE_024.

(* Rule: STYLE-025 *)
(* Run‑on sentence detected *)
Module Rule_STYLE_025.
  
  Definition id := "STYLE-025".
  Definition description := "Run‑on sentence detected".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_025.

(* Rule: STYLE-026 *)
(* Repeated word (the the) *)
Module Rule_STYLE_026.
  
  Definition id := "STYLE-026".
  Definition description := "Repeated word (the the)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_026.

(* Rule: STYLE-027 *)
(* Overuse of adverbs (-ly >5 % of words) *)
Module Rule_STYLE_027.
  
  Definition id := "STYLE-027".
  Definition description := "Overuse of adverbs (-ly >5 % of words)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_027.

(* Rule: STYLE-028 *)
(* Equation referenced without adjoining punctuation *)
Module Rule_STYLE_028.
  
  Definition id := "STYLE-028".
  Definition description := "Equation referenced without adjoining punctuation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_028.

(* Rule: STYLE-029 *)
(* First‑person plural 'we' not defined (author vs generic) *)
Module Rule_STYLE_029.
  
  Definition id := "STYLE-029".
  Definition description := "First‑person plural 'we' not defined (author vs generic)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_029.

(* Rule: STYLE-030 *)
(* Subheading capitalisation inconsistent *)
Module Rule_STYLE_030.
  
  Definition id := "STYLE-030".
  Definition description := "Subheading capitalisation inconsistent".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_030.

(* Rule: STYLE-031 *)
(* Heading number without title *)
Module Rule_STYLE_031.
  
  Definition id := "STYLE-031".
  Definition description := "Heading number without title".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_031.

(* Rule: STYLE-032 *)
(* Bullet list mixed sentence‑case and title‑case *)
Module Rule_STYLE_032.
  
  Definition id := "STYLE-032".
  Definition description := "Bullet list mixed sentence‑case and title‑case".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_032.

(* Rule: STYLE-033 *)
(* Space before citation bracket *)
Module Rule_STYLE_033.
  
  Definition id := "STYLE-033".
  Definition description := "Space before citation bracket".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_STYLE_033.

(* Rule: STYLE-034 *)
(* Orphan word at paragraph end (1‑2 letters) *)
Module Rule_STYLE_034.
  
  Definition id := "STYLE-034".
  Definition description := "Orphan word at paragraph end (1‑2 letters)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_034.

(* Rule: STYLE-035 *)
(* Text uses slash for 'and/or' *)
Module Rule_STYLE_035.
  
  Definition id := "STYLE-035".
  Definition description := "Text uses slash for 'and/or'".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_035.

(* Rule: STYLE-036 *)
(* Latin phrase (cf., ibid.) not italicised *)
Module Rule_STYLE_036.
  
  Definition id := "STYLE-036".
  Definition description := "Latin phrase (cf., ibid.) not italicised".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_036.

(* Rule: STYLE-037 *)
(* Sentence starts with conjunction 'And' or 'But' *)
Module Rule_STYLE_037.
  
  Definition id := "STYLE-037".
  Definition description := "Sentence starts with conjunction 'And' or 'But'".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_037.

(* Rule: STYLE-038 *)
(* Footnote paragraph exceeds 80 words *)
Module Rule_STYLE_038.
  
  Definition id := "STYLE-038".
  Definition description := "Footnote paragraph exceeds 80 words".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_038.

(* Rule: STYLE-039 *)
(* Figure captions inconsistent ending punctuation *)
Module Rule_STYLE_039.
  
  Definition id := "STYLE-039".
  Definition description := "Figure captions inconsistent ending punctuation".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_039.

(* Rule: STYLE-040 *)
(* Exclamation mark in academic prose *)
Module Rule_STYLE_040.
  
  Definition id := "STYLE-040".
  Definition description := "Exclamation mark in academic prose".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_STYLE_040.

(* Rule: TYPO-050 *)
(* Title‑case choice inconsistent within document *)
Module Rule_TYPO_050.
  
  Definition id := "TYPO-050".
  Definition description := "Title‑case choice inconsistent within document".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondStyle.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_050.

