(* SIGMA Rules - L0_Lexer *)
(* Auto-generated from rules_unified.yaml *)

Require Import Coq.Strings.String.
Require Import LatexAST.
Require Import ValidationTypes.

(* Rule: CHAR-005 *)
(* Control characters U+0000–001F present *)
Module Rule_CHAR_005.
  
  Definition id := "CHAR-005".
  Definition description := "Control characters U+0000–001F present".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x1F\x7F]").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_005.

(* Rule: CHAR-006 *)
(* Backspace U+0008 character in file *)
Module Rule_CHAR_006.
  
  Definition id := "CHAR-006".
  Definition description := "Backspace U+0008 character in file".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x1F\x7F]").
  
  (* Validation function *)
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

  
End Rule_CHAR_006.

(* Rule: CHAR-007 *)
(* Bell/alert U+0007 character in file *)
Module Rule_CHAR_007.
  
  Definition id := "CHAR-007".
  Definition description := "Bell/alert U+0007 character in file".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_CHAR_007.

(* Rule: CHAR-008 *)
(* Form feed U+000C present *)
Module Rule_CHAR_008.
  
  Definition id := "CHAR-008".
  Definition description := "Form feed U+000C present".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_CHAR_008.

(* Rule: CHAR-009 *)
(* Delete U+007F (DEL) present *)
Module Rule_CHAR_009.
  
  Definition id := "CHAR-009".
  Definition description := "Delete U+007F (DEL) present".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_CHAR_009.

(* Rule: CHAR-010 *)
(* Right‑to‑left mark U+200F outside RTL language context *)
Module Rule_CHAR_010.
  
  Definition id := "CHAR-010".
  Definition description := "Right‑to‑left mark U+200F outside RTL language context".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_010.

(* Rule: CHAR-011 *)
(* Left‑to‑right mark U+200E superfluous *)
Module Rule_CHAR_011.
  
  Definition id := "CHAR-011".
  Definition description := "Left‑to‑right mark U+200E superfluous".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_011.

(* Rule: CHAR-012 *)
(* Zero‑width joiner U+200D outside ligature context *)
Module Rule_CHAR_012.
  
  Definition id := "CHAR-012".
  Definition description := "Zero‑width joiner U+200D outside ligature context".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_CHAR_012.

(* Rule: CHAR-013 *)
(* Bidirectional isolate characters U+2066‑U+2069 present *)
Module Rule_CHAR_013.
  
  Definition id := "CHAR-013".
  Definition description := "Bidirectional isolate characters U+2066‑U+2069 present".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_CHAR_013.

(* Rule: CHAR-014 *)
(* Unicode replacement � found – indicates decoding error *)
Module Rule_CHAR_014.
  
  Definition id := "CHAR-014".
  Definition description := "Unicode replacement � found – indicates decoding error".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[^\x00-\x7F]").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_014.

(* Rule: CHAR-015 *)
(* Emoji detected in source *)
Module Rule_CHAR_015.
  
  Definition id := "CHAR-015".
  Definition description := "Emoji detected in source".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_015.

(* Rule: CHAR-016 *)
(* Double‑width CJK punctuation used in ASCII context *)
Module Rule_CHAR_016.
  
  Definition id := "CHAR-016".
  Definition description := "Double‑width CJK punctuation used in ASCII context".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_016.

(* Rule: CHAR-017 *)
(* Full‑width Latin letters detected *)
Module Rule_CHAR_017.
  
  Definition id := "CHAR-017".
  Definition description := "Full‑width Latin letters detected".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_CHAR_017.

(* Rule: CHAR-018 *)
(* Deprecated ligature ﬀ, ﬁ, ﬂ characters *)
Module Rule_CHAR_018.
  
  Definition id := "CHAR-018".
  Definition description := "Deprecated ligature ﬀ, ﬁ, ﬂ characters".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_CHAR_018.

(* Rule: CHAR-019 *)
(* Non‑standard minus sign U+2212 in text *)
Module Rule_CHAR_019.
  
  Definition id := "CHAR-019".
  Definition description := "Non‑standard minus sign U+2212 in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_CHAR_019.

(* Rule: CHAR-020 *)
(* Sharp S ß in uppercase context – suggest SS *)
Module Rule_CHAR_020.
  
  Definition id := "CHAR-020".
  Definition description := "Sharp S ß in uppercase context – suggest SS".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CHAR_020.

(* Rule: CJK-001 *)
(* Full‑width comma U+FF0C in ASCII context *)
Module Rule_CJK_001.
  
  Definition id := "CJK-001".
  Definition description := "Full‑width comma U+FF0C in ASCII context".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_CJK_001.

(* Rule: CJK-002 *)
(* Full‑width period U+FF0E in ASCII context *)
Module Rule_CJK_002.
  
  Definition id := "CJK-002".
  Definition description := "Full‑width period U+FF0E in ASCII context".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_CJK_002.

(* Rule: CJK-010 *)
(* CJK punctuation half‑width variant outside ASCII *)
Module Rule_CJK_010.
  
  Definition id := "CJK-010".
  Definition description := "CJK punctuation half‑width variant outside ASCII".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[.,;:!?]").
  
  (* Validation function *)
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

  
End Rule_CJK_010.

(* Rule: CJK-014 *)
(* Japanese inter‑punct U+30FB used outside CJK run *)
Module Rule_CJK_014.
  
  Definition id := "CJK-014".
  Definition description := "Japanese inter‑punct U+30FB used outside CJK run".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_CJK_014.

(* Rule: CMD-002 *)
(* Command redefined with \\def instead of \\renewcommand *)
Module Rule_CMD_002.
  
  Definition id := "CMD-002".
  Definition description := "Command redefined with \\def instead of \\renewcommand".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_CMD_002.

(* Rule: CMD-004 *)
(* CamelCase command names discouraged *)
Module Rule_CMD_004.
  
  Definition id := "CMD-004".
  Definition description := "CamelCase command names discouraged".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_004.

(* Rule: CMD-005 *)
(* Single‑letter macro created (\\x) *)
Module Rule_CMD_005.
  
  Definition id := "CMD-005".
  Definition description := "Single‑letter macro created (\\x)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_005.

(* Rule: CMD-006 *)
(* Macro defined inside document body *)
Module Rule_CMD_006.
  
  Definition id := "CMD-006".
  Definition description := "Macro defined inside document body".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_006.

(* Rule: CMD-008 *)
(* Macro uses \\@ in name without maketitle context *)
Module Rule_CMD_008.
  
  Definition id := "CMD-008".
  Definition description := "Macro uses \\@ in name without maketitle context".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_008.

(* Rule: CMD-009 *)
(* Macro name contains digits *)
Module Rule_CMD_009.
  
  Definition id := "CMD-009".
  Definition description := "Macro name contains digits".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_CMD_009.

(* Rule: ENC-001 *)
(* Non‑UTF‑8 byte sequence detected *)
Module Rule_ENC_001.
  
  Definition id := "ENC-001".
  Definition description := "Non‑UTF‑8 byte sequence detected".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "^\ufeff").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_001.

(* Rule: ENC-002 *)
(* Byte‑order‑mark U+FEFF present in middle of file *)
Module Rule_ENC_002.
  
  Definition id := "ENC-002".
  Definition description := "Byte‑order‑mark U+FEFF present in middle of file".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[^\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_ENC_002.

(* Rule: ENC-003 *)
(* LATIN‑1 smart quotes detected *)
Module Rule_ENC_003.
  
  Definition id := "ENC-003".
  Definition description := "LATIN‑1 smart quotes detected".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[^\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_ENC_003.

(* Rule: ENC-004 *)
(* Windows‑1252 characters (– — …) outside UTF‑8 *)
Module Rule_ENC_004.
  
  Definition id := "ENC-004".
  Definition description := "Windows‑1252 characters (– — …) outside UTF‑8".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_ENC_004.

(* Rule: ENC-005 *)
(* Invalid UTF‑8 continuation byte *)
Module Rule_ENC_005.
  
  Definition id := "ENC-005".
  Definition description := "Invalid UTF‑8 continuation byte".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_005.

(* Rule: ENC-006 *)
(* Overlong UTF‑8 encoding sequence *)
Module Rule_ENC_006.
  
  Definition id := "ENC-006".
  Definition description := "Overlong UTF‑8 encoding sequence".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\over(?:\s|[^a-zA-Z])").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_006.

(* Rule: ENC-007 *)
(* Deprecated Unicode U+200B zero‑width space *)
Module Rule_ENC_007.
  
  Definition id := "ENC-007".
  Definition description := "Deprecated Unicode U+200B zero‑width space".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[^\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_ENC_007.

(* Rule: ENC-008 *)
(* Private‑use codepoint detected *)
Module Rule_ENC_008.
  
  Definition id := "ENC-008".
  Definition description := "Private‑use codepoint detected".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{lstlisting\}.*?\\end\{lstlisting\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_008.

(* Rule: ENC-009 *)
(* Unpaired surrogate code unit *)
Module Rule_ENC_009.
  
  Definition id := "ENC-009".
  Definition description := "Unpaired surrogate code unit".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{lstlisting\}.*?\\end\{lstlisting\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_009.

(* Rule: ENC-010 *)
(* Non‑canonical NFC form *)
Module Rule_ENC_010.
  
  Definition id := "ENC-010".
  Definition description := "Non‑canonical NFC form".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_ENC_010.

(* Rule: ENC-011 *)
(* Byte sequence looks like MacRoman encoding *)
Module Rule_ENC_011.
  
  Definition id := "ENC-011".
  Definition description := "Byte sequence looks like MacRoman encoding".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_ENC_011.

(* Rule: ENC-012 *)
(* C1 control characters U+0080–009F *)
Module Rule_ENC_012.
  
  Definition id := "ENC-012".
  Definition description := "C1 control characters U+0080–009F".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x1F\x7F]").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_012.

(* Rule: ENC-013 *)
(* Mixed line endings CRLF and LF in same file *)
Module Rule_ENC_013.
  
  Definition id := "ENC-013".
  Definition description := "Mixed line endings CRLF and LF in same file".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{([^}]+)\}.*?\\end\{\1\}").
  
  (* Validation function *)
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

  
End Rule_ENC_013.

(* Rule: ENC-014 *)
(* UTF‑16 byte order mark present *)
Module Rule_ENC_014.
  
  Definition id := "ENC-014".
  Definition description := "UTF‑16 byte order mark present".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "^\ufeff").
  
  (* Validation function *)
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

  
End Rule_ENC_014.

(* Rule: ENC-015 *)
(* Non‑NFKC homoglyph characters (Greek mu vs µ) *)
Module Rule_ENC_015.
  
  Definition id := "ENC-015".
  Definition description := "Non‑NFKC homoglyph characters (Greek mu vs µ)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_ENC_015.

(* Rule: ENC-016 *)
(* Arabic numerals replaced by Unicode look‑alikes *)
Module Rule_ENC_016.
  
  Definition id := "ENC-016".
  Definition description := "Arabic numerals replaced by Unicode look‑alikes".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[^\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_ENC_016.

(* Rule: ENC-017 *)
(* Soft hyphen U+00AD found in source *)
Module Rule_ENC_017.
  
  Definition id := "ENC-017".
  Definition description := "Soft hyphen U+00AD found in source".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_ENC_017.

(* Rule: ENC-018 *)
(* Non‑breaking hyphen U+2011 – discourage except in URLs *)
Module Rule_ENC_018.
  
  Definition id := "ENC-018".
  Definition description := "Non‑breaking hyphen U+2011 – discourage except in URLs".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\url\{[^}]+\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_ENC_018.

(* Rule: ENC-019 *)
(* Duplicate combining accents on same base glyph *)
Module Rule_ENC_019.
  
  Definition id := "ENC-019".
  Definition description := "Duplicate combining accents on same base glyph".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_ENC_019.

(* Rule: ENC-020 *)
(* Invisible formatting mark U+200E / U+200F present *)
Module Rule_ENC_020.
  
  Definition id := "ENC-020".
  Definition description := "Invisible formatting mark U+200E / U+200F present".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_ENC_020.

(* Rule: MATH-083 *)
(* Unicode minus inside text mode *)
Module Rule_MATH_083.
  
  Definition id := "MATH-083".
  Definition description := "Unicode minus inside text mode".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[−‐‑]").
  
  (* Validation function *)
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

  
End Rule_MATH_083.

(* Rule: SEC-001 *)
(* \\write18 detected (even in comments) *)
Module Rule_SEC_001.
  
  Definition id := "SEC-001".
  Definition description := "\\write18 detected (even in comments)".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\(sub)*(section|chapter)\{[^}]+\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SEC_001.

(* Rule: SEC-003 *)
(* Input path points to /dev or /proc *)
Module Rule_SEC_003.
  
  Definition id := "SEC-003".
  Definition description := "Input path points to /dev or /proc".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\(sub)*(section|chapter)\{[^}]+\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SEC_003.

(* Rule: SPC-001 *)
(* Line longer than 120 characters *)
Module Rule_SPC_001.
  
  Definition id := "SPC-001".
  Definition description := "Line longer than 120 characters".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "  +").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SPC_001.

(* Rule: SPC-002 *)
(* Lines with only whitespace *)
Module Rule_SPC_002.
  
  Definition id := "SPC-002".
  Definition description := "Lines with only whitespace".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "  +").
  
  (* Validation function *)
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

  
End Rule_SPC_002.

(* Rule: SPC-003 *)
(* Hard tab precedes non‑tab text *)
Module Rule_SPC_003.
  
  Definition id := "SPC-003".
  Definition description := "Hard tab precedes non‑tab text".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
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
    Some (convert_tabs_fix input).

  
End Rule_SPC_003.

(* Rule: SPC-004 *)
(* Carriage return characters CR (U+000D) lone *)
Module Rule_SPC_004.
  
  Definition id := "SPC-004".
  Definition description := "Carriage return characters CR (U+000D) lone".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[\x00-\x7F]").
  
  (* Validation function *)
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

  
End Rule_SPC_004.

(* Rule: SPC-005 *)
(* Trailing tab at end of line *)
Module Rule_SPC_005.
  
  Definition id := "SPC-005".
  Definition description := "Trailing tab at end of line".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
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
    Some (convert_tabs_fix input).

  
End Rule_SPC_005.

(* Rule: SPC-006 *)
(* Indentation mixes spaces and tabs *)
Module Rule_SPC_006.
  
  Definition id := "SPC-006".
  Definition description := "Indentation mixes spaces and tabs".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
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
    Some (convert_tabs_fix input).

  
End Rule_SPC_006.

(* Rule: SPC-007 *)
(* Three or more consecutive blank lines *)
Module Rule_SPC_007.
  
  Definition id := "SPC-007".
  Definition description := "Three or more consecutive blank lines".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_SPC_007.

(* Rule: SPC-008 *)
(* Paragraph starts with whitespace *)
Module Rule_SPC_008.
  
  Definition id := "SPC-008".
  Definition description := "Paragraph starts with whitespace".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_008.

(* Rule: SPC-009 *)
(* Non‑breaking space ~ at line start *)
Module Rule_SPC_009.
  
  Definition id := "SPC-009".
  Definition description := "Non‑breaking space ~ at line start".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_009.

(* Rule: SPC-010 *)
(* Sentence spacing uses two spaces after period *)
Module Rule_SPC_010.
  
  Definition id := "SPC-010".
  Definition description := "Sentence spacing uses two spaces after period".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\\[\s+[^\]]*\s+\\\]").
  
  (* Validation function *)
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

  
End Rule_SPC_010.

(* Rule: SPC-011 *)
(* Space before newline inside math display $$ *)
Module Rule_SPC_011.
  
  Definition id := "SPC-011".
  Definition description := "Space before newline inside math display $$".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\$[^$]+\$").
  
  (* Validation function *)
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

  
End Rule_SPC_011.

(* Rule: SPC-012 *)
(* Leading BOM not at file start *)
Module Rule_SPC_012.
  
  Definition id := "SPC-012".
  Definition description := "Leading BOM not at file start".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "^\ufeff").
  
  (* Validation function *)
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

  
End Rule_SPC_012.

(* Rule: SPC-013 *)
(* Whitespace-only paragraph *)
Module Rule_SPC_013.
  
  Definition id := "SPC-013".
  Definition description := "Whitespace-only paragraph".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_013.

(* Rule: SPC-014 *)
(* Mix of LF and CRLF within same paragraph *)
Module Rule_SPC_014.
  
  Definition id := "SPC-014".
  Definition description := "Mix of LF and CRLF within same paragraph".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_SPC_014.

(* Rule: SPC-015 *)
(* Indentation >8 spaces (code smell) *)
Module Rule_SPC_015.
  
  Definition id := "SPC-015".
  Definition description := "Indentation >8 spaces (code smell)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{lstlisting\}.*?\\end\{lstlisting\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SPC_015.

(* Rule: SPC-016 *)
(* Space before semicolon in text *)
Module Rule_SPC_016.
  
  Definition id := "SPC-016".
  Definition description := "Space before semicolon in text".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_SPC_016.

(* Rule: SPC-017 *)
(* Missing \\, thin space before units (e.g. 5cm) *)
Module Rule_SPC_017.
  
  Definition id := "SPC-017".
  Definition description := "Missing \\, thin space before units (e.g. 5cm)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\,|\\;|\\:|\\!").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SPC_017.

(* Rule: SPC-018 *)
(* No space after sentence-ending period *)
Module Rule_SPC_018.
  
  Definition id := "SPC-018".
  Definition description := "No space after sentence-ending period".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{([^}]+)\}.*?\\end\{\1\}").
  
  (* Validation function *)
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

  
End Rule_SPC_018.

(* Rule: SPC-019 *)
(* Trailing full‑width space U+3000 at line end *)
Module Rule_SPC_019.
  
  Definition id := "SPC-019".
  Definition description := "Trailing full‑width space U+3000 at line end".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{([^}]+)\}.*?\\end\{\1\}").
  
  (* Validation function *)
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

  
End Rule_SPC_019.

(* Rule: SPC-020 *)
(* Tab character inside math mode *)
Module Rule_SPC_020.
  
  Definition id := "SPC-020".
  Definition description := "Tab character inside math mode".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
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
    Some (convert_tabs_fix input).

  
End Rule_SPC_020.

(* Rule: SPC-021 *)
(* Space before colon in text *)
Module Rule_SPC_021.
  
  Definition id := "SPC-021".
  Definition description := "Space before colon in text".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_SPC_021.

(* Rule: SPC-022 *)
(* Tab after bullet in itemize environment *)
Module Rule_SPC_022.
  
  Definition id := "SPC-022".
  Definition description := "Tab after bullet in itemize environment".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
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
    Some (convert_tabs_fix input).

  
End Rule_SPC_022.

(* Rule: SPC-023 *)
(* Hard space (U+00A0) outside French punctuation context *)
Module Rule_SPC_023.
  
  Definition id := "SPC-023".
  Definition description := "Hard space (U+00A0) outside French punctuation context".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SPC_023.

(* Rule: SPC-024 *)
(* Leading spaces on blank line *)
Module Rule_SPC_024.
  
  Definition id := "SPC-024".
  Definition description := "Leading spaces on blank line".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_024.

(* Rule: SPC-025 *)
(* Space before ellipsis \\dots *)
Module Rule_SPC_025.
  
  Definition id := "SPC-025".
  Definition description := "Space before ellipsis \\dots".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\.\.\.").
  
  (* Validation function *)
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

  
End Rule_SPC_025.

(* Rule: SPC-026 *)
(* Mixed indentation width within same list level *)
Module Rule_SPC_026.
  
  Definition id := "SPC-026".
  Definition description := "Mixed indentation width within same list level".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_SPC_026.

(* Rule: SPC-027 *)
(* Trailing whitespace inside \\url{} argument *)
Module Rule_SPC_027.
  
  Definition id := "SPC-027".
  Definition description := "Trailing whitespace inside \\url{} argument".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\url\{[^}]+\}").
  
  (* Validation function *)
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

  
End Rule_SPC_027.

(* Rule: SPC-028 *)
(* Multiple ~ non‑breaking spaces in a row *)
Module Rule_SPC_028.
  
  Definition id := "SPC-028".
  Definition description := "Multiple ~ non‑breaking spaces in a row".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_028.

(* Rule: SPC-029 *)
(* Indentation uses non‑breaking spaces *)
Module Rule_SPC_029.
  
  Definition id := "SPC-029".
  Definition description := "Indentation uses non‑breaking spaces".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_029.

(* Rule: SPC-030 *)
(* Line starts with full‑width space U+3000 *)
Module Rule_SPC_030.
  
  Definition id := "SPC-030".
  Definition description := "Line starts with full‑width space U+3000".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +").
  
  (* Validation function *)
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

  
End Rule_SPC_030.

(* Rule: TYPO-001 *)
(* ASCII straight quotes (\" … \") must be curly quotes *)
Module Rule_TYPO_001.
  
  Definition id := "TYPO-001".
  Definition description := "ASCII straight quotes (\"" … \"") must be curly quotes".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string """[^""]*""").
  
  (* Validation function *)
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

  
End Rule_TYPO_001.

(* Rule: TYPO-002 *)
(* Double hyphen -- should be en‑dash – *)
Module Rule_TYPO_002.
  
  Definition id := "TYPO-002".
  Definition description := "Double hyphen -- should be en‑dash –".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "--").
  
  (* Validation function *)
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

  
End Rule_TYPO_002.

(* Rule: TYPO-003 *)
(* Triple hyphen --- should be em‑dash — *)
Module Rule_TYPO_003.
  
  Definition id := "TYPO-003".
  Definition description := "Triple hyphen --- should be em‑dash —".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "---").
  
  (* Validation function *)
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

  
End Rule_TYPO_003.

(* Rule: TYPO-004 *)
(* TeX double back‑tick ``…'' not allowed; use opening curly quotes *)
Module Rule_TYPO_004.
  
  Definition id := "TYPO-004".
  Definition description := "TeX double back‑tick ``…'' not allowed; use opening curly quotes".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "``[^']*''").
  
  (* Validation function *)
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

  
End Rule_TYPO_004.

(* Rule: TYPO-005 *)
(* Ellipsis as three periods ...; use \\dots *)
Module Rule_TYPO_005.
  
  Definition id := "TYPO-005".
  Definition description := "Ellipsis as three periods ...; use \\dots".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\.\.\.").
  
  (* Validation function *)
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

  
End Rule_TYPO_005.

(* Rule: TYPO-006 *)
(* Tab character U+0009 forbidden *)
Module Rule_TYPO_006.
  
  Definition id := "TYPO-006".
  Definition description := "Tab character U+0009 forbidden".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_006.

(* Rule: TYPO-007 *)
(* Trailing spaces at end of line *)
Module Rule_TYPO_007.
  
  Definition id := "TYPO-007".
  Definition description := "Trailing spaces at end of line".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +$").
  
  (* Validation function *)
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

  
End Rule_TYPO_007.

(* Rule: TYPO-008 *)
(* Multiple consecutive blank lines (>2) in source *)
Module Rule_TYPO_008.
  
  Definition id := "TYPO-008".
  Definition description := "Multiple consecutive blank lines (>2) in source".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_TYPO_008.

(* Rule: TYPO-009 *)
(* Non‑breaking space ~ used incorrectly at line start *)
Module Rule_TYPO_009.
  
  Definition id := "TYPO-009".
  Definition description := "Non‑breaking space ~ used incorrectly at line start".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_009.

(* Rule: TYPO-010 *)
(* Space before punctuation , . ; : ? ! *)
Module Rule_TYPO_010.
  
  Definition id := "TYPO-010".
  Definition description := "Space before punctuation , . ; : ? !".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
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

  
End Rule_TYPO_010.

(* Rule: TYPO-011 *)
(* Missing thin space (\,) before differential d in integrals *)
Module Rule_TYPO_011.
  
  Definition id := "TYPO-011".
  Definition description := "Missing thin space (\,) before differential d in integrals".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\,|\\;|\\:|\\!").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_011.

(* Rule: TYPO-012 *)
(* Straight apostrophe ' used for minutes/feet; use ^\\prime or ′ *)
Module Rule_TYPO_012.
  
  Definition id := "TYPO-012".
  Definition description := "Straight apostrophe ' used for minutes/feet; use ^\\prime or ′".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
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

  
End Rule_TYPO_012.

(* Rule: TYPO-013 *)
(* Ascii backtick ` used as opening quote *)
Module Rule_TYPO_013.
  
  Definition id := "TYPO-013".
  Definition description := "Ascii backtick ` used as opening quote".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string """[^""]*""").
  
  (* Validation function *)
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

  
End Rule_TYPO_013.

(* Rule: TYPO-014 *)
(* Space before percent sign \\% *)
Module Rule_TYPO_014.
  
  Definition id := "TYPO-014".
  Definition description := "Space before percent sign \\%".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
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

  
End Rule_TYPO_014.

(* Rule: TYPO-015 *)
(* Double \\% in source; likely stray percent *)
Module Rule_TYPO_015.
  
  Definition id := "TYPO-015".
  Definition description := "Double \\% in source; likely stray percent".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_015.

(* Rule: TYPO-016 *)
(* Non‑breaking space ~ missing before \\cite / \\ref *)
Module Rule_TYPO_016.
  
  Definition id := "TYPO-016".
  Definition description := "Non‑breaking space ~ missing before \\cite / \\ref".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
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

  
End Rule_TYPO_016.

(* Rule: TYPO-017 *)
(* TeX accent commands (\\'{e}) in text; prefer UTF‑8 é *)
Module Rule_TYPO_017.
  
  Definition id := "TYPO-017".
  Definition description := "TeX accent commands (\\'{e}) in text; prefer UTF‑8 é".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_TYPO_017.

(* Rule: TYPO-018 *)
(* Multiple consecutive spaces in text *)
Module Rule_TYPO_018.
  
  Definition id := "TYPO-018".
  Definition description := "Multiple consecutive spaces in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
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

  
End Rule_TYPO_018.

(* Rule: TYPO-019 *)
(* Comma splice detected: missing conjunction after comma *)
Module Rule_TYPO_019.
  
  Definition id := "TYPO-019".
  Definition description := "Comma splice detected: missing conjunction after comma".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_019.

(* Rule: TYPO-020 *)
(* Sentence without ending punctuation *)
Module Rule_TYPO_020.
  
  Definition id := "TYPO-020".
  Definition description := "Sentence without ending punctuation".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{([^}]+)\}.*?\\end\{\1\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_020.

(* Rule: TYPO-021 *)
(* Capital letter after ellipsis without space *)
Module Rule_TYPO_021.
  
  Definition id := "TYPO-021".
  Definition description := "Capital letter after ellipsis without space".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\.\.\.").
  
  (* Validation function *)
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

  
End Rule_TYPO_021.

(* Rule: TYPO-022 *)
(* Space before closing punctuation ) ] } *)
Module Rule_TYPO_022.
  
  Definition id := "TYPO-022".
  Definition description := "Space before closing punctuation ) ] }".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
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

  
End Rule_TYPO_022.

(* Rule: TYPO-023 *)
(* ASCII ampersand & outside tabular env; use \\& *)
Module Rule_TYPO_023.
  
  Definition id := "TYPO-023".
  Definition description := "ASCII ampersand & outside tabular env; use \\&".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\t").
  
  (* Validation function *)
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

  
End Rule_TYPO_023.

(* Rule: TYPO-024 *)
(* Dangling dash at line end *)
Module Rule_TYPO_024.
  
  Definition id := "TYPO-024".
  Definition description := "Dangling dash at line end".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{([^}]+)\}.*?\\end\{\1\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_024.

(* Rule: TYPO-025 *)
(* Space before en‑dash in number range *)
Module Rule_TYPO_025.
  
  Definition id := "TYPO-025".
  Definition description := "Space before en‑dash in number range".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
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

  
End Rule_TYPO_025.

(* Rule: TYPO-026 *)
(* Wrong dash in page range – should use -- *)
Module Rule_TYPO_026.
  
  Definition id := "TYPO-026".
  Definition description := "Wrong dash in page range – should use --".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "--").
  
  (* Validation function *)
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

  
End Rule_TYPO_026.

(* Rule: TYPO-027 *)
(* Multiple exclamation marks ‼ *)
Module Rule_TYPO_027.
  
  Definition id := "TYPO-027".
  Definition description := "Multiple exclamation marks ‼".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_027.

(* Rule: TYPO-028 *)
(* Use of ``$$'' display math delimiter *)
Module Rule_TYPO_028.
  
  Definition id := "TYPO-028".
  Definition description := "Use of ``$$'' display math delimiter".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "``[^']*''").
  
  (* Validation function *)
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

  
End Rule_TYPO_028.

(* Rule: TYPO-029 *)
(* Non‑breaking space after \\ref missing *)
Module Rule_TYPO_029.
  
  Definition id := "TYPO-029".
  Definition description := "Non‑breaking space after \\ref missing".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
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

  
End Rule_TYPO_029.

(* Rule: TYPO-030 *)
(* UK spelling inconsistency detected *)
Module Rule_TYPO_030.
  
  Definition id := "TYPO-030".
  Definition description := "UK spelling inconsistency detected".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_030.

(* Rule: TYPO-031 *)
(* American punctuation placement inside quotes *)
Module Rule_TYPO_031.
  
  Definition id := "TYPO-031".
  Definition description := "American punctuation placement inside quotes".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string """[^""]*""").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_031.

(* Rule: TYPO-032 *)
(* Comma before \\cite *)
Module Rule_TYPO_032.
  
  Definition id := "TYPO-032".
  Definition description := "Comma before \\cite".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\cite(\[[^\]]*\])?\{[^}]+\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_032.

(* Rule: TYPO-033 *)
(* Abbreviation et.al without space *)
Module Rule_TYPO_033.
  
  Definition id := "TYPO-033".
  Definition description := "Abbreviation et.al without space".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
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

  
End Rule_TYPO_033.

(* Rule: TYPO-034 *)
(* Spurious space before footnote command \\footnote *)
Module Rule_TYPO_034.
  
  Definition id := "TYPO-034".
  Definition description := "Spurious space before footnote command \\footnote".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
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

  
End Rule_TYPO_034.

(* Rule: TYPO-035 *)
(* French punctuation requires nbsp before ; : ! ? *)
Module Rule_TYPO_035.
  
  Definition id := "TYPO-035".
  Definition description := "French punctuation requires nbsp before ; : ! ?".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[.,;:!?]").
  
  (* Validation function *)
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

  
End Rule_TYPO_035.

(* Rule: TYPO-036 *)
(* Suspicious consecutive capitalised words (shouting) *)
Module Rule_TYPO_036.
  
  Definition id := "TYPO-036".
  Definition description := "Suspicious consecutive capitalised words (shouting)".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "3\.14(?:\d+)?").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_036.

(* Rule: TYPO-037 *)
(* Space before comma *)
Module Rule_TYPO_037.
  
  Definition id := "TYPO-037".
  Definition description := "Space before comma".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\s+").
  
  (* Validation function *)
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

  
End Rule_TYPO_037.

(* Rule: TYPO-038 *)
(* E‑mail address not in \\href *)
Module Rule_TYPO_038.
  
  Definition id := "TYPO-038".
  Definition description := "E‑mail address not in \\href".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\ref\{[^}]+\}").
  
  (* Validation function *)
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

  
End Rule_TYPO_038.

(* Rule: TYPO-039 *)
(* URL split across lines without \\url{} *)
Module Rule_TYPO_039.
  
  Definition id := "TYPO-039".
  Definition description := "URL split across lines without \\url{}".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\url\{[^}]+\}").
  
  (* Validation function *)
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

  
End Rule_TYPO_039.

(* Rule: TYPO-040 *)
(* Math in text mode $...$ exceeds 80 chars *)
Module Rule_TYPO_040.
  
  Definition id := "TYPO-040".
  Definition description := "Math in text mode $...$ exceeds 80 chars".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\.\.\.").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_040.

(* Rule: TYPO-041 *)
(* Incorrect spacing around \\ldots ... *)
Module Rule_TYPO_041.
  
  Definition id := "TYPO-041".
  Definition description := "Incorrect spacing around \\ldots ...".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\.\.\.").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_041.

(* Rule: TYPO-042 *)
(* Multiple consecutive question marks ?? *)
Module Rule_TYPO_042.
  
  Definition id := "TYPO-042".
  Definition description := "Multiple consecutive question marks ??".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_042.

(* Rule: TYPO-043 *)
(* Smart quotes inside verbatim detected *)
Module Rule_TYPO_043.
  
  Definition id := "TYPO-043".
  Definition description := "Smart quotes inside verbatim detected".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\verb\|[^|]+\|").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_043.

(* Rule: TYPO-044 *)
(* Acronym not defined on first use *)
Module Rule_TYPO_044.
  
  Definition id := "TYPO-044".
  Definition description := "Acronym not defined on first use".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := None.
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_044.

(* Rule: TYPO-045 *)
(* Non‑ASCII punctuation in math mode (e.g. ‘ ’ “ ”) *)
Module Rule_TYPO_045.
  
  Definition id := "TYPO-045".
  Definition description := "Non‑ASCII punctuation in math mode (e.g. ‘ ’ “ ”)".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "[.,;:!?]").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_045.

(* Rule: TYPO-046 *)
(* Use of \$begin:math:text$ ... \\$end:math:text$ inline math instead of $ ... $ *)
Module Rule_TYPO_046.
  
  Definition id := "TYPO-046".
  Definition description := "Use of \$begin:math:text$ ... \\$end:math:text$ inline math instead of $ ... $".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\.\.\.").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_046.

(* Rule: TYPO-047 *)
(* Starred section command \\section* used in numbered context *)
Module Rule_TYPO_047.
  
  Definition id := "TYPO-047".
  Definition description := "Starred section command \\section* used in numbered context".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_047.

(* Rule: TYPO-048 *)
(* En‑dash used as minus sign in text *)
Module Rule_TYPO_048.
  
  Definition id := "TYPO-048".
  Definition description := "En‑dash used as minus sign in text".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\frac\{[^}]*\}\{[^}]*\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_TYPO_048.

(* Rule: TYPO-049 *)
(* Space after opening quote *)
Module Rule_TYPO_049.
  
  Definition id := "TYPO-049".
  Definition description := "Space after opening quote".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string """[^""]*""").
  
  (* Validation function *)
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

  
End Rule_TYPO_049.

(* Rule: VERB-001 *)
(* \\verb delimiter reused inside same verb block *)
Module Rule_VERB_001.
  
  Definition id := "VERB-001".
  Definition description := "\\verb delimiter reused inside same verb block".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\verb\|[^|]+\|").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_001.

(* Rule: VERB-002 *)
(* Tab inside verbatim – discouraged *)
Module Rule_VERB_002.
  
  Definition id := "VERB-002".
  Definition description := "Tab inside verbatim – discouraged".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{verbatim\}.*?\\end\{verbatim\}").
  
  (* Validation function *)
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
    Some (convert_tabs_fix input).

  
End Rule_VERB_002.

(* Rule: VERB-003 *)
(* Trailing spaces inside verbatim *)
Module Rule_VERB_003.
  
  Definition id := "VERB-003".
  Definition description := "Trailing spaces inside verbatim".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string " +$").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_003.

(* Rule: VERB-004 *)
(* Non‑ASCII quotes inside verbatim *)
Module Rule_VERB_004.
  
  Definition id := "VERB-004".
  Definition description := "Non‑ASCII quotes inside verbatim".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string """[^""]*""").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_004.

(* Rule: VERB-005 *)
(* Long verbatim > 120 chars on one line *)
Module Rule_VERB_005.
  
  Definition id := "VERB-005".
  Definition description := "Long verbatim > 120 chars on one line".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\verb\|[^|]+\|").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_005.

(* Rule: VERB-006 *)
(* Inline verb \\verb used for multiline content *)
Module Rule_VERB_006.
  
  Definition id := "VERB-006".
  Definition description := "Inline verb \\verb used for multiline content".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\verb\|[^|]+\|").
  
  (* Validation function *)
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

  
End Rule_VERB_006.

(* Rule: VERB-007 *)
(* Nested verbatim environment *)
Module Rule_VERB_007.
  
  Definition id := "VERB-007".
  Definition description := "Nested verbatim environment".
  Definition severity := SeverityError.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{([^}]+)\}.*?\\end\{\1\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_007.

(* Rule: VERB-008 *)
(* `lstlisting` uses language=none *)
Module Rule_VERB_008.
  
  Definition id := "VERB-008".
  Definition description := "`lstlisting` uses language=none".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{lstlisting\}.*?\\end\{lstlisting\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_008.

(* Rule: VERB-009 *)
(* Missing caption in minted code block *)
Module Rule_VERB_009.
  
  Definition id := "VERB-009".
  Definition description := "Missing caption in minted code block".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_009.

(* Rule: VERB-010 *)
(* Inline code uses back‑ticks (`) instead of \\verb *)
Module Rule_VERB_010.
  
  Definition id := "VERB-010".
  Definition description := "Inline code uses back‑ticks (`) instead of \\verb".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\verb\|[^|]+\|").
  
  (* Validation function *)
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

  
End Rule_VERB_010.

(* Rule: VERB-011 *)
(* lstlisting language unknown *)
Module Rule_VERB_011.
  
  Definition id := "VERB-011".
  Definition description := "lstlisting language unknown".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{lstlisting\}.*?\\end\{lstlisting\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_011.

(* Rule: VERB-012 *)
(* minted block missing autogobble option *)
Module Rule_VERB_012.
  
  Definition id := "VERB-012".
  Definition description := "minted block missing autogobble option".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "(?<!\\)(?:sin|cos|tan|log|exp|ln|max|min|det|dim)(?![a-zA-Z])").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_012.

(* Rule: VERB-013 *)
(* Code line > 120 glyphs *)
Module Rule_VERB_013.
  
  Definition id := "VERB-013".
  Definition description := "Code line > 120 glyphs".
  Definition severity := SeverityInfo.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\begin\{lstlisting\}.*?\\end\{lstlisting\}").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_013.

(* Rule: VERB-015 *)
(* Verbatim uses catcode changes instead of \\verb *)
Module Rule_VERB_015.
  
  Definition id := "VERB-015".
  Definition description := "Verbatim uses catcode changes instead of \\verb".
  Definition severity := SeverityWarning.
  Definition precondition := PrecondLexer.
  
  (* Pattern matching for this rule *)
  Definition pattern : option regex := Some (regex_from_string "\\verb\|[^|]+\|").
  
  (* Validation function *)
  Definition validate (input : latex_token_list) : validation_result :=
    match pattern with
    | None => Valid
    | Some p => 
        if regex_match p input then
          Invalid id description severity
        else
          Valid
    end.

  
End Rule_VERB_015.

