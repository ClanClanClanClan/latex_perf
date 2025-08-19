(* Language and Localization Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for multilingual documents and proper language usage *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

type validation_issue = {
  rule_id: string;
  message: string;
  location: Location.t;
  suggestion: string option;
  confidence: float;
}

type rule_severity = Info | Warning | Error

type validation_rule = {
  id: string;
  name: string;
  description: string;
  severity: rule_severity;
  category: string;
  check: token array -> validation_issue list;
}

(* Language detection helpers *)
let common_english_words = [
  "the"; "and"; "for"; "are"; "but"; "not"; "you"; "all"; "can"; "had"; 
  "her"; "was"; "one"; "our"; "out"; "day"; "get"; "has"; "him"; "his"; 
  "how"; "man"; "new"; "now"; "old"; "see"; "two"; "way"; "who"; "boy";
]

let common_german_words = [
  "der"; "die"; "und"; "in"; "den"; "von"; "zu"; "das"; "mit"; "sich";
  "des"; "auf"; "für"; "ist"; "im"; "dem"; "nicht"; "ein"; "eine"; "als";
]

let common_french_words = [
  "le"; "de"; "et"; "à"; "un"; "il"; "être"; "et"; "en"; "avoir";
  "que"; "pour"; "dans"; "ce"; "son"; "une"; "sur"; "avec"; "ne"; "se";
]

let common_spanish_words = [
  "el"; "la"; "de"; "que"; "y"; "a"; "en"; "un"; "es"; "se"; "no"; "te";
  "lo"; "le"; "da"; "su"; "por"; "son"; "con"; "para"; "al"; "las";
]

(** Language consistency rules *)
module LanguageConsistency = struct
  
  (* Rule: Consistent hyphenation patterns *)
  let hyphenation_consistency = {
    id = "LANG-001";
    name = "hyphenation_consistency";
    description = "Use consistent hyphenation for the document language";
    severity = Warning;
    category = "language";
    check = fun tokens ->
      let issues = ref [] in
      let babel_lang = ref None in
      let polyglossia_lang = ref None in
      
      let rec scan = function
        | [] -> ()
        | TMacro "usepackage" :: TGroupOpen :: TMacro "babel" :: TGroupClose :: rest ->
            scan rest (* Note: Extract language options *)
        | TMacro "selectlanguage" :: TGroupOpen :: TMacro lang :: TGroupClose :: rest ->
            babel_lang := Some lang;
            scan rest
        | TMacro "setmainlanguage" :: TGroupOpen :: TMacro lang :: TGroupClose :: rest ->
            polyglossia_lang := Some lang;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      (* Check for mixed language packages *)
      if Option.is_some !babel_lang && Option.is_some !polyglossia_lang then
        issues := {
          rule_id = "LANG-001";
          message = "Both babel and polyglossia detected";
          location = Location.make 0 0;
          suggestion = Some "Use either babel or polyglossia, not both";
          confidence = 0.9;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Language-specific quotation marks *)
  let quotation_marks = {
    id = "LANG-002";
    name = "quotation_marks";
    description = "Use language-appropriate quotation marks";
    severity = Info;
    category = "language";
    check = fun tokens ->
      let issues = ref [] in
      let quote_styles = Hashtbl.create 10 in
      
      (* Detect quotation mark usage patterns *)
      let rec scan = function
        | [] -> ()
        | TMacro "enquote" :: rest ->
            Hashtbl.replace quote_styles "csquotes" true;
            scan rest
        | TMacro "glqq" :: rest | TMacro "grqq" :: rest ->
            Hashtbl.replace quote_styles "german" true;
            scan rest
        | TMacro "guillemotleft" :: rest | TMacro "guillemotright" :: rest ->
            Hashtbl.replace quote_styles "french" true;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      if Hashtbl.length quote_styles > 1 then
        issues := {
          rule_id = "LANG-002";
          message = "Mixed quotation mark styles detected";
          location = Location.make 0 0;
          suggestion = Some "Use consistent quotation style for the document language";
          confidence = 0.7;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Proper language switching *)
  let language_switching = {
    id = "LANG-003";
    name = "language_switching";
    description = "Proper language switching in multilingual documents";
    severity = Warning;
    category = "language";
    check = fun tokens ->
      let issues = ref [] in
      let current_lang = ref "english" in
      let lang_stack = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "foreignlanguage" :: TGroupOpen :: TMacro lang :: TGroupClose :: rest ->
            (* Should be followed by proper text grouping *)
            (match rest with
            | TGroupOpen :: _ -> ()
            | _ -> 
                issues := {
                  rule_id = "LANG-003";
                  message = "\\foreignlanguage should be followed by {text}";
                  location = Location.make 0 0;
                  suggestion = Some "Use \\foreignlanguage{lang}{text}";
                  confidence = 0.8;
                } :: !issues);
            scan rest
        | TMacro lang :: rest when List.mem lang ["english"; "german"; "french"; "spanish"] ->
            lang_stack := !current_lang :: !lang_stack;
            current_lang := lang;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      List.rev !issues
  }
end

(** Typography rules for specific languages *)
module TypographyByLanguage = struct
  
  (* Rule: German typography *)
  let german_typography = {
    id = "LANG-004";
    name = "german_typography";
    description = "German-specific typography rules";
    severity = Info;
    category = "language";
    check = fun tokens ->
      let issues = ref [] in
      let is_german = ref false in
      
      (* Detect German language *)
      Array.iter (function
        | TMacro lang when List.mem lang ["german"; "ngerman"; "deutsch"] ->
            is_german := true
        | _ -> ()
      ) tokens;
      
      if !is_german then (
        (* Check for proper German quotation marks *)
        let rec scan = function
          | [] -> ()
          | TChar (uc1, _) :: TChar (uc2, _) :: rest 
            when Uchar.to_int uc1 = 0x22 && Uchar.to_int uc2 = 0x22 -> (* "" *)
              issues := {
                rule_id = "LANG-004";
                message = "Use German quotation marks \\glqq and \\grqq";
                location = Location.make 0 0;
                suggestion = Some "Replace with \\glqq{}text\\grqq{}";
                confidence = 0.8;
              } :: !issues;
              scan rest
          | _ :: rest -> scan rest
        in
        scan (Array.to_list tokens)
      );
      
      List.rev !issues
  }
  
  (* Rule: French typography *)
  let french_typography = {
    id = "LANG-005";
    name = "french_typography";
    description = "French-specific typography rules";
    severity = Info;
    category = "language";
    check = fun tokens ->
      let issues = ref [] in
      let is_french = ref false in
      
      (* Detect French language *)
      Array.iter (function
        | TMacro lang when List.mem lang ["french"; "francais"; "frenchb"] ->
            is_french := true
        | _ -> ()
      ) tokens;
      
      if !is_french then (
        (* Check for proper French spacing rules *)
        Array.iteri (fun i tok ->
          match tok with
          | TChar (uc, _) when Uchar.to_int uc = 0x3A -> (* : *)
              if i > 0 then (match tokens.(i-1) with
                | TChar (uc_prev, _) when Uchar.to_int uc_prev <> 0x20 ->
                    issues := {
                      rule_id = "LANG-005";
                      message = "French typography requires space before colon";
                      location = Location.make 0 0;
                      suggestion = Some "Add non-breaking space ~ before :";
                      confidence = 0.9;
                    } :: !issues
                | _ -> ())
          | TChar (uc, _) when Uchar.to_int uc = 0x21 -> (* ! *)
              if i > 0 then (match tokens.(i-1) with
                | TChar (uc_prev, _) when Uchar.to_int uc_prev <> 0x20 ->
                    issues := {
                      rule_id = "LANG-005";
                      message = "French typography requires space before exclamation";
                      location = Location.make 0 0;
                      suggestion = Some "Add non-breaking space ~ before !";
                      confidence = 0.9;
                    } :: !issues
                | _ -> ())
          | _ -> ()
        ) tokens
      );
      
      List.rev !issues
  }
end

(** Encoding and character rules *)
module EncodingRules = struct
  
  (* Rule: Consistent input encoding *)
  let input_encoding = {
    id = "LANG-006";
    name = "input_encoding";
    description = "Specify input encoding consistently";
    severity = Warning;
    category = "language";
    check = fun tokens ->
      let encodings = ref [] in
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "usepackage" :: TGroupOpen :: TMacro "inputenc" :: TGroupClose :: rest ->
            encodings := "inputenc" :: !encodings;
            scan rest
        | TMacro "inputencoding" :: TGroupOpen :: TMacro enc :: TGroupClose :: rest ->
            encodings := enc :: !encodings;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      let unique_encodings = List.sort_uniq String.compare !encodings in
      if List.length unique_encodings > 1 then
        issues := {
          rule_id = "LANG-006";
          message = "Multiple input encodings specified";
          location = Location.make 0 0;
          suggestion = Some "Use consistent input encoding throughout";
          confidence = 0.8;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Font encoding *)
  let font_encoding = {
    id = "LANG-007";
    name = "font_encoding";
    description = "Use appropriate font encoding for language";
    severity = Warning;
    category = "language";
    check = fun tokens ->
      let has_fontenc = ref false in
      let has_unicode_engine = ref false in
      let issues = ref [] in
      
      Array.iter (function
        | TMacro "usepackage" -> has_fontenc := true
        | TMacro cmd when List.mem cmd ["XeLaTeX"; "LuaLaTeX"] -> 
            has_unicode_engine := true
        | _ -> ()
      ) tokens;
      
      if not !has_fontenc && not !has_unicode_engine then
        issues := {
          rule_id = "LANG-007";
          message = "Consider using fontenc package for better font encoding";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage[T1]{fontenc} to preamble";
          confidence = 0.6;
        } :: !issues;
      
      List.rev !issues
  }
end

(** Collect all language rules *)
let all_rules = [
  (* Language consistency *)
  LanguageConsistency.hyphenation_consistency;
  LanguageConsistency.quotation_marks;
  LanguageConsistency.language_switching;
  
  (* Language-specific typography *)
  TypographyByLanguage.german_typography;
  TypographyByLanguage.french_typography;
  
  (* Encoding *)
  EncodingRules.input_encoding;
  EncodingRules.font_encoding;
]

(** Validation functions *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    acc @ List.map (fun issue -> (rule, issue)) issues
  ) [] all_rules

let rule_count () = List.length all_rules

let rules_by_category category =
  List.filter (fun r -> r.category = category) all_rules