(* Code and Verbatim Text Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for proper code listing and verbatim text formatting *)

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

(** Code listing package rules **)
module CodePackageRules = struct
  
  (* Rule: Consistent code package usage *)
  let consistent_code_packages = {
    id = "CODE-001";
    name = "consistent_code_packages";
    description = "Use consistent package for code listings";
    severity = Warning;
    category = "code";
    check = fun tokens ->
      let code_packages = ref [] in
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "usepackage" :: TGroupOpen :: TMacro pkg :: TGroupClose :: rest
          when List.mem pkg ["listings"; "minted"; "fancyvrb"; "verbatim"] ->
            code_packages := pkg :: !code_packages;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      let unique_packages = List.sort_uniq String.compare !code_packages in
      if List.length unique_packages > 1 then
        issues := {
          rule_id = "CODE-001";
          message = "Multiple code listing packages detected";
          location = Location.make 0 0;
          suggestion = Some "Use one consistent package (listings or minted)";
          confidence = 0.8;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Syntax highlighting *)
  let syntax_highlighting = {
    id = "CODE-002";
    name = "syntax_highlighting";
    description = "Use syntax highlighting for code listings";
    severity = Info;
    category = "code";
    check = fun tokens ->
      let has_listings = 
        let rec check_listings i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "listings", TGroupClose) -> true
            | _ -> check_listings (i + 1))
          | _ -> check_listings (i + 1)
        in check_listings 0 in
      
      let has_lstlisting = 
        let rec check_lstlisting i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "begin" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "lstlisting", TGroupClose) -> true
            | _ -> check_lstlisting (i + 1))
          | _ -> check_lstlisting (i + 1)
        in check_lstlisting 0 in
      
      let has_language_spec = Array.exists (function
        | TMacro "lstset" -> true
        | _ -> false
      ) tokens in
      
      if has_listings && has_lstlisting && not has_language_spec then
        [{
          rule_id = "CODE-002";
          message = "Consider specifying language for syntax highlighting";
          location = Location.make 0 0;
          suggestion = Some "Use \\lstset{language=Python} or [language=Python] option";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Code listing captions *)
  let code_captions = {
    id = "CODE-003";
    name = "code_captions";
    description = "Add captions to code listings";
    severity = Info;
    category = "code";
    check = fun tokens ->
      let issues = ref [] in
      let in_lstlisting = ref false in
      let current_listing_has_caption = ref false in
      
      let rec scan = function
        | [] ->
            if !in_lstlisting && not !current_listing_has_caption then
              issues := {
                rule_id = "CODE-003";
                message = "Code listing without caption";
                location = Location.make 0 0;
                suggestion = Some "Add caption option or \\caption{...}";
                confidence = 0.6;
              } :: !issues
        | TMacro "begin" :: TGroupOpen :: TMacro "lstlisting" :: TGroupClose :: rest ->
            in_lstlisting := true;
            current_listing_has_caption := false;
            (* Check for caption option *)
            (match rest with
            | TOptionalArg _ :: _ -> current_listing_has_caption := true
            | _ -> ());
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro "lstlisting" :: TGroupClose :: rest ->
            if !in_lstlisting && not !current_listing_has_caption then
              issues := {
                rule_id = "CODE-003";
                message = "Code listing without caption";
                location = Location.make 0 0;
                suggestion = Some "Add caption option: [caption={...}]";
                confidence = 0.6;
              } :: !issues;
            in_lstlisting := false;
            scan rest
        | TMacro "caption" :: rest when !in_lstlisting ->
            current_listing_has_caption := true;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Verbatim environment rules **)
module VerbatimRules = struct
  
  (* Rule: Avoid basic verbatim for code *)
  let avoid_basic_verbatim = {
    id = "VERB-001";
    name = "avoid_basic_verbatim";
    description = "Use specialized environments instead of basic verbatim for code";
    severity = Info;
    category = "verbatim";
    check = fun tokens ->
      let has_verbatim = ref false in
      let has_code_packages = ref false in
      let issues = ref [] in
      
      let rec scan_tokens i =
        if i < Array.length tokens - 3 then
          match tokens.(i) with
          | TMacro "begin" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "verbatim", TGroupClose) -> 
              has_verbatim := true; scan_tokens (i + 4)
            | _ -> scan_tokens (i + 1))
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro pkg, TGroupClose) 
              when List.mem pkg ["listings"; "minted"; "fancyvrb"] ->
              has_code_packages := true; scan_tokens (i + 4)
            | _ -> scan_tokens (i + 1))
          | _ -> scan_tokens (i + 1)
      in
      scan_tokens 0;
      
      if !has_verbatim && !has_code_packages then
        issues := {
          rule_id = "VERB-001";
          message = "Consider using lstlisting instead of verbatim for code";
          location = Location.make 0 0;
          suggestion = Some "Use \\begin{lstlisting} for better code formatting";
          confidence = 0.7;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Long verbatim blocks *)
  let long_verbatim_blocks = {
    id = "VERB-002";
    name = "long_verbatim_blocks";
    description = "Consider page breaks for long verbatim blocks";
    severity = Info;
    category = "verbatim";
    check = fun tokens ->
      let issues = ref [] in
      let in_verbatim = ref false in
      let verbatim_line_count = ref 0 in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["verbatim"; "lstlisting"; "minted"] ->
            in_verbatim := true;
            verbatim_line_count := 0;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["verbatim"; "lstlisting"; "minted"] ->
            if !verbatim_line_count > 30 then
              issues := {
                rule_id = "VERB-002";
                message = Printf.sprintf "Very long code block (%d lines)" !verbatim_line_count;
                location = Location.make 0 0;
                suggestion = Some "Consider splitting or using breaklines option";
                confidence = 0.6;
              } :: !issues;
            in_verbatim := false;
            scan rest
        | TChar (uc, _) :: rest when !in_verbatim && Uchar.to_int uc = 0x0A -> (* newline *)
            incr verbatim_line_count;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Inline vs block verbatim *)
  let inline_vs_block = {
    id = "VERB-003";
    name = "inline_vs_block";
    description = "Use appropriate verbatim for inline vs block code";
    severity = Info;
    category = "verbatim";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "verb" :: rest ->
            (* Check for long inline code *)
            let rec count_verb_length acc = function
              | [] -> acc
              | TChar (uc, _) :: rest when Uchar.to_int uc <> 0x7C -> (* not | *)
                  count_verb_length (acc + 1) rest
              | _ -> acc
            in
            let length = count_verb_length 0 rest in
            if length > 50 then
              issues := {
                rule_id = "VERB-003";
                message = "Long inline code - consider using block environment";
                location = Location.make 0 0;
                suggestion = Some "Use \\begin{lstlisting} for multi-line code";
                confidence = 0.7;
              } :: !issues;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Code style and formatting rules **)
module CodeStyleRules = struct
  
  (* Rule: Code indentation *)
  let code_indentation = {
    id = "STYLE-001";
    name = "code_indentation";
    description = "Maintain consistent code indentation";
    severity = Info;
    category = "style";
    check = fun tokens ->
      [{
        rule_id = "STYLE-001";
        message = "Ensure consistent indentation in code blocks";
        location = Location.make 0 0;
        suggestion = Some "Use tabsize and breakindent options in listings";
        confidence = 0.5;
      }]
  }
  
  (* Rule: Line length in code *)
  let code_line_length = {
    id = "STYLE-002";
    name = "code_line_length";
    description = "Consider line length in code listings";
    severity = Info;
    category = "style";
    check = fun tokens ->
      [{
        rule_id = "STYLE-002";
        message = "Consider using breaklines for long code lines";
        location = Location.make 0 0;
        suggestion = Some "Add breaklines=true to lstset or listing options";
        confidence = 0.6;
      }]
  }
  
  (* Rule: Code font size *)
  let code_font_size = {
    id = "STYLE-003";
    name = "code_font_size";
    description = "Use appropriate font size for code listings";
    severity = Info;
    category = "style";
    check = fun tokens ->
      let has_small_font = Array.exists (function
        | TMacro name when List.mem name ["tiny"; "scriptsize"; "footnotesize"; "small"] -> true
        | _ -> false
      ) tokens in
      
      if not has_small_font then
        [{
          rule_id = "STYLE-003";
          message = "Consider smaller font size for code listings";
          location = Location.make 0 0;
          suggestion = Some "Add basicstyle=\\small or \\footnotesize to lstset";
          confidence = 0.5;
        }]
      else []
  }
end

(** Algorithm and pseudocode rules **)
module AlgorithmRules = struct
  
  (* Rule: Algorithm formatting *)
  let algorithm_formatting = {
    id = "ALG-001";
    name = "algorithm_formatting";
    description = "Use proper algorithm formatting packages";
    severity = Info;
    category = "algorithm";
    check = fun tokens ->
      let has_algorithm = 
        let rec check_algorithm i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "begin" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro env, TGroupClose) 
              when List.mem env ["algorithm"; "algorithmic"] -> true
            | _ -> check_algorithm (i + 1))
          | _ -> check_algorithm (i + 1)
        in check_algorithm 0 in
      
      let has_algo_package = 
        let rec check_algo_package i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro pkg, TGroupClose) 
              when List.mem pkg ["algorithm2e"; "algorithmic"; "algorithmicx"] -> true
            | _ -> check_algo_package (i + 1))
          | _ -> check_algo_package (i + 1)
        in check_algo_package 0 in
      
      if has_algorithm && not has_algo_package then
        [{
          rule_id = "ALG-001";
          message = "Consider using algorithm2e or algorithmic package";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage{algorithm2e} or \\usepackage{algorithmic}";
          confidence = 0.8;
        }]
      else []
  }
  
  (* Rule: Algorithm captions *)
  let algorithm_captions = {
    id = "ALG-002";
    name = "algorithm_captions";
    description = "Add captions to algorithms";
    severity = Info;
    category = "algorithm";
    check = fun tokens ->
      let issues = ref [] in
      let in_algorithm = ref false in
      let current_algo_has_caption = ref false in
      
      let rec scan = function
        | [] ->
            if !in_algorithm && not !current_algo_has_caption then
              issues := {
                rule_id = "ALG-002";
                message = "Algorithm without caption";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} to algorithm";
                confidence = 0.8;
              } :: !issues
        | TMacro "begin" :: TGroupOpen :: TMacro "algorithm" :: TGroupClose :: rest ->
            in_algorithm := true;
            current_algo_has_caption := false;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro "algorithm" :: TGroupClose :: rest ->
            if !in_algorithm && not !current_algo_has_caption then
              issues := {
                rule_id = "ALG-002";
                message = "Algorithm without caption";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} to algorithm";
                confidence = 0.8;
              } :: !issues;
            in_algorithm := false;
            scan rest
        | TMacro "caption" :: rest when !in_algorithm ->
            current_algo_has_caption := true;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Syntax and escaping rules **)
module SyntaxRules = struct
  
  (* Rule: Special character escaping *)
  let special_character_escaping = {
    id = "ESC-001";
    name = "special_character_escaping";
    description = "Properly escape special characters in verbatim";
    severity = Warning;
    category = "syntax";
    check = fun tokens ->
      let issues = ref [] in
      let in_verbatim = ref false in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["verbatim"; "lstlisting"] ->
            in_verbatim := true;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["verbatim"; "lstlisting"] ->
            in_verbatim := false;
            scan rest
        | TChar (uc, _) :: rest when not !in_verbatim ->
            let char_code = Uchar.to_int uc in
            if List.mem char_code [0x24; 0x25; 0x26; 0x23; 0x5F; 0x7B; 0x7D] then (* $ % & # _ { } *)
              issues := {
                rule_id = "ESC-001";
                message = "Special character may need escaping";
                location = Location.make 0 0;
                suggestion = Some "Use \\ to escape special characters";
                confidence = 0.6;
              } :: !issues;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Unicode in code *)
  let unicode_in_code = {
    id = "ESC-002";
    name = "unicode_in_code";
    description = "Handle Unicode characters in code listings";
    severity = Info;
    category = "syntax";
    check = fun tokens ->
      let issues = ref [] in
      let in_code = ref false in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["lstlisting"; "minted"] ->
            in_code := true;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["lstlisting"; "minted"] ->
            in_code := false;
            scan rest
        | TChar (uc, _) :: rest when !in_code ->
            if Uchar.to_int uc > 127 then
              issues := {
                rule_id = "ESC-002";
                message = "Unicode character in code listing";
                location = Location.make 0 0;
                suggestion = Some "Ensure listings package supports Unicode or use XeLaTeX/LuaLaTeX";
                confidence = 0.7;
              } :: !issues;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Collect all code and verbatim rules *)
let all_rules = [
  (* Code packages *)
  CodePackageRules.consistent_code_packages;
  CodePackageRules.syntax_highlighting;
  CodePackageRules.code_captions;
  
  (* Verbatim *)
  VerbatimRules.avoid_basic_verbatim;
  VerbatimRules.long_verbatim_blocks;
  VerbatimRules.inline_vs_block;
  
  (* Code style *)
  CodeStyleRules.code_indentation;
  CodeStyleRules.code_line_length;
  CodeStyleRules.code_font_size;
  
  (* Algorithms *)
  AlgorithmRules.algorithm_formatting;
  AlgorithmRules.algorithm_captions;
  
  (* Syntax *)
  SyntaxRules.special_character_escaping;
  SyntaxRules.unicode_in_code;
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