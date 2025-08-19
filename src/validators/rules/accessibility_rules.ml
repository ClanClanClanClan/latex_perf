(* Accessibility and Semantic Markup Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for proper accessibility and semantic document markup *)

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

(** PDF accessibility rules **)
module PDFAccessibilityRules = struct
  
  (* Rule: PDF/A compliance *)
  let pdf_a_compliance = {
    id = "ACC-001";
    name = "pdf_a_compliance";
    description = "Consider PDF/A compliance for accessibility";
    severity = Info;
    category = "accessibility";
    check = fun tokens ->
      let has_pdfa_package = 
        let rec check_pdfa i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro pkg, TGroupClose) 
              when List.mem pkg ["pdfx"; "pdfa"; "pdfx-a"] -> true
            | _ -> check_pdfa (i + 1))
          | _ -> check_pdfa (i + 1)
        in check_pdfa 0 in
      
      let has_hyperref = 
        let rec check_hyperref i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "hyperref", TGroupClose) -> true
            | _ -> check_hyperref (i + 1))
          | _ -> check_hyperref (i + 1)
        in check_hyperref 0 in
      
      if has_hyperref && not has_pdfa_package then
        [{
          rule_id = "ACC-001";
          message = "Consider PDF/A compliance for accessibility";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage{pdfx} or \\usepackage{pdfa} for standards compliance";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Alt text for graphics *)
  let alt_text_graphics = {
    id = "ACC-002";
    name = "alt_text_graphics";
    description = "Provide alt text for graphics";
    severity = Warning;
    category = "accessibility";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "includegraphics" :: rest ->
            (* Check if there's descriptive caption nearby *)
            let has_nearby_caption = ref false in
            let rec check_caption = function
              | [] -> ()
              | TMacro "caption" :: _ -> has_nearby_caption := true
              | _ :: rest -> check_caption rest
            in
            check_caption rest;
            if not !has_nearby_caption then
              issues := {
                rule_id = "ACC-002";
                message = "Graphics should have descriptive captions or alt text";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} or use accessibility packages";
                confidence = 0.8;
              } :: !issues;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Document metadata *)
  let document_metadata = {
    id = "ACC-003";
    name = "document_metadata";
    description = "Include document metadata for accessibility";
    severity = Info;
    category = "accessibility";
    check = fun tokens ->
      let has_title = Array.exists (function
        | TMacro "title" -> true
        | _ -> false
      ) tokens in
      
      let has_author = Array.exists (function
        | TMacro "author" -> true
        | _ -> false
      ) tokens in
      
      let issues = ref [] in
      if not has_title then
        issues := {
          rule_id = "ACC-003";
          message = "Document should have \\title{...} for metadata";
          location = Location.make 0 0;
          suggestion = Some "Add \\title{Document Title} in preamble";
          confidence = 0.9;
        } :: !issues;
      
      if not has_author then
        issues := {
          rule_id = "ACC-003";
          message = "Document should have \\author{...} for metadata";
          location = Location.make 0 0;
          suggestion = Some "Add \\author{Author Name} in preamble";
          confidence = 0.8;
        } :: !issues;
      
      List.rev !issues
  }
end

(** Semantic markup rules **)
module SemanticMarkupRules = struct
  
  (* Rule: Use semantic commands over formatting *)
  let semantic_over_formatting = {
    id = "SEM-001";
    name = "semantic_over_formatting";
    description = "Use semantic commands instead of direct formatting";
    severity = Warning;
    category = "semantic";
    check = fun tokens ->
      let formatting_commands = ["textbf"; "textit"; "underline"; "emph"] in
      let has_semantic_commands = Array.exists (function
        | TMacro name when List.mem name ["strong"; "term"; "concept"; "keyword"] -> true
        | _ -> false
      ) tokens in
      
      let formatting_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name formatting_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if formatting_count > 5 && not has_semantic_commands then
        [{
          rule_id = "SEM-001";
          message = "Consider defining semantic commands instead of direct formatting";
          location = Location.make 0 0;
          suggestion = Some "Define \\newcommand{\\term}[1]{\\textit{#1}} for semantic markup";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Proper emphasis usage *)
  let proper_emphasis = {
    id = "SEM-002";
    name = "proper_emphasis";
    description = "Use \\emph{} for emphasis instead of \\textit{}";
    severity = Info;
    category = "semantic";
    check = fun tokens ->
      let textit_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro "textit" -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      let emph_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro "emph" -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if textit_count > emph_count * 2 then
        [{
          rule_id = "SEM-002";
          message = "Consider using \\emph{} instead of \\textit{} for emphasis";
          location = Location.make 0 0;
          suggestion = Some "Use \\emph{} for semantic emphasis";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Quote environments *)
  let quote_environments = {
    id = "SEM-003";
    name = "quote_environments";
    description = "Use proper quote environments for quotations";
    severity = Info;
    category = "semantic";
    check = fun tokens ->
      let has_quotes = Array.exists (function
        | TChar (uc, _) when List.mem (Uchar.to_int uc) [0x22; 0x201C; 0x201D] -> true (* " " " *)
        | _ -> false
      ) tokens in
      
      let has_quote_env = 
        let rec check_quote_env i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "begin" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro env, TGroupClose) 
              when List.mem env ["quote"; "quotation"; "displayquote"] -> true
            | _ -> check_quote_env (i + 1))
          | _ -> check_quote_env (i + 1)
        in check_quote_env 0 in
      
      if has_quotes && not has_quote_env then
        [{
          rule_id = "SEM-003";
          message = "Consider using quote or quotation environment for long quotes";
          location = Location.make 0 0;
          suggestion = Some "Use \\begin{quote}...\\end{quote} for block quotations";
          confidence = 0.5;
        }]
      else []
  }
end

(** Language and internationalization rules **)
module InternationalizationRules = struct
  
  (* Rule: Language tagging *)
  let language_tagging = {
    id = "I18N-001";
    name = "language_tagging";
    description = "Tag document language for accessibility";
    severity = Info;
    category = "i18n";
    check = fun tokens ->
      let has_babel = 
        let rec check_babel i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "babel", TGroupClose) -> true
            | _ -> check_babel (i + 1))
          | _ -> check_babel (i + 1)
        in check_babel 0 in
      
      let has_polyglossia = 
        let rec check_polyglossia i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "polyglossia", TGroupClose) -> true
            | _ -> check_polyglossia (i + 1))
          | _ -> check_polyglossia (i + 1)
        in check_polyglossia 0 in
      
      if not has_babel && not has_polyglossia then
        [{
          rule_id = "I18N-001";
          message = "Consider specifying document language";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage[english]{babel} or similar";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Font encoding *)
  let proper_font_encoding = {
    id = "I18N-002";
    name = "proper_font_encoding";
    description = "Use proper font encoding for international characters";
    severity = Warning;
    category = "i18n";
    check = fun tokens ->
      let has_fontenc = 
        let rec check_fontenc i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "fontenc", TGroupClose) -> true
            | _ -> check_fontenc (i + 1))
          | _ -> check_fontenc (i + 1)
        in check_fontenc 0 in
      
      let has_inputenc = 
        let rec check_inputenc i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "inputenc", TGroupClose) -> true
            | _ -> check_inputenc (i + 1))
          | _ -> check_inputenc (i + 1)
        in check_inputenc 0 in
      
      let has_unicode_chars = Array.exists (function
        | TChar (uc, _) when Uchar.to_int uc > 127 -> true
        | _ -> false
      ) tokens in
      
      if has_unicode_chars && not (has_fontenc || has_inputenc) then
        [{
          rule_id = "I18N-002";
          message = "Non-ASCII characters detected without proper encoding setup";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage[T1]{fontenc} and \\usepackage[utf8]{inputenc}";
          confidence = 0.9;
        }]
      else []
  }
end

(** Structure and navigation rules **)
module StructureNavigationRules = struct
  
  (* Rule: Logical heading structure *)
  let logical_heading_structure = {
    id = "NAV-001";
    name = "logical_heading_structure";
    description = "Maintain logical heading hierarchy for navigation";
    severity = Warning;
    category = "navigation";
    check = fun tokens ->
      let heading_levels = [
        ("part", -1);
        ("chapter", 0);
        ("section", 1);
        ("subsection", 2);
        ("subsubsection", 3);
        ("paragraph", 4);
      ] in
      let issues = ref [] in
      let previous_level = ref (-2) in
      
      Array.iter (function
        | TMacro name when List.mem_assoc name heading_levels ->
            let level = List.assoc name heading_levels in
            if level > !previous_level + 1 then
              issues := {
                rule_id = "NAV-001";
                message = Printf.sprintf "Heading level jump: %s after level %d" name !previous_level;
                location = Location.make 0 0;
                suggestion = Some "Use intermediate heading levels for logical structure";
                confidence = 0.9;
              } :: !issues;
            previous_level := level
        | _ -> ()
      ) tokens;
      
      List.rev !issues
  }
  
  (* Rule: Table of contents *)
  let table_of_contents = {
    id = "NAV-002";
    name = "table_of_contents";
    description = "Include table of contents for navigation";
    severity = Info;
    category = "navigation";
    check = fun tokens ->
      let has_toc = Array.exists (function
        | TMacro "tableofcontents" -> true
        | _ -> false
      ) tokens in
      
      let section_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name ["section"; "subsection"; "chapter"] -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if section_count > 5 && not has_toc then
        [{
          rule_id = "NAV-002";
          message = "Document with many sections should include table of contents";
          location = Location.make 0 0;
          suggestion = Some "Add \\tableofcontents after \\maketitle";
          confidence = 0.8;
        }]
      else []
  }
end

(** Link and cross-reference accessibility **)
module LinkAccessibilityRules = struct
  
  (* Rule: Descriptive link text *)
  let descriptive_links = {
    id = "LINK-001";
    name = "descriptive_links";
    description = "Use descriptive text for hyperlinks";
    severity = Info;
    category = "links";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "href" :: TGroupOpen :: url :: TGroupClose :: TGroupOpen :: text :: TGroupClose :: rest ->
            (* Check if link text is just URL *)
            (match (url, text) with
            | (TMacro url_str, TMacro text_str) when url_str = text_str ->
                issues := {
                  rule_id = "LINK-001";
                  message = "Link text should be descriptive, not just URL";
                  location = Location.make 0 0;
                  suggestion = Some "Use descriptive text: \\href{url}{descriptive text}";
                  confidence = 0.8;
                } :: !issues
            | _ -> ());
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Cross-reference clarity *)
  let clear_cross_references = {
    id = "LINK-002";
    name = "clear_cross_references";
    description = "Use clear cross-reference text";
    severity = Info;
    category = "links";
    check = fun tokens ->
      let bare_refs = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro "ref" -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      let contextual_refs = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name ["cref"; "Cref"; "autoref"] -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if bare_refs > contextual_refs * 2 then
        [{
          rule_id = "LINK-002";
          message = "Consider using \\cref{} or \\autoref{} for clearer references";
          location = Location.make 0 0;
          suggestion = Some "Use cleveref package: \\cref{fig:example} instead of \\ref{fig:example}";
          confidence = 0.7;
        }]
      else []
  }
end

(** Color and visual accessibility **)
module VisualAccessibilityRules = struct
  
  (* Rule: Color dependency *)
  let color_dependency = {
    id = "VIS-001";
    name = "color_dependency";
    description = "Avoid relying solely on color for meaning";
    severity = Warning;
    category = "visual";
    check = fun tokens ->
      let has_color_commands = Array.exists (function
        | TMacro name when List.mem name ["textcolor"; "color"; "colorbox"] -> true
        | _ -> false
      ) tokens in
      
      if has_color_commands then
        [{
          rule_id = "VIS-001";
          message = "Ensure information is not conveyed by color alone";
          location = Location.make 0 0;
          suggestion = Some "Use shapes, patterns, or text in addition to color";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Sufficient contrast *)
  let sufficient_contrast = {
    id = "VIS-002";
    name = "sufficient_contrast";
    description = "Ensure sufficient color contrast";
    severity = Info;
    category = "visual";
    check = fun tokens ->
      let light_colors = ["yellow"; "cyan"; "lightgray"; "white"] in
      let has_light_colors = Array.exists (function
        | TMacro name when List.mem name light_colors -> true
        | _ -> false
      ) tokens in
      
      if has_light_colors then
        [{
          rule_id = "VIS-002";
          message = "Light colors may have insufficient contrast";
          location = Location.make 0 0;
          suggestion = Some "Test color contrast ratios for accessibility compliance";
          confidence = 0.5;
        }]
      else []
  }
end

(** Collect all accessibility rules *)
let all_rules = [
  (* PDF Accessibility *)
  PDFAccessibilityRules.pdf_a_compliance;
  PDFAccessibilityRules.alt_text_graphics;
  PDFAccessibilityRules.document_metadata;
  
  (* Semantic markup *)
  SemanticMarkupRules.semantic_over_formatting;
  SemanticMarkupRules.proper_emphasis;
  SemanticMarkupRules.quote_environments;
  
  (* Internationalization *)
  InternationalizationRules.language_tagging;
  InternationalizationRules.proper_font_encoding;
  
  (* Structure and navigation *)
  StructureNavigationRules.logical_heading_structure;
  StructureNavigationRules.table_of_contents;
  
  (* Link accessibility *)
  LinkAccessibilityRules.descriptive_links;
  LinkAccessibilityRules.clear_cross_references;
  
  (* Visual accessibility *)
  VisualAccessibilityRules.color_dependency;
  VisualAccessibilityRules.sufficient_contrast;
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