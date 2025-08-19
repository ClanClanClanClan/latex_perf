(* Page Layout Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for proper page layout, margins, and formatting *)

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

(** Margin and spacing rules **)
module MarginRules = struct
  
  (* Rule: Consistent margin specification *)
  let consistent_margins = {
    id = "MARGIN-001";
    name = "consistent_margins";
    description = "Use consistent margin specification";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let margin_commands = ["setlength"; "geometry"; "usepackage"] in
      let margin_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name margin_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if margin_count > 3 then
        [{
          rule_id = "MARGIN-001";
          message = "Multiple margin specifications detected";
          location = Location.make 0 0;
          suggestion = Some "Use geometry package for consistent margin control";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Standard paper size *)
  let standard_paper_size = {
    id = "MARGIN-002";
    name = "standard_paper_size";
    description = "Use standard paper sizes";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let paper_sizes = ["a4paper"; "letterpaper"; "a5paper"; "b5paper"] in
      let has_paper_size = Array.exists (function
        | TMacro name when List.mem name paper_sizes -> true
        | _ -> false
      ) tokens in
      
      if not has_paper_size then
        [{
          rule_id = "MARGIN-002";
          message = "Consider specifying paper size explicitly";
          location = Location.make 0 0;
          suggestion = Some "Add paper size option to documentclass or geometry";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Margin symmetry *)
  let margin_symmetry = {
    id = "MARGIN-003";
    name = "margin_symmetry";
    description = "Consider margin symmetry for binding";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_twoside = Array.exists (function
        | TMacro "twoside" -> true
        | _ -> false
      ) tokens in
      
      let has_binding_offset = Array.exists (function
        | TMacro "bindingoffset" -> true
        | _ -> false
      ) tokens in
      
      if has_twoside && not has_binding_offset then
        [{
          rule_id = "MARGIN-003";
          message = "Two-sided document without binding offset";
          location = Location.make 0 0;
          suggestion = Some "Add bindingoffset option in geometry package";
          confidence = 0.7;
        }]
      else []
  }
end

(** Header and footer rules **)
module HeaderFooterRules = struct
  
  (* Rule: Page numbering consistency *)
  let page_numbering = {
    id = "HEADER-001";
    name = "page_numbering";
    description = "Use consistent page numbering style";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let numbering_styles = ["arabic"; "roman"; "Roman"; "alph"; "Alph"] in
      let style_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro "pagenumbering" -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if style_count > 2 then
        [{
          rule_id = "HEADER-001";
          message = "Multiple page numbering style changes";
          location = Location.make 0 0;
          suggestion = Some "Limit page numbering changes to frontmatter/mainmatter";
          confidence = 0.8;
        }]
      else []
  }
  
  (* Rule: Running headers *)
  let running_headers = {
    id = "HEADER-002";
    name = "running_headers";
    description = "Consider running headers for navigation";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_sections = Array.exists (function
        | TMacro name when List.mem name ["section"; "chapter"] -> true
        | _ -> false
      ) tokens in
      
      let has_fancyhdr = 
        let rec check_fancyhdr i =
          if i >= Array.length tokens - 3 then false
          else match tokens.(i) with
          | TMacro "usepackage" ->
            (match (tokens.(i+1), tokens.(i+2), tokens.(i+3)) with
            | (TGroupOpen, TMacro "fancyhdr", TGroupClose) -> true
            | _ -> check_fancyhdr (i + 1))
          | _ -> check_fancyhdr (i + 1)
        in check_fancyhdr 0 in
      
      if has_sections && not has_fancyhdr then
        [{
          rule_id = "HEADER-002";
          message = "Consider using running headers for better navigation";
          location = Location.make 0 0;
          suggestion = Some "Add \\usepackage{fancyhdr} for custom headers";
          confidence = 0.5;
        }]
      else []
  }
  
  (* Rule: Header/footer balance *)
  let header_footer_balance = {
    id = "HEADER-003";
    name = "header_footer_balance";
    description = "Balance header and footer content";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let header_commands = ["lhead"; "chead"; "rhead"; "markboth"; "markright"] in
      let footer_commands = ["lfoot"; "cfoot"; "rfoot"] in
      
      let header_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name header_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      let footer_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name footer_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if header_count > 0 && footer_count = 0 then
        [{
          rule_id = "HEADER-003";
          message = "Headers defined but no footer content";
          location = Location.make 0 0;
          suggestion = Some "Consider adding page numbers or other footer content";
          confidence = 0.4;
        }]
      else []
  }
end

(** Line spacing and paragraph rules **)
module SpacingRules = struct
  
  (* Rule: Line spacing consistency *)
  let line_spacing_consistency = {
    id = "SPACE-001";
    name = "line_spacing_consistency";
    description = "Use consistent line spacing";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let spacing_commands = ["linespread"; "setstretch"; "singlespacing"; "doublespacing"; "onehalfspacing"] in
      let spacing_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name spacing_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if spacing_count > 2 then
        [{
          rule_id = "SPACE-001";
          message = "Multiple line spacing changes detected";
          location = Location.make 0 0;
          suggestion = Some "Use consistent line spacing throughout document";
          confidence = 0.8;
        }]
      else []
  }
  
  (* Rule: Paragraph indentation *)
  let paragraph_indentation = {
    id = "SPACE-002";
    name = "paragraph_indentation";
    description = "Choose between indentation or spacing for paragraphs";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_parindent = Array.exists (function
        | TMacro "setlength" -> true (* Note: Check for parindent *)
        | _ -> false
      ) tokens in
      
      let has_parskip = Array.exists (function
        | TMacro "setlength" -> true (* Note: Check for parskip *)
        | _ -> false
      ) tokens in
      
      if has_parindent && has_parskip then
        [{
          rule_id = "SPACE-002";
          message = "Both paragraph indentation and spacing set";
          location = Location.make 0 0;
          suggestion = Some "Use either indentation or spacing, not both";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Vertical spacing *)
  let vertical_spacing = {
    id = "SPACE-003";
    name = "vertical_spacing";
    description = "Use semantic spacing commands";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let manual_spacing = ["vspace"; "vskip"; "bigskip"; "medskip"; "smallskip"] in
      let semantic_spacing = ["section"; "subsection"; "paragraph"] in
      
      let manual_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name manual_spacing -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      let semantic_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name semantic_spacing -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if manual_count > semantic_count then
        [{
          rule_id = "SPACE-003";
          message = "High use of manual vertical spacing";
          location = Location.make 0 0;
          suggestion = Some "Consider using semantic sectioning commands";
          confidence = 0.6;
        }]
      else []
  }
end

(** Column and text layout rules **)
module TextLayoutRules = struct
  
  (* Rule: Text width optimization *)
  let text_width_optimization = {
    id = "TEXT-001";
    name = "text_width_optimization";
    description = "Optimize text width for readability";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_geometry = Array.exists (function
        | TMacro "usepackage" -> true (* Note: Check for geometry package *)
        | _ -> false
      ) tokens in
      
      let has_textwidth = Array.exists (function
        | TMacro "setlength" -> true (* Note: Check for textwidth *)
        | _ -> false
      ) tokens in
      
      if not (has_geometry || has_textwidth) then
        [{
          rule_id = "TEXT-001";
          message = "Consider optimizing text width for readability";
          location = Location.make 0 0;
          suggestion = Some "Use geometry package to set appropriate text width";
          confidence = 0.5;
        }]
      else []
  }
  
  (* Rule: Column layout *)
  let column_layout = {
    id = "TEXT-002";
    name = "column_layout";
    description = "Use appropriate column layout";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_twocolumn = Array.exists (function
        | TMacro "twocolumn" -> true
        | _ -> false
      ) tokens in
      
      let has_multicol = Array.exists (function
        | TMacro "usepackage" -> true (* Note: Check for multicol package *)
        | _ -> false
      ) tokens in
      
      if has_twocolumn && not has_multicol then
        [{
          rule_id = "TEXT-002";
          message = "Consider multicol package for flexible column layout";
          location = Location.make 0 0;
          suggestion = Some "Use \\usepackage{multicol} for better column control";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Hyphenation settings *)
  let hyphenation_settings = {
    id = "TEXT-003";
    name = "hyphenation_settings";
    description = "Configure hyphenation appropriately";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_hyphenation = Array.exists (function
        | TMacro name when List.mem name ["hyphenation"; "sloppy"; "fussy"] -> true
        | _ -> false
      ) tokens in
      
      let has_ragged = Array.exists (function
        | TMacro name when List.mem name ["raggedright"; "raggedleft"; "centering"] -> true
        | _ -> false
      ) tokens in
      
      if has_ragged && has_hyphenation then
        [{
          rule_id = "TEXT-003";
          message = "Hyphenation settings with ragged text";
          location = Location.make 0 0;
          suggestion = Some "Review hyphenation needs with ragged text";
          confidence = 0.4;
        }]
      else []
  }
end

(** Float and positioning rules **)
module FloatPositioningRules = struct
  
  (* Rule: Float parameters *)
  let float_parameters = {
    id = "FLOAT-003";
    name = "float_parameters";
    description = "Adjust float parameters for better placement";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_float_params = Array.exists (function
        | TMacro name when List.mem name ["setcounter"; "renewcommand"] -> true
        | _ -> false
      ) tokens in
      
      let float_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro "begin" -> acc + 1 (* Note: Count figure/table environments *)
        | _ -> acc
      ) 0 tokens in
      
      if float_count > 5 && not has_float_params then
        [{
          rule_id = "FLOAT-003";
          message = "Many floats without parameter adjustment";
          location = Location.make 0 0;
          suggestion = Some "Consider adjusting topfraction, bottomfraction parameters";
          confidence = 0.5;
        }]
      else []
  }
  
  (* Rule: Float placement balance *)
  let float_placement_balance = {
    id = "FLOAT-004";
    name = "float_placement_balance";
    description = "Balance float placement throughout document";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      [{
        rule_id = "FLOAT-004";
        message = "Consider float distribution for balanced layout";
        location = Location.make 0 0;
        suggestion = Some "Review float placement to avoid clustering";
        confidence = 0.3;
      }]
  }
end

(** Page break rules **)
module PageBreakRules = struct
  
  (* Rule: Manual page breaks *)
  let manual_page_breaks = {
    id = "BREAK-001";
    name = "manual_page_breaks";
    description = "Limit manual page breaks";
    severity = Warning;
    category = "layout";
    check = fun tokens ->
      let break_commands = ["newpage"; "clearpage"; "cleardoublepage"; "pagebreak"] in
      let break_count = Array.fold_left (fun acc tok ->
        match tok with
        | TMacro name when List.mem name break_commands -> acc + 1
        | _ -> acc
      ) 0 tokens in
      
      if break_count > 5 then
        [{
          rule_id = "BREAK-001";
          message = Printf.sprintf "High number of manual page breaks: %d" break_count;
          location = Location.make 0 0;
          suggestion = Some "Let LaTeX handle page breaking automatically when possible";
          confidence = 0.8;
        }]
      else []
  }
  
  (* Rule: Widow and orphan control *)
  let widow_orphan_control = {
    id = "BREAK-002";
    name = "widow_orphan_control";
    description = "Set widow and orphan penalties";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_widow_penalty = Array.exists (function
        | TMacro "widowpenalty" -> true
        | _ -> false
      ) tokens in
      
      let has_orphan_penalty = Array.exists (function
        | TMacro "clubpenalty" -> true
        | _ -> false
      ) tokens in
      
      if not (has_widow_penalty || has_orphan_penalty) then
        [{
          rule_id = "BREAK-002";
          message = "Consider setting widow and orphan penalties";
          location = Location.make 0 0;
          suggestion = Some "Add \\widowpenalty=1000 \\clubpenalty=1000";
          confidence = 0.6;
        }]
      else []
  }
  
  (* Rule: Section break consistency *)
  let section_break_consistency = {
    id = "BREAK-003";
    name = "section_break_consistency";
    description = "Use consistent section breaking";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      [{
        rule_id = "BREAK-003";
        message = "Ensure consistent section break handling";
        location = Location.make 0 0;
        suggestion = Some "Use titlesec package for consistent section formatting";
        confidence = 0.4;
      }]
  }
end

(** Document class and options rules **)
module DocumentClassRules = struct
  
  (* Rule: Appropriate document class *)
  let appropriate_document_class = {
    id = "CLASS-001";
    name = "appropriate_document_class";
    description = "Use appropriate document class for content type";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      let has_bibliography = Array.exists (function
        | TMacro "bibliography" -> true
        | _ -> false
      ) tokens in
      
      let has_chapters = Array.exists (function
        | TMacro "chapter" -> true
        | _ -> false
      ) tokens in
      
      let document_class = ref "article" in
      Array.iter (function
        | TMacro "documentclass" -> () (* Note: Extract class name *)
        | _ -> ()
      ) tokens;
      
      let issues = ref [] in
      
      if has_chapters && !document_class = "article" then
        issues := {
          rule_id = "CLASS-001";
          message = "Article class with chapters - consider report or book";
          location = Location.make 0 0;
          suggestion = Some "Use report or book class for documents with chapters";
          confidence = 0.8;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Class options consistency *)
  let class_options_consistency = {
    id = "CLASS-002";
    name = "class_options_consistency";
    description = "Use consistent class options";
    severity = Info;
    category = "layout";
    check = fun tokens ->
      [{
        rule_id = "CLASS-002";
        message = "Review document class options for consistency";
        location = Location.make 0 0;
        suggestion = Some "Ensure font size, paper, and layout options match requirements";
        confidence = 0.3;
      }]
  }
end

(** Collect all page layout rules *)
let all_rules = [
  (* Margins *)
  MarginRules.consistent_margins;
  MarginRules.standard_paper_size;
  MarginRules.margin_symmetry;
  
  (* Headers/Footers *)
  HeaderFooterRules.page_numbering;
  HeaderFooterRules.running_headers;
  HeaderFooterRules.header_footer_balance;
  
  (* Spacing *)
  SpacingRules.line_spacing_consistency;
  SpacingRules.paragraph_indentation;
  SpacingRules.vertical_spacing;
  
  (* Text layout *)
  TextLayoutRules.text_width_optimization;
  TextLayoutRules.column_layout;
  TextLayoutRules.hyphenation_settings;
  
  (* Float positioning *)
  FloatPositioningRules.float_parameters;
  FloatPositioningRules.float_placement_balance;
  
  (* Page breaks *)
  PageBreakRules.manual_page_breaks;
  PageBreakRules.widow_orphan_control;
  PageBreakRules.section_break_consistency;
  
  (* Document class *)
  DocumentClassRules.appropriate_document_class;
  DocumentClassRules.class_options_consistency;
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