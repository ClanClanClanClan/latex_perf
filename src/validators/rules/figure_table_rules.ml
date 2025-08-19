(* Figure and Table Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for proper figure and table formatting *)

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

(** Figure placement and format rules **)
module FigureRules = struct
  
  (* Rule: Figure captions *)
  let figure_captions = {
    id = "FIG-001";
    name = "figure_captions";
    description = "All figures should have captions";
    severity = Warning;
    category = "figure";
    check = fun tokens ->
      let figures = ref [] in
      let captions = ref [] in
      let issues = ref [] in
      let in_figure = ref false in
      let current_figure_has_caption = ref false in
      
      let rec scan = function
        | [] -> 
            if !in_figure && not !current_figure_has_caption then
              issues := {
                rule_id = "FIG-001";
                message = "Figure environment without caption";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} to figure";
                confidence = 0.9;
              } :: !issues
        | TMacro "begin" :: TGroupOpen :: TMacro "figure" :: TGroupClose :: rest ->
            in_figure := true;
            current_figure_has_caption := false;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro "figure" :: TGroupClose :: rest ->
            if !in_figure && not !current_figure_has_caption then
              issues := {
                rule_id = "FIG-001";
                message = "Figure environment without caption";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} to figure";
                confidence = 0.9;
              } :: !issues;
            in_figure := false;
            scan rest
        | TMacro "caption" :: rest when !in_figure ->
            current_figure_has_caption := true;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Figure placement specifiers *)
  let figure_placement = {
    id = "FIG-002";
    name = "figure_placement";
    description = "Use appropriate figure placement specifiers";
    severity = Info;
    category = "figure";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro "figure" :: TGroupClose :: rest ->
            (* Check if placement specifier follows *)
            (match rest with
            | TOptionalArg _ :: _ -> () (* Has placement specifier *)
            | _ -> 
                issues := {
                  rule_id = "FIG-002";
                  message = "Consider adding placement specifier to figure";
                  location = Location.make 0 0;
                  suggestion = Some "Use \\begin{figure}[htbp] or similar";
                  confidence = 0.6;
                } :: !issues);
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Figure references *)
  let figure_references = {
    id = "FIG-003";
    name = "figure_references";
    description = "Figures should be referenced in text";
    severity = Info;
    category = "figure";
    check = fun tokens ->
      let figure_labels = ref [] in
      let figure_refs = ref [] in
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "label" :: TGroupOpen :: TMacro label :: TGroupClose :: rest 
          when String.length label >= 4 && String.sub label 0 4 = "fig:" ->
            figure_labels := label :: !figure_labels;
            scan rest
        | TMacro "ref" :: TGroupOpen :: TMacro label :: TGroupClose :: rest
          when String.length label >= 4 && String.sub label 0 4 = "fig:" ->
            figure_refs := label :: !figure_refs;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      (* Check for unreferenced figures *)
      List.iter (fun label ->
        if not (List.mem label !figure_refs) then
          issues := {
            rule_id = "FIG-003";
            message = Printf.sprintf "Figure %s is not referenced in text" label;
            location = Location.make 0 0;
            suggestion = Some (Printf.sprintf "Add \\ref{%s} in text" label);
            confidence = 0.8;
          } :: !issues
      ) !figure_labels;
      
      List.rev !issues
  }
  
  (* Rule: Graphics file format *)
  let graphics_format = {
    id = "FIG-004";
    name = "graphics_format";
    description = "Use appropriate graphics formats";
    severity = Info;
    category = "figure";
    check = fun tokens ->
      let issues = ref [] in
      let vector_formats = ["pdf"; "eps"; "svg"] in
      let raster_formats = ["png"; "jpg"; "jpeg"] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "includegraphics" :: rest ->
            (* Look for file extension in following tokens *)
            let rec find_extension = function
              | [] -> ()
              | TMacro filename :: rest2 ->
                  (try
                    let dot_pos = String.rindex filename '.' in
                    let ext = String.sub filename (dot_pos + 1) (String.length filename - dot_pos - 1) in
                    let ext_lower = String.lowercase_ascii ext in
                    if List.mem ext_lower raster_formats then
                      issues := {
                        rule_id = "FIG-004";
                        message = Printf.sprintf "Consider vector format instead of %s" ext;
                        location = Location.make 0 0;
                        suggestion = Some "Use PDF, EPS, or SVG for scalable graphics";
                        confidence = 0.6;
                      } :: !issues
                  with Not_found -> ());
                  find_extension rest2
              | _ :: rest2 -> find_extension rest2
            in
            find_extension rest;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Table format and structure rules **)
module TableRules = struct
  
  (* Rule: Table captions *)
  let table_captions = {
    id = "TBL-001";
    name = "table_captions";
    description = "All tables should have captions";
    severity = Warning;
    category = "table";
    check = fun tokens ->
      let issues = ref [] in
      let in_table = ref false in
      let current_table_has_caption = ref false in
      
      let rec scan = function
        | [] ->
            if !in_table && not !current_table_has_caption then
              issues := {
                rule_id = "TBL-001";
                message = "Table environment without caption";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} to table";
                confidence = 0.9;
              } :: !issues
        | TMacro "begin" :: TGroupOpen :: TMacro "table" :: TGroupClose :: rest ->
            in_table := true;
            current_table_has_caption := false;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro "table" :: TGroupClose :: rest ->
            if !in_table && not !current_table_has_caption then
              issues := {
                rule_id = "TBL-001";
                message = "Table environment without caption";
                location = Location.make 0 0;
                suggestion = Some "Add \\caption{...} to table";
                confidence = 0.9;
              } :: !issues;
            in_table := false;
            scan rest
        | TMacro "caption" :: rest when !in_table ->
            current_table_has_caption := true;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Table column alignment *)
  let column_alignment = {
    id = "TBL-002";
    name = "column_alignment";
    description = "Use appropriate column alignment in tables";
    severity = Info;
    category = "table";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro "tabular" :: TGroupClose :: TGroupOpen :: alignment :: TGroupClose :: rest ->
            (* Check alignment specification *)
            let check_alignment_string = function
              | TMacro align_spec ->
                  let has_left = String.contains align_spec 'l' in
                  let has_center = String.contains align_spec 'c' in
                  let has_right = String.contains align_spec 'r' in
                  if not (has_left || has_center || has_right) then
                    issues := {
                      rule_id = "TBL-002";
                      message = "Table alignment should specify l, c, or r";
                      location = Location.make 0 0;
                      suggestion = Some "Use l (left), c (center), or r (right) alignment";
                      confidence = 0.8;
                    } :: !issues
              | _ -> ()
            in
            check_alignment_string alignment;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Professional table formatting *)
  let professional_tables = {
    id = "TBL-003";
    name = "professional_tables";
    description = "Use booktabs package for professional tables";
    severity = Info;
    category = "table";
    check = fun tokens ->
      let has_booktabs = Array.exists (function
        | TMacro "usepackage" -> true (* Note: Check if booktabs is loaded *)
        | _ -> false
      ) tokens in
      
      let has_hline = Array.exists (function
        | TMacro "hline" -> true
        | _ -> false
      ) tokens in
      
      if has_hline && not has_booktabs then
        [{
          rule_id = "TBL-003";
          message = "Consider using booktabs package for professional tables";
          location = Location.make 0 0;
          suggestion = Some "Use \\toprule, \\midrule, \\bottomrule instead of \\hline";
          confidence = 0.7;
        }]
      else []
  }
  
  (* Rule: Table width *)
  let table_width = {
    id = "TBL-004";
    name = "table_width";
    description = "Consider table width for readability";
    severity = Info;
    category = "table";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro "tabular" :: TGroupClose :: TGroupOpen :: alignment :: TGroupClose :: rest ->
            (* Count columns in alignment *)
            let count_columns = function
              | TMacro align_spec ->
                  let cols = ref 0 in
                  String.iter (function
                    | 'l' | 'c' | 'r' | 'p' -> incr cols
                    | _ -> ()
                  ) align_spec;
                  !cols
              | _ -> 0
            in
            let col_count = count_columns alignment in
            if col_count > 8 then
              issues := {
                rule_id = "TBL-004";
                message = Printf.sprintf "Table has %d columns - consider splitting" col_count;
                location = Location.make 0 0;
                suggestion = Some "Use tabularx or split into multiple tables";
                confidence = 0.6;
              } :: !issues;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Float positioning rules **)
module FloatRules = struct
  
  (* Rule: Float positioning best practices *)
  let float_positioning = {
    id = "FLOAT-001";
    name = "float_positioning";
    description = "Use appropriate float positioning";
    severity = Info;
    category = "float";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: TOptionalArg pos :: rest
          when List.mem env ["figure"; "table"] ->
            (* Check for problematic positioning *)
            (match pos with
            | TMacro "h" -> 
                issues := {
                  rule_id = "FLOAT-001";
                  message = "Avoid 'h' alone - use 'htbp' for better placement";
                  location = Location.make 0 0;
                  suggestion = Some "Use [htbp] or [htb] for flexible placement";
                  confidence = 0.8;
                } :: !issues
            | TMacro "H" ->
                issues := {
                  rule_id = "FLOAT-001";
                  message = "Use 'H' sparingly - may cause spacing issues";
                  location = Location.make 0 0;
                  suggestion = Some "Consider [htbp] unless absolute positioning required";
                  confidence = 0.6;
                } :: !issues
            | _ -> ());
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Float-to-text ratio *)
  let float_ratio = {
    id = "FLOAT-002";
    name = "float_ratio";
    description = "Maintain reasonable float-to-text ratio";
    severity = Info;
    category = "float";
    check = fun tokens ->
      let float_count = ref 0 in
      let text_tokens = ref 0 in
      
      Array.iter (function
        | TMacro "begin" when List.mem "figure" (Array.to_list tokens) || List.mem "table" (Array.to_list tokens) ->
            incr float_count
        | TChar (_, _) -> incr text_tokens
        | _ -> ()
      ) tokens;
      
      let ratio = if !text_tokens > 0 then float !float_count /. float !text_tokens else 0.0 in
      if ratio > 0.1 then
        [{
          rule_id = "FLOAT-002";
          message = Printf.sprintf "High float-to-text ratio: %.2f" ratio;
          location = Location.make 0 0;
          suggestion = Some "Consider reducing number of figures/tables or adding more text";
          confidence = 0.5;
        }]
      else []
  }
end

(** Caption style rules **)
module CaptionRules = struct
  
  (* Rule: Caption punctuation *)
  let caption_punctuation = {
    id = "CAP-001";
    name = "caption_punctuation";
    description = "Use consistent caption punctuation";
    severity = Info;
    category = "caption";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "caption" :: TGroupOpen :: content :: TGroupClose :: rest ->
            (* Check if caption ends with period *)
            let rec check_ending = function
              | [] -> 
                  issues := {
                    rule_id = "CAP-001";
                    message = "Consider ending captions with periods";
                    location = Location.make 0 0;
                    suggestion = Some "Add period at end of caption";
                    confidence = 0.6;
                  } :: !issues
              | [TChar (uc, _)] when Uchar.to_int uc = 0x2E -> () (* Ends with period *)
              | _ :: rest -> check_ending rest
            in
            (match content with
            | content_list -> check_ending content_list);
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Caption length *)
  let caption_length = {
    id = "CAP-002";
    name = "caption_length";
    description = "Keep captions concise but descriptive";
    severity = Info;
    category = "caption";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "caption" :: TGroupOpen :: content :: TGroupClose :: rest ->
            (* Count words in caption (simplified) *)
            let word_count = ref 0 in
            let rec count_words = function
              | [] -> ()
              | TChar (uc, _) :: rest when Uchar.to_int uc = 0x20 -> (* space *)
                  incr word_count;
                  count_words rest
              | _ :: rest -> count_words rest
            in
            (match content with
            | content_list -> count_words content_list);
            if !word_count < 3 then
              issues := {
                rule_id = "CAP-002";
                message = "Caption may be too brief";
                location = Location.make 0 0;
                suggestion = Some "Add more descriptive text to caption";
                confidence = 0.5;
              } :: !issues
            else if !word_count > 30 then
              issues := {
                rule_id = "CAP-002";
                message = "Caption may be too long";
                location = Location.make 0 0;
                suggestion = Some "Consider moving details to main text";
                confidence = 0.5;
              } :: !issues;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Collect all figure and table rules *)
let all_rules = [
  (* Figures *)
  FigureRules.figure_captions;
  FigureRules.figure_placement;
  FigureRules.figure_references;
  FigureRules.graphics_format;
  
  (* Tables *)
  TableRules.table_captions;
  TableRules.column_alignment;
  TableRules.professional_tables;
  TableRules.table_width;
  
  (* Floats *)
  FloatRules.float_positioning;
  FloatRules.float_ratio;
  
  (* Captions *)
  CaptionRules.caption_punctuation;
  CaptionRules.caption_length;
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