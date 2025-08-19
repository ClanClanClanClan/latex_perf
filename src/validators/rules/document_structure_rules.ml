(* Document Structure Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for document organization, sectioning, and structure *)

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

(* Helper functions *)
let is_char c = function
  | TChar (uc, _) -> Uchar.to_int uc = Char.code c
  | _ -> false

let is_macro name = function
  | TMacro m -> m = name
  | _ -> false

(** Sectioning and hierarchy rules *)
module SectioningRules = struct
  
  (* Rule: Proper section hierarchy *)
  let section_hierarchy = {
    id = "STRUCT-001";
    name = "section_hierarchy";
    description = "Maintain proper sectioning hierarchy";
    severity = Warning;
    category = "structure";
    check = fun tokens ->
      let issues = ref [] in
      let current_level = ref 0 in
      let section_levels = [
        ("part", -1);
        ("chapter", 0);
        ("section", 1);
        ("subsection", 2);
        ("subsubsection", 3);
        ("paragraph", 4);
        ("subparagraph", 5);
      ] in
      
      Array.iter (function
        | TMacro name when List.mem_assoc name section_levels ->
            let level = List.assoc name section_levels in
            if level > !current_level + 1 then
              issues := {
                rule_id = "STRUCT-001";
                message = Printf.sprintf "Skipping section level: \\%s after level %d" name !current_level;
                location = Location.make 0 0;
                suggestion = Some "Use intermediate section levels";
                confidence = 0.9;
              } :: !issues;
            current_level := level
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Empty sections *)
  let empty_sections = {
    id = "STRUCT-002";
    name = "empty_sections";
    description = "Avoid empty sections without content";
    severity = Info;
    category = "structure";
    check = fun tokens ->
      let issues = ref [] in
      let in_section = ref false in
      let section_content = ref 0 in
      let section_name = ref "" in
      
      Array.iter (function
        | TMacro name when List.mem name ["section"; "subsection"; "subsubsection"] ->
            if !in_section && !section_content = 0 then
              issues := {
                rule_id = "STRUCT-002";
                message = Printf.sprintf "Empty section: \\%s" !section_name;
                location = Location.make 0 0;
                suggestion = Some "Add content or remove empty section";
                confidence = 0.8;
              } :: !issues;
            in_section := true;
            section_content := 0;
            section_name := name
        | TChar (_, _) -> if !in_section then incr section_content
        | TMacro _ -> if !in_section then incr section_content
        | _ -> ()
      ) tokens;
      List.rev !issues
  }
  
  (* Rule: Missing document class *)
  let document_class_required = {
    id = "STRUCT-003";
    name = "document_class";
    description = "Document must have \\documentclass";
    severity = Error;
    category = "structure";
    check = fun tokens ->
      let has_documentclass = Array.exists (is_macro "documentclass") tokens in
      if has_documentclass then []
      else [{
        rule_id = "STRUCT-003";
        message = "Missing \\documentclass declaration";
        location = Location.make 0 0;
        suggestion = Some "Add \\documentclass{article} or similar";
        confidence = 1.0;
      }]
  }
end

(** Environment validation rules *)
module EnvironmentRules = struct
  
  (* Rule: Matching begin/end pairs *)
  let matching_environments = {
    id = "ENV-001";
    name = "matching_environments";
    description = "Every \\begin must have matching \\end";
    severity = Error;
    category = "environment";
    check = fun tokens ->
      let issues = ref [] in
      let env_stack = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest ->
            env_stack := env :: !env_stack;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro env :: TGroupClose :: rest ->
            (match !env_stack with
            | top :: stack_rest when top = env ->
                env_stack := stack_rest
            | top :: _ ->
                issues := {
                  rule_id = "ENV-001";
                  message = Printf.sprintf "Mismatched environment: expected \\end{%s}, found \\end{%s}" top env;
                  location = Location.make 0 0;
                  suggestion = Some (Printf.sprintf "Use \\end{%s}" top);
                  confidence = 0.95;
                } :: !issues
            | [] ->
                issues := {
                  rule_id = "ENV-001";
                  message = Printf.sprintf "Unmatched \\end{%s}";
                  location = Location.make 0 0;
                  suggestion = Some "Remove extra \\end or add matching \\begin";
                  confidence = 0.9;
                } :: !issues);
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      (* Check for unclosed environments *)
      List.iter (fun env ->
        issues := {
          rule_id = "ENV-001";
          message = Printf.sprintf "Unclosed environment: \\begin{%s}" env;
          location = Location.make 0 0;
          suggestion = Some (Printf.sprintf "Add \\end{%s}" env);
          confidence = 0.95;
        } :: !issues
      ) !env_stack;
      
      List.rev !issues
  }
  
  (* Rule: Deprecated environments *)
  let deprecated_environments = {
    id = "ENV-002";
    name = "deprecated_environments";
    description = "Avoid deprecated LaTeX environments";
    severity = Warning;
    category = "environment";
    check = fun tokens ->
      let issues = ref [] in
      let deprecated = [
        ("eqnarray", "align");
        ("center", "centering command");
        ("flushleft", "raggedright command");
        ("flushright", "raggedleft command");
      ] in
      
      Array.iter (function
        | TMacro "begin" -> ()  (* Look ahead handled in main scan *)
        | _ -> ()
      ) tokens;
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest ->
            (match List.assoc_opt env deprecated with
            | Some replacement ->
                issues := {
                  rule_id = "ENV-002";
                  message = Printf.sprintf "Deprecated environment: %s" env;
                  location = Location.make 0 0;
                  suggestion = Some (Printf.sprintf "Use %s instead" replacement);
                  confidence = 0.8;
                } :: !issues
            | None -> ());
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Reference and citation rules *)
module ReferenceRules = struct
  
  (* Rule: Undefined references *)
  let undefined_references = {
    id = "REF-001";
    name = "undefined_references";
    description = "Check for undefined label references";
    severity = Error;
    category = "reference";
    check = fun tokens ->
      let labels = Hashtbl.create 100 in
      let refs = ref [] in
      let issues = ref [] in
      
      (* Collect labels and references *)
      let rec scan = function
        | [] -> ()
        | TMacro "label" :: TGroupOpen :: TMacro name :: TGroupClose :: rest ->
            Hashtbl.add labels name ();
            scan rest
        | TMacro ("ref" | "pageref" | "eqref") :: TGroupOpen :: TMacro name :: TGroupClose :: rest ->
            refs := name :: !refs;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      (* Check for undefined references *)
      List.iter (fun ref_name ->
        if not (Hashtbl.mem labels ref_name) then
          issues := {
            rule_id = "REF-001";
            message = Printf.sprintf "Undefined reference: %s" ref_name;
            location = Location.make 0 0;
            suggestion = Some (Printf.sprintf "Add \\label{%s} before reference" ref_name);
            confidence = 0.95;
          } :: !issues
      ) !refs;
      
      List.rev !issues
  }
  
  (* Rule: Non-breaking space before references *)
  let space_before_ref = {
    id = "REF-002";
    name = "space_before_ref";
    description = "Use ~ before references to prevent line breaks";
    severity = Info;
    category = "reference";
    check = fun tokens ->
      let issues = ref [] in
      
      Array.iteri (fun i tok ->
        match tok with
        | TMacro ("ref" | "pageref" | "eqref") when i > 0 ->
            (match tokens.(i-1) with
            | TChar (uc, _) when Uchar.to_int uc = 0x20 -> (* space *)
                issues := {
                  rule_id = "REF-002";
                  message = "Use ~ before reference to prevent line break";
                  location = Location.make 0 0;
                  suggestion = Some "Replace space with ~";
                  confidence = 0.8;
                } :: !issues
            | _ -> ())
        | _ -> ()
      ) tokens;
      
      List.rev !issues
  }
  
  (* Rule: Citation format consistency *)
  let citation_format = {
    id = "REF-003";
    name = "citation_format";
    description = "Use consistent citation commands";
    severity = Info;
    category = "reference";
    check = fun tokens ->
      let citations = Hashtbl.create 20 in
      let issues = ref [] in
      
      Array.iter (function
        | TMacro name when List.mem name ["cite"; "citep"; "citet"; "citealp"; "citealt"] ->
            let count = try Hashtbl.find citations name with Not_found -> 0 in
            Hashtbl.replace citations name (count + 1)
        | _ -> ()
      ) tokens;
      
      let cite_types = Hashtbl.fold (fun k v acc -> (k, v) :: acc) citations [] in
      if List.length cite_types > 1 then
        issues := {
          rule_id = "REF-003";
          message = "Mixed citation styles detected";
          location = Location.make 0 0;
          suggestion = Some "Use consistent citation commands throughout";
          confidence = 0.7;
        } :: !issues;
      
      List.rev !issues
  }
end

(** Package and preamble rules *)
module PreambleRules = struct
  
  (* Rule: Package loading order *)
  let package_order = {
    id = "PKG-001";
    name = "package_order";
    description = "Load packages in recommended order";
    severity = Warning;
    category = "preamble";
    check = fun tokens ->
      let issues = ref [] in
      let early_packages = ["inputenc"; "fontenc"; "babel"; "polyglossia"] in
      let late_packages = ["hyperref"; "cleveref"] in
      let seen_early = ref false in
      let seen_late = ref false in
      
      let rec scan = function
        | [] -> ()
        | TMacro "usepackage" :: TGroupOpen :: TMacro pkg :: TGroupClose :: rest ->
            if List.mem pkg late_packages then seen_late := true;
            if !seen_late && List.mem pkg early_packages then
              issues := {
                rule_id = "PKG-001";
                message = Printf.sprintf "Package %s should be loaded earlier" pkg;
                location = Location.make 0 0;
                suggestion = Some "Move package to top of preamble";
                confidence = 0.8;
              } :: !issues;
            if List.mem pkg early_packages then seen_early := true;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Conflicting packages *)
  let conflicting_packages = {
    id = "PKG-002";
    name = "conflicting_packages";
    description = "Detect conflicting package combinations";
    severity = Error;
    category = "preamble";
    check = fun tokens ->
      let packages = ref [] in
      let issues = ref [] in
      let conflicts = [
        (["babel"; "polyglossia"], "Choose either babel or polyglossia, not both");
        (["natbib"; "biblatex"], "Choose either natbib or biblatex, not both");
        (["fancyhdr"; "scrpage2"], "fancyhdr and scrpage2 conflict");
      ] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "usepackage" :: TGroupOpen :: TMacro pkg :: TGroupClose :: rest ->
            packages := pkg :: !packages;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      List.iter (fun (conflict_group, message) ->
        let found = List.filter (fun pkg -> List.mem pkg !packages) conflict_group in
        if List.length found > 1 then
          issues := {
            rule_id = "PKG-002";
            message;
            location = Location.make 0 0;
            suggestion = Some "Remove conflicting packages";
            confidence = 0.9;
          } :: !issues
      ) conflicts;
      
      List.rev !issues
  }
end

(** Collect all document structure rules *)
let all_rules = [
  (* Sectioning *)
  SectioningRules.section_hierarchy;
  SectioningRules.empty_sections;
  SectioningRules.document_class_required;
  
  (* Environments *)
  EnvironmentRules.matching_environments;
  EnvironmentRules.deprecated_environments;
  
  (* References *)
  ReferenceRules.undefined_references;
  ReferenceRules.space_before_ref;
  ReferenceRules.citation_format;
  
  (* Preamble *)
  PreambleRules.package_order;
  PreambleRules.conflicting_packages;
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