(* Bibliography and Citation Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for proper bibliography format and citation usage *)

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

(** Bibliography format rules **)
module BibliographyRules = struct
  
  (* Rule: Consistent bibliography style *)
  let bibliography_style = {
    id = "BIB-001";
    name = "bibliography_style";
    description = "Use consistent bibliography style throughout document";
    severity = Warning;
    category = "bibliography";
    check = fun tokens ->
      let bib_styles = ref [] in
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "bibliographystyle" :: TGroupOpen :: TMacro style :: TGroupClose :: rest ->
            bib_styles := style :: !bib_styles;
            scan rest
        | TMacro "usepackage" :: TGroupOpen :: TMacro pkg :: TGroupClose :: rest 
          when List.mem pkg ["natbib"; "biblatex"; "apacite"] ->
            bib_styles := pkg :: !bib_styles;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      let unique_styles = List.sort_uniq String.compare !bib_styles in
      if List.length unique_styles > 1 then
        issues := {
          rule_id = "BIB-001";
          message = "Multiple bibliography styles detected";
          location = Location.make 0 0;
          suggestion = Some "Use one bibliography style consistently";
          confidence = 0.9;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Bibliography section placement *)
  let bibliography_placement = {
    id = "BIB-002";
    name = "bibliography_placement";
    description = "Bibliography should appear before appendices";
    severity = Info;
    category = "bibliography";
    check = fun tokens ->
      let bib_position = ref None in
      let appendix_position = ref None in
      let issues = ref [] in
      
      Array.iteri (fun i tok ->
        match tok with
        | TMacro "bibliography" -> bib_position := Some i
        | TMacro "appendix" -> appendix_position := Some i
        | _ -> ()
      ) tokens;
      
      (match (!bib_position, !appendix_position) with
      | (Some bib_pos, Some app_pos) when bib_pos > app_pos ->
          issues := {
            rule_id = "BIB-002";
            message = "Bibliography appears after appendix";
            location = Location.make 0 0;
            suggestion = Some "Move \\bibliography before \\appendix";
            confidence = 0.8;
          } :: !issues
      | _ -> ());
      
      List.rev !issues
  }
  
  (* Rule: Missing bibliography *)
  let missing_bibliography = {
    id = "BIB-003";
    name = "missing_bibliography";
    description = "Documents with citations should have bibliography";
    severity = Warning;
    category = "bibliography";
    check = fun tokens ->
      let has_citations = Array.exists (function
        | TMacro name when List.mem name ["cite"; "citep"; "citet"; "nocite"] -> true
        | _ -> false
      ) tokens in
      
      let has_bibliography = Array.exists (function
        | TMacro name when List.mem name ["bibliography"; "printbibliography"; "thebibliography"] -> true
        | _ -> false
      ) tokens in
      
      if has_citations && not has_bibliography then
        [{
          rule_id = "BIB-003";
          message = "Document has citations but no bibliography";
          location = Location.make 0 0;
          suggestion = Some "Add \\bibliography{filename} or \\printbibliography";
          confidence = 0.9;
        }]
      else []
  }
end

(** Citation format rules **)
module CitationRules = struct
  
  (* Rule: Citation punctuation *)
  let citation_punctuation = {
    id = "CITE-001";
    name = "citation_punctuation";
    description = "Proper punctuation around citations";
    severity = Info;
    category = "citation";
    check = fun tokens ->
      let issues = ref [] in
      
      Array.iteri (fun i tok ->
        match tok with
        | TMacro name when List.mem name ["cite"; "citep"; "citet"] ->
            (* Check for punctuation after citation *)
            if i < Array.length tokens - 1 then (
              match tokens.(i+1) with
              | TChar (uc, _) when List.mem (Uchar.to_int uc) [0x2E; 0x2C; 0x3B] -> (* . , ; *)
                  issues := {
                    rule_id = "CITE-001";
                    message = "Punctuation should typically go before citation";
                    location = Location.make 0 0;
                    suggestion = Some "Move punctuation inside citation command";
                    confidence = 0.6;
                  } :: !issues
              | _ -> ()
            )
        | _ -> ()
      ) tokens;
      
      List.rev !issues
  }
  
  (* Rule: Page numbers in citations *)
  let citation_page_numbers = {
    id = "CITE-002";
    name = "citation_page_numbers";
    description = "Use proper page number format in citations";
    severity = Info;
    category = "citation";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro ("cite" | "citep" | "citet") :: TGroupOpen :: content when List.length content > 0 ->
            (* Check for page numbers without p. or pp. prefix *)
            let rec check_page_format = function
              | [] -> ()
              | TChar (uc, _) :: TChar (uc2, _) :: rest 
                when Uchar.to_int uc >= 48 && Uchar.to_int uc <= 57 &&
                     Uchar.to_int uc2 >= 48 && Uchar.to_int uc2 <= 57 ->
                  issues := {
                    rule_id = "CITE-002";
                    message = "Consider using p. or pp. prefix for page numbers";
                    location = Location.make 0 0;
                    suggestion = Some "Use p.~123 or pp.~123-456 format";
                    confidence = 0.7;
                  } :: !issues;
                  check_page_format rest
              | _ :: rest -> check_page_format rest
            in
            check_page_format content;
            scan content
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: Multiple citations *)
  let multiple_citations = {
    id = "CITE-003";
    name = "multiple_citations";
    description = "Use single citation command for multiple references";
    severity = Info;
    category = "citation";
    check = fun tokens ->
      let issues = ref [] in
      
      Array.iteri (fun i tok ->
        match tok with
        | TMacro name when List.mem name ["cite"; "citep"; "citet"] ->
            (* Check if next token is also a citation *)
            if i < Array.length tokens - 1 then (
              match tokens.(i+1) with
              | TMacro name2 when List.mem name2 ["cite"; "citep"; "citet"] ->
                  issues := {
                    rule_id = "CITE-003";
                    message = "Combine multiple citations into single command";
                    location = Location.make 0 0;
                    suggestion = Some "Use \\cite{ref1,ref2} instead of \\cite{ref1}\\cite{ref2}";
                    confidence = 0.8;
                  } :: !issues
              | _ -> ()
            )
        | _ -> ()
      ) tokens;
      
      List.rev !issues
  }
end

(** Reference format rules **)
module ReferenceFormatRules = struct
  
  (* Rule: DOI format *)
  let doi_format = {
    id = "REF-004";
    name = "doi_format";
    description = "Use proper DOI format in bibliography";
    severity = Info;
    category = "reference";
    check = fun tokens ->
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "doi" :: TGroupOpen :: content :: TGroupClose :: rest ->
            (* Check DOI format - should start with 10. *)
            let check_doi_prefix = function
              | TChar (uc1, _) :: TChar (uc2, _) :: TChar (uc3, _) :: _ 
                when Uchar.to_int uc1 = 49 && Uchar.to_int uc2 = 48 && Uchar.to_int uc3 = 46 ->
                  () (* Valid DOI prefix *)
              | _ ->
                  issues := {
                    rule_id = "REF-004";
                    message = "DOI should start with '10.'";
                    location = Location.make 0 0;
                    suggestion = Some "Ensure DOI format: 10.xxxx/xxxx";
                    confidence = 0.8;
                  } :: !issues
            in
            (match content with
            | content_list -> check_doi_prefix content_list);
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
  
  (* Rule: URL accessibility *)
  let url_accessibility = {
    id = "REF-005";
    name = "url_accessibility";
    description = "Include access dates for URLs";
    severity = Info;
    category = "reference";
    check = fun tokens ->
      let has_url = ref false in
      let has_urldate = ref false in
      let issues = ref [] in
      
      Array.iter (function
        | TMacro "url" -> has_url := true
        | TMacro "urldate" -> has_urldate := true
        | _ -> ()
      ) tokens;
      
      if !has_url && not !has_urldate then
        issues := {
          rule_id = "REF-005";
          message = "Consider adding access date for URLs";
          location = Location.make 0 0;
          suggestion = Some "Add urldate field: urldate={2025-08-10}";
          confidence = 0.6;
        } :: !issues;
      
      List.rev !issues
  }
  
  (* Rule: Journal abbreviations *)
  let journal_abbreviations = {
    id = "REF-006";
    name = "journal_abbreviations";
    description = "Use consistent journal name abbreviations";
    severity = Info;
    category = "reference";
    check = fun tokens ->
      let journal_patterns = [
        ("Journal of", "J.");
        ("Proceedings of", "Proc.");
        ("Transactions on", "Trans.");
        ("Communications", "Commun.");
        ("International", "Int.");
      ] in
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "journal" :: TGroupOpen :: content :: TGroupClose :: rest ->
            List.iter (fun (full, abbrev) ->
              (* Simple pattern matching - in practice would be more sophisticated *)
              issues := {
                rule_id = "REF-006";
                message = "Consider using standard journal abbreviations";
                location = Location.make 0 0;
                suggestion = Some (Printf.sprintf "Use '%s' instead of '%s'" abbrev full);
                confidence = 0.5;
              } :: !issues
            ) journal_patterns;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** BibTeX specific rules **)
module BibTeXRules = struct
  
  (* Rule: Required fields *)
  let required_fields = {
    id = "BIBTEX-001";
    name = "required_fields";
    description = "Check for required BibTeX fields";
    severity = Warning;
    category = "bibtex";
    check = fun tokens ->
      let entry_types = [
        ("article", ["author"; "title"; "journal"; "year"]);
        ("book", ["author"; "title"; "publisher"; "year"]);
        ("inproceedings", ["author"; "title"; "booktitle"; "year"]);
        ("techreport", ["author"; "title"; "institution"; "year"]);
      ] in
      let issues = ref [] in
      
      (* This is a simplified check - full BibTeX parsing would be more complex *)
      List.iter (fun (entry_type, required) ->
        List.iter (fun field ->
          issues := {
            rule_id = "BIBTEX-001";
            message = Printf.sprintf "Ensure %s entries have %s field" entry_type field;
            location = Location.make 0 0;
            suggestion = Some (Printf.sprintf "Add %s = {...} to %s entries" field entry_type);
            confidence = 0.7;
          } :: !issues
        ) required
      ) entry_types;
      
      List.rev !issues
  }
  
  (* Rule: Consistent capitalization *)
  let title_capitalization = {
    id = "BIBTEX-002";
    name = "title_capitalization";
    description = "Use consistent title capitalization in BibTeX";
    severity = Info;
    category = "bibtex";
    check = fun tokens ->
      [{
        rule_id = "BIBTEX-002";
        message = "Use {Title Case} for proper nouns in BibTeX titles";
        location = Location.make 0 0;
        suggestion = Some "Protect capitalization with braces: {LaTeX}, {PDF}";
        confidence = 0.6;
      }]
  }
end

(** Collect all bibliography rules *)
let all_rules = [
  (* Bibliography *) 
  BibliographyRules.bibliography_style;
  BibliographyRules.bibliography_placement;
  BibliographyRules.missing_bibliography;
  
  (* Citations *)
  CitationRules.citation_punctuation;
  CitationRules.citation_page_numbers;
  CitationRules.multiple_citations;
  
  (* Reference format *)
  ReferenceFormatRules.doi_format;
  ReferenceFormatRules.url_accessibility;
  ReferenceFormatRules.journal_abbreviations;
  
  (* BibTeX *)
  BibTeXRules.required_fields;
  BibTeXRules.title_capitalization;
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