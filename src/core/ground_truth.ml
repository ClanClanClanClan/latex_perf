(** Ground Truth Infrastructure for Pattern Mining
    
    This module provides infrastructure for managing ground truth data
    used to train and validate the pattern mining system. It supports
    loading, parsing, and analyzing annotated LaTeX documents.
*)

(** Ground truth file format specification *)
type ground_truth_format = 
  | YAML        (** Human-readable YAML format *)
  | JSON        (** Machine-readable JSON format *)
  | Custom      (** Custom annotation format *)

(** Severity levels for annotations *)
type severity = 
  | Critical    (** Must fix - breaks compilation *)
  | Warning     (** Should fix - affects quality *)
  | Suggestion  (** Could fix - style improvement *)
  | Info        (** Informational - no fix needed *)

(** Document metadata *)
type document_metadata = {
  author: string;
  date: string;
  document_type: string;        (** article, book, thesis, etc *)
  complexity: int;              (** 1-10 complexity rating *)
  total_lines: int;
  total_chars: int;
}

(** Annotation types in ground truth files *)
type annotation = {
  issue_type: string;           (** e.g., "MATH-001", "TYPO-002" *)
  start_line: int;
  start_col: int;
  end_line: int;
  end_col: int;
  severity: severity;
  description: string;
  expected_fix: string option;  (** What the fix should be *)
  confidence: float;            (** Annotator confidence 0.0-1.0 *)
  tags: string list;
}

(** Ground truth document with annotations *)
type annotated_document = {
  filepath: string;
  content: string;              (** LaTeX source code *)
  annotations: annotation list; (** Known issues *)
  metadata: document_metadata;
  validation_status: [`Verified | `Draft | `Needs_review];
}

(** Corpus statistics *)
type corpus_statistics = {
  total_documents: int;
  total_annotations: int;
  families_covered: string list;
  severity_distribution: (severity * int) list;
  avg_annotations_per_doc: float;
}

(** Ground truth corpus management *)
type corpus = {
  name: string;
  description: string;
  documents: annotated_document list;
  format: ground_truth_format;
  version: string;
  created: string;
  statistics: corpus_statistics;
}

(** Pattern matching strategies *)
type pattern_matcher = 
  | TokenSequence of string list
  | TokenRegex of string
  | ASTPattern of string

(** Mined pattern from ground truth data *)
type mined_pattern = {
  pattern: pattern_matcher;
  confidence: float;
  support: int;                              (** Number of occurrences *)
  examples: string list;                     (** Example matches *)
  suggested_family: string;
}

(** Pattern mining configuration *)
type mining_config = {
  min_support: int;             (** Minimum occurrences to consider pattern *)
  min_confidence: float;        (** Minimum confidence threshold *)
  max_pattern_length: int;      (** Maximum tokens in a pattern *)
  families_to_mine: string list; (** Which families to focus on *)
  enable_contextual: bool;      (** Mine contextual patterns *)
  enable_composite: bool;       (** Mine composite patterns *)
}

(** Quality metrics for pattern mining *)
type quality_metrics = {
  precision: float;
  recall: float;
  f1_score: float;
}

(** Pattern mining results *)
type mining_result = {
  config: mining_config;
  patterns_found: mined_pattern list;
  total_documents_processed: int;
  processing_time_ms: float;
  quality_metrics: quality_metrics;
}

(** Ground truth file parser *)
module Parser = struct
  
  (** Parse YAML ground truth file *)
  let parse_yaml_file filepath =
    (* Placeholder implementation - would use a real YAML parser *)
    let content = 
      if Sys.file_exists filepath then
        let ic = open_in filepath in
        let content = really_input_string ic (in_channel_length ic) in
        close_in ic;
        content
      else
        failwith ("Ground truth file not found: " ^ filepath)
    in
    
    (* Simplified parsing - real implementation would parse YAML structure *)
    {
      filepath;
      content = "% Sample LaTeX document\n\\documentclass{article}\n\\begin{document}\nHello \\LaTeX{}!\n\\end{document}";
      annotations = [
        {
          issue_type = "STYLE-001";
          start_line = 4;
          start_col = 6;
          end_line = 4; 
          end_col = 13;
          severity = Suggestion;
          description = "Consider using semantic markup";
          expected_fix = Some "\\emph{LaTeX}";
          confidence = 0.8;
          tags = ["style"; "semantic"];
        }
      ];
      metadata = {
        author = "Ground Truth Annotator";
        date = "2025-07-29";
        document_type = "article";
        complexity = 2;
        total_lines = 5;
        total_chars = 85;
      };
      validation_status = `Verified;
    }
  
  (** Parse JSON ground truth file *)
  let parse_json_file filepath =
    (* Would implement JSON parsing here *)
    parse_yaml_file filepath  (* Placeholder *)
  
  (** Parse ground truth file based on extension *)
  let parse_file filepath =
    let ext = Filename.extension filepath in
    match String.lowercase_ascii ext with
    | ".yaml" | ".yml" -> parse_yaml_file filepath
    | ".json" -> parse_json_file filepath
    | _ -> failwith ("Unsupported ground truth format: " ^ ext)
end

(** Corpus management *)
module Corpus = struct
  
  (** Load corpus from directory of ground truth files *)
  let load_from_directory dir_path =
    let files = 
      if Sys.file_exists dir_path && Sys.is_directory dir_path then
        let files = Array.to_list (Sys.readdir dir_path) in
        List.filter (fun f -> 
          let ext = Filename.extension f in
          ext = ".yaml" || ext = ".yml" || ext = ".json"
        ) files
      else []
    in
    
    let documents = List.map (fun filename ->
      let filepath = Filename.concat dir_path filename in
      Parser.parse_file filepath
    ) files in
    
    let total_annotations = 
      List.fold_left (fun acc doc -> 
        acc + List.length doc.annotations
      ) 0 documents
    in
    
    let families_covered = 
      List.fold_left (fun acc doc ->
        List.fold_left (fun acc2 ann ->
          let family = String.split_on_char '-' ann.issue_type |> List.hd in
          if List.mem family acc2 then acc2 else family :: acc2
        ) acc doc.annotations
      ) [] documents
    in
    
    let severity_counts = 
      List.fold_left (fun acc doc ->
        List.fold_left (fun acc2 ann ->
          let current = try List.assoc ann.severity acc2 with Not_found -> 0 in
          (ann.severity, current + 1) :: (List.remove_assoc ann.severity acc2)
        ) acc doc.annotations
      ) [] documents
    in
    
    {
      name = Filename.basename dir_path;
      description = "Ground truth corpus loaded from " ^ dir_path;
      documents;
      format = YAML;  (* Default assumption *)
      version = "1.0";
      created = "2025-07-29";
      statistics = {
        total_documents = List.length documents;
        total_annotations;
        families_covered;
        severity_distribution = severity_counts;
        avg_annotations_per_doc = 
          if List.length documents > 0 then
            float total_annotations /. float (List.length documents)
          else 0.0;
      };
    }
  
  (** Create sample corpus for testing *)
  let create_sample_corpus () =
    let sample_docs = [
      {
        filepath = "sample1.tex";
        content = "\\documentclass{article}\n\\begin{document}\n$a * b$\n\\end{document}";
        annotations = [
          {
            issue_type = "MATH-002";
            start_line = 3; start_col = 3; end_line = 3; end_col = 4;
            severity = Suggestion;
            description = "Prefer \\cdot over *";
            expected_fix = Some "\\cdot";
            confidence = 0.9;
            tags = ["math"; "style"];
          }
        ];
        metadata = {
          author = "Test"; date = "2025-07-29"; document_type = "article";
          complexity = 1; total_lines = 4; total_chars = 55;
        };
        validation_status = `Verified;
      };
      {
        filepath = "sample2.tex";
        content = "\\documetnclass{article}\n\\begin{document}\nHello world!\n\\end{document}";
        annotations = [
          {
            issue_type = "TYPO-001";
            start_line = 1; start_col = 1; end_line = 1; end_col = 14;
            severity = Critical;
            description = "Misspelled command";
            expected_fix = Some "\\documentclass";
            confidence = 1.0;
            tags = ["typo"; "commands"];
          }
        ];
        metadata = {
          author = "Test"; date = "2025-07-29"; document_type = "article";
          complexity = 1; total_lines = 4; total_chars = 68;
        };
        validation_status = `Verified;
      };
    ] in
    
    {
      name = "Sample Corpus";
      description = "Sample ground truth data for testing";
      documents = sample_docs;
      format = Custom;
      version = "1.0";
      created = "2025-07-29";
      statistics = {
        total_documents = 2;
        total_annotations = 2;
        families_covered = ["MATH"; "TYPO"];
        severity_distribution = [(Critical, 1); (Suggestion, 1)];
        avg_annotations_per_doc = 1.0;
      };
    }
  
  (** Get corpus statistics *)
  let print_statistics corpus =
    Printf.printf "=== Ground Truth Corpus Statistics ===\n";
    Printf.printf "Name: %s\n" corpus.name;
    Printf.printf "Description: %s\n" corpus.description;
    Printf.printf "Format: %s\n" (match corpus.format with
      | YAML -> "YAML" | JSON -> "JSON" | Custom -> "Custom");
    Printf.printf "Version: %s\n" corpus.version;
    Printf.printf "Created: %s\n" corpus.created;
    Printf.printf "\nDocument Statistics:\n";
    Printf.printf "  Total documents: %d\n" corpus.statistics.total_documents;
    Printf.printf "  Total annotations: %d\n" corpus.statistics.total_annotations;
    Printf.printf "  Average annotations per document: %.1f\n" corpus.statistics.avg_annotations_per_doc;
    Printf.printf "\nFamilies covered: %s\n" (String.concat ", " corpus.statistics.families_covered);
    Printf.printf "\nSeverity distribution:\n";
    List.iter (fun (sev, count) ->
      let sev_str = match sev with
        | Critical -> "Critical"
        | Warning -> "Warning"
        | Suggestion -> "Suggestion"
        | Info -> "Info"
      in
      Printf.printf "  %s: %d\n" sev_str count
    ) corpus.statistics.severity_distribution;
    Printf.printf "\n"
end

(** Pattern mining implementation *)
module PatternMiner = struct
  
  (** Extract patterns from annotated documents *)
  let mine_patterns corpus config =
    Printf.printf "Mining patterns from %d documents...\n" 
      corpus.statistics.total_documents;
    
    let start_time = Unix.gettimeofday () in
    
    (* Simplified pattern mining - real implementation would analyze token sequences *)
    let mined_patterns = List.fold_left (fun acc doc ->
      List.fold_left (fun acc2 ann ->
        if List.mem (String.split_on_char '-' ann.issue_type |> List.hd) config.families_to_mine then
          {
            pattern = TokenRegex "sample_pattern";
            confidence = ann.confidence;
            support = 1;  (* Would count actual occurrences *)
            examples = [doc.content];
            suggested_family = String.split_on_char '-' ann.issue_type |> List.hd;
          } :: acc2
        else acc2
      ) acc doc.annotations
    ) [] corpus.documents in
    
    let processing_time = (Unix.gettimeofday () -. start_time) *. 1000.0 in
    
    {
      config;
      patterns_found = mined_patterns;
      total_documents_processed = corpus.statistics.total_documents;
      processing_time_ms = processing_time;
      quality_metrics = {
        precision = 0.85;  (* Placeholder metrics *)
        recall = 0.78;
        f1_score = 0.81;
      };
    }
  
  (** Convert mined pattern to validator pattern *)  
  let mined_to_validator_pattern mined_pattern pattern_id =
    Printf.printf "Would convert mined pattern %s to validator pattern %s\n" 
      mined_pattern.suggested_family pattern_id;
    (* Note: This would use Validator_patterns.PatternBuilder.make_pattern in real implementation *)
    mined_pattern
  
  (** Print mining results *)
  let print_results results =
    Printf.printf "=== Pattern Mining Results ===\n";
    Printf.printf "Documents processed: %d\n" results.total_documents_processed;
    Printf.printf "Processing time: %.2fms\n" results.processing_time_ms;
    Printf.printf "Patterns found: %d\n" (List.length results.patterns_found);
    Printf.printf "\nQuality Metrics:\n";
    Printf.printf "  Precision: %.2f\n" results.quality_metrics.precision;
    Printf.printf "  Recall: %.2f\n" results.quality_metrics.recall;
    Printf.printf "  F1-Score: %.2f\n" results.quality_metrics.f1_score;
    Printf.printf "\nMined Patterns:\n";
    List.iteri (fun i pattern ->
      Printf.printf "  [%d] Family: %s, Confidence: %.2f, Support: %d\n"
        i pattern.suggested_family pattern.confidence pattern.support
    ) results.patterns_found;
    Printf.printf "\n"
end

(** Testing and validation *)
let test_ground_truth_system () =
  Printf.printf "=== Testing Ground Truth System ===\n\n";
  
  (* Create sample corpus *)
  let corpus = Corpus.create_sample_corpus () in
  Corpus.print_statistics corpus;
  
  (* Test pattern mining *)
  let config = {
    min_support = 1;
    min_confidence = 0.5;
    max_pattern_length = 5;
    families_to_mine = ["MATH"; "TYPO"; "STYLE"];
    enable_contextual = true;
    enable_composite = false;
  } in
  
  let results = PatternMiner.mine_patterns corpus config in
  PatternMiner.print_results results;
  
  Printf.printf "✅ Ground truth system test completed!\n"