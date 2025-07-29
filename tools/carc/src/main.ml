(* CARC Main Module - CLI Entry Point *)
(* Certified Automatic Rule Classifier *)

open Ast
open Parser  
open Classify

let print_usage () =
  Printf.printf "CARC - Certified Automatic Rule Classifier\n";
  Printf.printf "Usage: carc [OPTIONS] <rules_file>\n";
  Printf.printf "\n";
  Printf.printf "Options:\n";
  Printf.printf "  --output-json <file>    Output JSON classification manifest\n";
  Printf.printf "  --stats                 Print classification statistics\n";
  Printf.printf "  --verbose               Verbose output\n";
  Printf.printf "  --confidence-threshold <float>  Minimum confidence threshold (default: 0.6)\n";
  Printf.printf "  --help                  Show this help\n";
  Printf.printf "\n";
  Printf.printf "Example:\n";
  Printf.printf "  carc rules/rules_unified.yaml --output-json rules_manifest.json --stats\n"

let output_json_manifest classifications filename =
  let json_output = Buffer.create 1024 in
  Buffer.add_string json_output "{\n";
  Buffer.add_string json_output "  \"carc_version\": \"1.0\",\n";
  Buffer.add_string json_output "  \"timestamp\": \"";
  Buffer.add_string json_output (string_of_float (Sys.time ()));
  Buffer.add_string json_output "\",\n";
  Buffer.add_string json_output "  \"total_rules\": ";
  Buffer.add_string json_output (string_of_int (List.length classifications));
  Buffer.add_string json_output ",\n";
  Buffer.add_string json_output "  \"classifications\": [\n";
  
  let rec output_classifications = function
    | [] -> ()
    | [c] -> 
        Buffer.add_string json_output "    {\n";
        Buffer.add_string json_output ("      \"rule_id\": \"" ^ c.rule_id ^ "\",\n");
        Buffer.add_string json_output ("      \"classification\": \"" ^ 
          (match c.classification with REG -> "REG" | VPL -> "VPL" | CST -> "CST") ^ "\",\n");
        Buffer.add_string json_output ("      \"confidence\": " ^ string_of_float c.confidence ^ ",\n");
        Buffer.add_string json_output ("      \"reasoning\": \"" ^ c.reasoning ^ "\"\n");
        Buffer.add_string json_output "    }\n"
    | c :: rest ->
        Buffer.add_string json_output "    {\n";
        Buffer.add_string json_output ("      \"rule_id\": \"" ^ c.rule_id ^ "\",\n");
        Buffer.add_string json_output ("      \"classification\": \"" ^ 
          (match c.classification with REG -> "REG" | VPL -> "VPL" | CST -> "CST") ^ "\",\n");
        Buffer.add_string json_output ("      \"confidence\": " ^ string_of_float c.confidence ^ ",\n");
        Buffer.add_string json_output ("      \"reasoning\": \"" ^ c.reasoning ^ "\"\n");
        Buffer.add_string json_output "    },\n";
        output_classifications rest
  in
  
  output_classifications classifications;
  Buffer.add_string json_output "  ]\n";
  Buffer.add_string json_output "}\n";
  
  let oc = open_out filename in
  output_string oc (Buffer.contents json_output);
  close_out oc;
  Printf.printf "JSON manifest written to: %s\n" filename

let print_statistics report =
  Printf.printf "\nCARCClassification Statistics:\n";
  Printf.printf "================================\n";
  Printf.printf "Total rules processed: %d\n" report.total_rules;
  Printf.printf "\nClassification breakdown:\n";
  Printf.printf "  REG (Regular):           %d (%.1f%%)\n" 
    report.reg_count 
    (float_of_int report.reg_count *. 100.0 /. float_of_int report.total_rules);
  Printf.printf "  VPL (Visibly Pushdown): %d (%.1f%%)\n"
    report.vpl_count
    (float_of_int report.vpl_count *. 100.0 /. float_of_int report.total_rules);
  Printf.printf "  CST (Context-Sensitive): %d (%.1f%%)\n"
    report.cst_count  
    (float_of_int report.cst_count *. 100.0 /. float_of_int report.total_rules);
  Printf.printf "\nAverage confidence: %.3f\n" report.avg_confidence;
  
  analyze_confidence report.classifications

let parse_args () =
  let rules_file = ref "" in
  let output_json = ref None in
  let show_stats = ref false in
  let verbose = ref false in
  let confidence_threshold = ref 0.6 in
  
  let rec parse_args_rec args =
    match args with
    | [] -> ()
    | "--help" :: _ -> print_usage (); exit 0
    | "--output-json" :: filename :: rest ->
        output_json := Some filename;
        parse_args_rec rest
    | "--stats" :: rest ->
        show_stats := true;
        parse_args_rec rest
    | "--verbose" :: rest ->
        verbose := true;
        parse_args_rec rest
    | "--confidence-threshold" :: threshold :: rest ->
        confidence_threshold := float_of_string threshold;
        parse_args_rec rest
    | filename :: rest ->
        if !rules_file = "" then
          rules_file := filename
        else (
          Printf.eprintf "Error: Multiple input files specified\n";
          exit 1
        );
        parse_args_rec rest
  in
  
  parse_args_rec (List.tl (Array.to_list Sys.argv));
  
  if !rules_file = "" then (
    Printf.eprintf "Error: No input file specified\n";
    print_usage ();
    exit 1
  );
  
  (!rules_file, !output_json, !show_stats, !verbose, !confidence_threshold)

let main () =
  try
    let (rules_file, output_json, show_stats, verbose, confidence_threshold) = parse_args () in
    
    if verbose then
      Printf.printf "CARC v1.0 - Certified Automatic Rule Classifier\n";
      
    if verbose then
      Printf.printf "Loading rules from: %s\n" rules_file;
      
    let rules = parse_rules_file rules_file in
    let validated_rules = validate_rules rules in
    
    if verbose then
      Printf.printf "Classifying %d rules...\n" (List.length validated_rules);
      
    let classifications = classify_rules validated_rules in
    let report = generate_report classifications in
    
    if show_stats then
      print_statistics report;
      
    begin match output_json with
    | Some filename -> output_json_manifest classifications filename
    | None -> 
        Printf.printf "Classification complete. Use --output-json to save manifest.\n"
    end;
    
    if verbose then
      Printf.printf "CARC classification completed successfully.\n"
      
  with
  | Parse_error msg ->
      Printf.eprintf "Parse error: %s\n" msg;
      exit 1
  | Sys_error msg ->
      Printf.eprintf "System error: %s\n" msg;
      exit 1
  | e ->
      Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string e);
      exit 1

let () = main ()