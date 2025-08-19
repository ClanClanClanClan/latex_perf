(* COMPREHENSIVE INTEGRATION TEST FRAMEWORK *)
(* Tests the complete L0->L1->L2->Validation pipeline with unified architecture *)

open Pipeline_core

module IntegrationTestFramework = struct

  (* === TEST CASE DEFINITIONS === *)
  
  type test_category = 
    | Smoke | Performance | Regression | EdgeCase | RealWorld

  type test_case = {
    id: string;
    name: string;
    description: string;
    category: test_category;
    latex_input: string;
    expected_issues: string list; (* Expected rule IDs *)
    performance_target_ms: float;
    memory_target_mb: float;
    should_succeed: bool; (* Should pipeline complete successfully *)
    metadata: (string * string) list;
  }

  type test_execution_result = {
    test_id: string;
    success: bool;
    pipeline_succeeded: bool;
    execution_time_ms: float;
    memory_used_mb: float;
    issues_found: int;
    expected_issues_found: int;
    unexpected_issues: string list;
    missing_issues: string list;
    performance_pass: bool;
    memory_pass: bool;
    error_message: string option;
    stage_breakdown: (string * float) list;
    details: string list;
  }

  type test_suite_result = {
    suite_name: string;
    total_tests: int;
    passed_tests: int;
    failed_tests: int;
    pass_rate: float;
    total_execution_time_ms: float;
    average_test_time_ms: float;
    performance_failures: int;
    memory_failures: int;
    category_breakdown: (test_category * int * int) list; (* category, passed, total *)
    test_results: test_execution_result list;
  }

  (* === MOCK IMPLEMENTATIONS FOR TESTING === *)
  
  (* Mock L0 Lexer that converts strings to unified tokens *)
  module MockL0Lexer : L0_Lexer = struct
    type input = string
    type output = located_token list  
    type error = string
    type options = { track_locations: bool; include_whitespace: bool }
    
    let stage_name = "MockL0Lexer"
    let default_options = { track_locations = true; include_whitespace = false }
    
    let tokenize_string_simple input =
      let tokens = ref [] in
      let pos = ref 0 in
      let line = ref 1 in
      let col = ref 1 in
      
      let add_token token =
        let location = Location.make !pos (!pos + 1) in
        let located_tok = {
          token = token;
          location = location;
          source_line = !line;
          source_column = !col;
        } in
        tokens := located_tok :: !tokens;
        incr pos;
        incr col
      in
      
      let i = ref 0 in
      let len = String.length input in
      
      while !i < len do
        match input.[!i] with
        | '\\' when !i + 1 < len -> (* Macro *)
            let start = !i + 1 in
            let j = ref start in
            while !j < len && 
                  ((input.[!j] >= 'a' && input.[!j] <= 'z') ||
                   (input.[!j] >= 'A' && input.[!j] <= 'Z')) do
              incr j
            done;
            if !j > start then (
              let macro_name = String.sub input start (!j - start) in
              add_token (TMacro macro_name);
              i := !j
            ) else (
              add_token (TChar (Uchar.of_int (Char.code '\\'), Catcode.Escape));
              incr i
            )
        | '{' -> add_token TGroupOpen; incr i
        | '}' -> add_token TGroupClose; incr i  
        | '$' -> add_token TMathShift; incr i
        | '&' -> add_token TAlignTab; incr i
        | '\n' -> add_token TEndLine; incr line; col := 1; incr i
        | ' ' | '\t' -> add_token TSpace; incr i
        | '%' -> (* Comment - skip to end of line *)
            let comment_start = !i in
            while !i < len && input.[!i] <> '\n' do incr i done;
            let comment_text = String.sub input comment_start (!i - comment_start) in
            add_token (TComment comment_text)
        | c ->
            let uchar = Uchar.of_int (Char.code c) in
            let catcode = Catcode.lookup_catcode (Char.code c) in
            add_token (TChar (uchar, catcode));
            incr i
      done;
      
      add_token TEOF;
      List.rev !tokens

    let validate_input input = String.length input >= 0
    let validate_output tokens = List.length tokens > 0
    
    let process options input =
      let start_time = Sys.time () in
      try
        if not (validate_input input) then
          Error "Invalid input string"
        else
          let tokens = tokenize_string_simple input in
          let execution_time = (Sys.time () -. start_time) *. 1000.0 in
          let metrics = {
            stage_name = "MockL0Lexer";
            input_size = String.length input;
            output_size = List.length tokens;
            execution_time_ms = execution_time;
            memory_used_kb = String.length input / 1024;
            errors_encountered = 0;
          } in
          if validate_output tokens then
            Success (tokens, metrics)
          else
            Error "Invalid tokens generated"
      with
      | exn -> Error (Printf.sprintf "Lexing failed: %s" (Printexc.to_string exn))

    let tokenize_string ?(options = default_options) input =
      process options input
  end

  (* Mock L1 Expander (pass-through for now) *)
  module MockL1Expander : L1_Expander = struct
    type input = located_token list
    type output = located_token list
    type error = string
    type options = { max_expansions: int; track_expansions: bool }
    
    type macro_def = {
      name: string;
      params: int; 
      replacement: token list;
      is_builtin: bool;
    }
    
    let stage_name = "MockL1Expander"
    let default_options = { max_expansions = 1000; track_expansions = false }
    
    let validate_input tokens = List.length tokens > 0
    let validate_output tokens = List.length tokens >= 0
    
    let process options tokens =
      let start_time = Sys.time () in
      try
        if not (validate_input tokens) then
          Error "Invalid input tokens"
        else
          (* For now, just pass through - real expansion would happen here *)
          let execution_time = (Sys.time () -. start_time) *. 1000.0 in
          let metrics = {
            stage_name = "MockL1Expander";
            input_size = List.length tokens;
            output_size = List.length tokens;
            execution_time_ms = execution_time;
            memory_used_kb = List.length tokens / 100;
            errors_encountered = 0;
          } in
          Success (tokens, metrics)
      with
      | exn -> Error (Printf.sprintf "Expansion failed: %s" (Printexc.to_string exn))

    let expand_tokens ?(options = default_options) tokens =
      process options tokens
    
    let load_macro_catalog _file = Success []
  end

  (* Mock L2 Parser *)
  module MockL2Parser : L2_Parser = struct
    type inline = 
      | Command of { name: string; args: string list }
      | Text of string
      | MathInline of inline list
      | Group of inline list

    type block = 
      | Section of { level: int; title: inline list; content: block list }
      | Environment of { name: string; body: block list }
      | Paragraph of inline list
      | MathDisplay of inline list

    type document = {
      preamble: block list;
      body: block list;
      metadata: (string * string) list;
    }

    type input = located_token list
    type output = document
    type error = string
    type options = { parse_math: bool; track_structure: bool }
    
    let stage_name = "MockL2Parser"
    let default_options = { parse_math = true; track_structure = true }
    
    let validate_input tokens = List.length tokens > 0
    let validate_output doc = 
      List.length doc.preamble >= 0 && List.length doc.body >= 0
    
    let process options tokens =
      let start_time = Sys.time () in
      try
        if not (validate_input tokens) then
          Error "Invalid input tokens"
        else
          (* Simple mock parsing *)
          let doc = {
            preamble = [];
            body = [Paragraph [Text "Mock parsed content"]];
            metadata = [("tokens", string_of_int (List.length tokens))];
          } in
          let execution_time = (Sys.time () -. start_time) *. 1000.0 in
          let metrics = {
            stage_name = "MockL2Parser";
            input_size = List.length tokens;
            output_size = 1; (* One paragraph *)
            execution_time_ms = execution_time;
            memory_used_kb = List.length tokens / 50;
            errors_encountered = 0;
          } in
          if validate_output doc then
            Success (doc, metrics)
          else
            Error "Invalid document generated"
      with
      | exn -> Error (Printf.sprintf "Parsing failed: %s" (Printexc.to_string exn))

    let parse_tokens ?(options = default_options) tokens =
      process options tokens
  end

  (* === INTEGRATION TEST CASES === *)
  
  let create_test_cases () = [
    {
      id = "smoke_001";
      name = "Basic document smoke test";
      description = "Simple LaTeX document with no issues";
      category = Smoke;
      latex_input = {|
\documentclass{article}
\begin{document}
\section{Test}
This is a test.
\end{document}
|};
      expected_issues = [];
      performance_target_ms = 10.0;
      memory_target_mb = 1.0;
      should_succeed = true;
      metadata = [("complexity", "low")];
    };
    
    {
      id = "deprecated_math_001";
      name = "Deprecated eqnarray detection";
      description = "Document with deprecated eqnarray environment";
      category = Regression;
      latex_input = {|
\documentclass{article}
\usepackage{amsmath}
\begin{document}
\section{Math}
\begin{eqnarray}
x &=& y \\
a &=& b
\end{eqnarray}
\end{document}
|};
      expected_issues = ["MATH-001"];
      performance_target_ms = 15.0;
      memory_target_mb = 1.0;
      should_succeed = true;
      metadata = [("complexity", "medium"); ("rule_type", "math")];
    };
    
    {
      id = "figure_no_caption_001";
      name = "Figure without caption";
      description = "Figure environment missing caption";
      category = Regression;
      latex_input = {|
\documentclass{article}
\usepackage{graphicx}
\begin{document}
\section{Figures}
\begin{figure}[h]
\centering
\includegraphics[width=0.5\textwidth]{test.png}
\end{figure}
\end{document}
|};
      expected_issues = ["FIG-001"];
      performance_target_ms = 15.0;
      memory_target_mb = 1.0;
      should_succeed = true;
      metadata = [("complexity", "medium"); ("rule_type", "structure")];
    };
    
    {
      id = "typography_issues_001";
      name = "Multiple typography issues";
      description = "Document with quotation and spacing issues";
      category = Regression;
      latex_input = {|
\documentclass{article}
\begin{document}
\section{Typography}
This has "bad quotes" and  multiple   spaces.
Also an apostrophe's test.
\end{document}
|};
      expected_issues = ["TYPO-002/003"; "SPACE-001"];
      performance_target_ms = 15.0;
      memory_target_mb = 1.0;
      should_succeed = true;
      metadata = [("complexity", "medium"); ("rule_type", "typography")];
    };
    
    {
      id = "package_conflict_001"; 
      name = "Package conflicts";
      description = "Document with conflicting packages";
      category = Regression;
      latex_input = {|
\documentclass{article}
\usepackage{natbib}
\usepackage{biblatex}
\begin{document}
\section{Test}
Test content.
\end{document}
|};
      expected_issues = ["PKG-001"];
      performance_target_ms = 15.0;
      memory_target_mb = 1.0;
      should_succeed = true;
      metadata = [("complexity", "low"); ("rule_type", "packages")];
    };
    
    {
      id = "environment_nesting_001";
      name = "Environment nesting issues";
      description = "Document with nested environment problems";
      category = EdgeCase;
      latex_input = {|
\documentclass{article}
\begin{document}
\begin{itemize}
\item First item
\begin{enumerate}
\item Nested item
\end{itemize}
\item This should fail
\end{enumerate}
\end{document}
|};
      expected_issues = ["NEST-001/002/003"];
      performance_target_ms = 20.0;
      memory_target_mb = 1.5;
      should_succeed = true;
      metadata = [("complexity", "high"); ("rule_type", "structure")];
    };
    
    {
      id = "performance_large_001";
      name = "Large document performance test";
      description = "Test performance on larger document";
      category = Performance;
      latex_input = String.concat "" [
        "\\documentclass{article}\n";
        "\\usepackage{amsmath}\n"; 
        "\\begin{document}\n";
        String.concat "" (List.init 50 (fun i -> 
          Printf.sprintf "\\section{Section %d}\nThis is content for section %d with ``proper quotes''.\n\n" i i));
        "\\end{document}\n";
      ];
      expected_issues = [];
      performance_target_ms = 50.0;
      memory_target_mb = 5.0;
      should_succeed = true;
      metadata = [("complexity", "high"); ("document_size", "large")];
    };
    
    {
      id = "real_world_001";
      name = "Real academic paper simulation";
      description = "Simulated academic paper with various elements";
      category = RealWorld;
      latex_input = {|
\documentclass[11pt]{article}
\usepackage{amsmath,amssymb,graphicx,cite}
\title{Test Paper}
\author{Author Name}
\begin{document}
\maketitle

\section{Introduction}
This paper discusses ``important topics'' in research.

\section{Methods}
\begin{equation}
E = mc^2 \label{eq:energy}
\end{equation}

As shown in Equation~\ref{eq:energy}, energy is conserved.

\begin{figure}[h]
\centering
\includegraphics[width=0.8\textwidth]{results.png}
\caption{Experimental results showing clear trends.}
\label{fig:results}
\end{figure}

\section{Conclusion}
The results in Figure~\ref{fig:results} demonstrate our hypothesis.

\end{document}
|};
      expected_issues = [];
      performance_target_ms = 30.0;
      memory_target_mb = 2.0;
      should_succeed = true;
      metadata = [("complexity", "realistic"); ("document_type", "academic")];
    };
  ]

  (* === PIPELINE INTEGRATION EXECUTION === *)
  
  let run_pipeline_on_test test_case =
    let start_time = Sys.time () in
    let stage_times = ref [] in
    
    let record_stage stage_name stage_start =
      let elapsed = (Sys.time () -. stage_start) *. 1000.0 in
      stage_times := (stage_name, elapsed) :: !stage_times;
      elapsed
    in
    
    try
      (* Stage 1: L0 Lexing *)
      let l0_start = Sys.time () in
      let l0_result = MockL0Lexer.tokenize_string test_case.latex_input in
      let l0_time = record_stage "L0_Lexing" l0_start in
      
      match l0_result with
      | Error err -> 
          Error (Printf.sprintf "L0 failed: %s" err, Some l0_time)
      | Success (l0_tokens, l0_metrics) ->
          
          (* Stage 2: L1 Expansion *)
          let l1_start = Sys.time () in
          let l1_result = MockL1Expander.expand_tokens l0_tokens in
          let l1_time = record_stage "L1_Expansion" l1_start in
          
          match l1_result with
          | Error err ->
              Error (Printf.sprintf "L1 failed: %s" err, Some l1_time)
          | Success (l1_tokens, l1_metrics) ->
              
              (* Stage 3: L2 Parsing *)
              let l2_start = Sys.time () in
              let l2_result = MockL2Parser.parse_tokens l1_tokens in
              let l2_time = record_stage "L2_Parsing" l2_start in
              
              match l2_result with
              | Error err ->
                  Error (Printf.sprintf "L2 failed: %s" err, Some l2_time)
              | Success (l2_document, l2_metrics) ->
                  
                  (* Stage 4: Validation *)
                  let validation_start = Sys.time () in
                  let module ValidationSystem = Validation_system_unified.UnifiedValidationSystem in
                  let validation_result = ValidationSystem.run_validation l1_tokens in
                  let validation_time = record_stage "Validation" validation_start in
                  
                  match validation_result with
                  | Error err ->
                      Error (Printf.sprintf "Validation failed: %s" err, Some validation_time)
                  | Success (issues, metrics, stage_metrics) ->
                      let total_time = (Sys.time () -. start_time) *. 1000.0 in
                      Ok {
                        test_input = test_case.latex_input;
                        l0_tokens = l0_tokens;
                        l1_tokens = l1_tokens; 
                        l2_document = l2_document;
                        validation_issues = issues;
                        validation_metrics = metrics;
                        total_time_ms = total_time;
                        stage_times = List.rev !stage_times;
                      }
                      
    with
    | exn -> Error (Printf.sprintf "Pipeline exception: %s" (Printexc.to_string exn), None)

  (* Execute a single test case *)
  let execute_test test_case =
    Printf.printf "\n🧪 Executing test: %s\n" test_case.name;
    Printf.printf "   Description: %s\n" test_case.description;
    
    let start_memory = Gc.allocated_bytes () in
    let pipeline_result = run_pipeline_on_test test_case in
    let end_memory = Gc.allocated_bytes () in
    let memory_used_mb = (end_memory -. start_memory) /. (1024.0 *. 1024.0) in
    
    match pipeline_result with
    | Error (error_msg, stage_time_opt) ->
        Printf.printf "   ❌ Pipeline Error: %s\n" error_msg;
        {
          test_id = test_case.id;
          success = false;
          pipeline_succeeded = false;
          execution_time_ms = (match stage_time_opt with Some t -> t | None -> 0.0);
          memory_used_mb = memory_used_mb;
          issues_found = 0;
          expected_issues_found = 0;
          unexpected_issues = [];
          missing_issues = test_case.expected_issues;
          performance_pass = false;
          memory_pass = memory_used_mb <= test_case.memory_target_mb;
          error_message = Some error_msg;
          stage_breakdown = [];
          details = ["Pipeline failed with error: " ^ error_msg];
        }
    
    | Ok pipeline_result ->
        let issues_found = List.length pipeline_result.validation_issues in
        let found_rule_ids = List.map (fun issue -> 
          issue.Validation_system_unified.UnifiedValidationSystem.rule_id
        ) pipeline_result.validation_issues in
        
        (* Check which expected issues were found *)
        let expected_found = List.filter (fun expected ->
          List.exists (fun found -> String.equal found expected) found_rule_ids
        ) test_case.expected_issues in
        
        let missing_issues = List.filter (fun expected ->
          not (List.exists (fun found -> String.equal found expected) found_rule_ids)
        ) test_case.expected_issues in
        
        let unexpected_issues = List.filter (fun found ->
          not (List.exists (fun expected -> String.equal found expected) test_case.expected_issues)
        ) found_rule_ids in
        
        let performance_pass = pipeline_result.total_time_ms <= test_case.performance_target_ms in
        let memory_pass = memory_used_mb <= test_case.memory_target_mb in
        let issues_match = List.length missing_issues = 0 && List.length unexpected_issues = 0 in
        let success = performance_pass && memory_pass && issues_match && test_case.should_succeed in
        
        let details = [
          Printf.sprintf "Total pipeline time: %.3f ms (target: %.1f ms)" 
            pipeline_result.total_time_ms test_case.performance_target_ms;
          Printf.sprintf "Memory used: %.2f MB (target: %.1f MB)"
            memory_used_mb test_case.memory_target_mb;
          Printf.sprintf "Issues found: %d (expected: %d)" 
            issues_found (List.length test_case.expected_issues);
          Printf.sprintf "Expected issues found: %s" 
            (String.concat ", " expected_found);
          if List.length missing_issues > 0 then
            Printf.sprintf "Missing issues: %s" (String.concat ", " missing_issues)
          else "";
          if List.length unexpected_issues > 0 then
            Printf.sprintf "Unexpected issues: %s" (String.concat ", " unexpected_issues)  
          else "";
          Printf.sprintf "Stage breakdown: %s"
            (String.concat ", " (List.map (fun (stage, time) -> 
              Printf.sprintf "%s: %.2fms" stage time) pipeline_result.stage_times));
        ] |> List.filter (fun s -> String.length s > 0) in
        
        Printf.printf "   %s %s\n" 
          (if success then "✅" else "❌")
          (if success then "PASS" else "FAIL");
        
        List.iter (fun detail -> Printf.printf "   - %s\n" detail) details;
        
        {
          test_id = test_case.id;
          success = success;
          pipeline_succeeded = true;
          execution_time_ms = pipeline_result.total_time_ms;
          memory_used_mb = memory_used_mb;
          issues_found = issues_found;
          expected_issues_found = List.length expected_found;
          unexpected_issues = unexpected_issues;
          missing_issues = missing_issues;
          performance_pass = performance_pass;
          memory_pass = memory_pass;
          error_message = None;
          stage_breakdown = pipeline_result.stage_times;
          details = details;
        }

  (* Run complete integration test suite *)
  let run_integration_test_suite () =
    Printf.printf "\n🔗 COMPREHENSIVE INTEGRATION TEST SUITE\n";
    Printf.printf "========================================\n";
    Printf.printf "Testing complete L0->L1->L2->Validation pipeline\n\n";
    
    let test_cases = create_test_cases () in
    let start_time = Sys.time () in
    let results = List.map execute_test test_cases in
    let total_time = (Sys.time () -. start_time) *. 1000.0 in
    
    let total_tests = List.length results in
    let passed_tests = List.length (List.filter (fun r -> r.success) results) in
    let failed_tests = total_tests - passed_tests in
    let performance_failures = List.length (List.filter (fun r -> not r.performance_pass) results) in
    let memory_failures = List.length (List.filter (fun r -> not r.memory_pass) results) in
    let avg_time = total_time /. float total_tests in
    
    (* Category breakdown *)
    let categories = [Smoke; Performance; Regression; EdgeCase; RealWorld] in
    let category_breakdown = List.map (fun cat ->
      let cat_tests = List.filter (fun tc -> 
        match List.find (fun r -> String.equal r.test_id tc.id) results with
        | r -> (List.find (fun tc2 -> String.equal tc2.id tc.id) test_cases).category = cat
        | exception Not_found -> false
      ) test_cases in
      let cat_results = List.filter (fun r ->
        List.exists (fun tc -> String.equal tc.id r.test_id && tc.category = cat) test_cases
      ) results in
      let passed = List.length (List.filter (fun r -> r.success) cat_results) in
      (cat, passed, List.length cat_tests)
    ) categories in
    
    Printf.printf "\n📊 INTEGRATION TEST SUMMARY\n";
    Printf.printf "============================\n";
    Printf.printf "Total tests: %d\n" total_tests;
    Printf.printf "Passed: %d (%.1f%%)\n" passed_tests (100.0 *. float passed_tests /. float total_tests);
    Printf.printf "Failed: %d\n" failed_tests;
    Printf.printf "Performance failures: %d\n" performance_failures;
    Printf.printf "Memory failures: %d\n" memory_failures;
    Printf.printf "Total execution time: %.3f ms\n" total_time;
    Printf.printf "Average test time: %.3f ms\n" avg_time;
    
    Printf.printf "\n📋 CATEGORY BREAKDOWN\n";
    Printf.printf "=====================\n";
    List.iter (fun (cat, passed, total) ->
      let cat_name = match cat with
        | Smoke -> "Smoke" | Performance -> "Performance" | Regression -> "Regression"
        | EdgeCase -> "EdgeCase" | RealWorld -> "RealWorld" in
      Printf.printf "%s: %d/%d (%.1f%%)\n" cat_name passed total 
        (if total > 0 then 100.0 *. float passed /. float total else 0.0)
    ) category_breakdown;
    
    if failed_tests > 0 then begin
      Printf.printf "\n❌ FAILED TESTS\n";
      Printf.printf "================\n";
      List.iter (fun result ->
        if not result.success then
          Printf.printf "- %s: %s\n" result.test_id 
            (match result.error_message with Some msg -> msg | None -> "Assertion failed")
      ) results
    end;
    
    Printf.printf "\n🎯 INTEGRATION STATUS: %s\n" 
      (if passed_tests = total_tests then "✅ ALL TESTS PASSED" else "❌ SOME TESTS FAILED");
    
    {
      suite_name = "Comprehensive Integration Tests";
      total_tests = total_tests;
      passed_tests = passed_tests;
      failed_tests = failed_tests;
      pass_rate = 100.0 *. float passed_tests /. float total_tests;
      total_execution_time_ms = total_time;
      average_test_time_ms = avg_time;
      performance_failures = performance_failures;
      memory_failures = memory_failures;
      category_breakdown = category_breakdown;
      test_results = results;
    }

end

(* Run the integration test suite *)
let () = 
  let _result = IntegrationTestFramework.run_integration_test_suite () in
  ()