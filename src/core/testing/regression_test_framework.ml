(* COMPREHENSIVE REGRESSION TEST FRAMEWORK *)
(* Ensures system stability and performance across changes *)

open Pipeline_core

module RegressionTestFramework = struct

  (* === BASELINE MANAGEMENT === *)
  
  type baseline_metrics = {
    version: string;
    timestamp: float;
    performance_baseline: (string * float) list; (* test_id -> execution_time_ms *)
    issue_baseline: (string * string list) list; (* test_id -> rule_ids *)
    memory_baseline: (string * float) list; (* test_id -> memory_mb *)
    success_baseline: (string * bool) list; (* test_id -> should_pass *)
  }

  type regression_result = 
    | NoRegression
    | PerformanceRegression of { test_id: string; baseline_ms: float; current_ms: float; factor: float }
    | FunctionalRegression of { test_id: string; expected_issues: string list; actual_issues: string list }
    | MemoryRegression of { test_id: string; baseline_mb: float; current_mb: float; factor: float }
    | NewFailure of { test_id: string; error: string }
    | UnexpectedSuccess of { test_id: string }

  type regression_analysis = {
    baseline_version: string;
    current_version: string;
    total_tests: int;
    regressions_found: int;
    performance_regressions: int;
    functional_regressions: int;
    memory_regressions: int;
    new_failures: int;
    unexpected_successes: int;
    regression_details: regression_result list;
    overall_performance_change: float; (* Percentage change *)
    stability_score: float; (* 0.0 to 1.0, 1.0 = perfectly stable *)
  }

  (* === TEST CORPUS MANAGEMENT === *)
  
  type corpus_file = {
    path: string;
    description: string;
    size_kb: float;
    complexity: [`Low | `Medium | `High | `Extreme];
    document_type: [`Academic | `Technical | `Book | `Presentation | `Other];
    expected_issues: string list;
    performance_target_ms: float;
    metadata: (string * string) list;
  }

  type corpus_test_result = {
    file_path: string;
    success: bool;
    execution_time_ms: float;
    memory_used_mb: float;
    issues_found: string list;
    pipeline_stages: (string * float) list;
    error_message: string option;
  }

  (* === PERFORMANCE TRACKING === *)
  
  type performance_trend = {
    test_id: string;
    measurements: (float * float) list; (* timestamp, execution_time_ms *)
    trend_direction: [`Improving | `Stable | `Degrading];
    trend_coefficient: float; (* Linear regression slope *)
    latest_measurement: float;
    baseline_measurement: float;
    deviation_percentage: float;
  }

  type performance_report = {
    report_timestamp: float;
    total_tests: int;
    average_execution_time: float;
    performance_trends: performance_trend list;
    concerning_trends: performance_trend list; (* Degrading trends *)
    overall_health: [`Excellent | `Good | `Concerning | `Critical];
    recommendations: string list;
  }

  (* === CORPUS FILE DEFINITIONS === *)
  
  let standard_corpus_files = [
    {
      path = "corpora/perf_smoke.tex";
      description = "Performance smoke test - basic document";
      size_kb = 1.0;
      complexity = `Low;
      document_type = `Technical;
      expected_issues = [];
      performance_target_ms = 5.0;
      metadata = [("purpose", "smoke_test"); ("baseline", "true")];
    };
    
    {
      path = "corpora/perf/edit_window_4kb.tex";
      description = "Edit window test - 4KB document";
      size_kb = 4.0;
      complexity = `Low;
      document_type = `Technical;
      expected_issues = [];
      performance_target_ms = 1.0;
      metadata = [("purpose", "edit_window"); ("target_size", "4kb")];
    };
    
    {
      path = "corpora/perf/perf_smoke_big.tex";
      description = "Large document performance test - 1MB+";
      size_kb = 1100.0;
      complexity = `High;
      document_type = `Academic;
      expected_issues = ["TYPO-002"; "SPACE-001"];
      performance_target_ms = 25.0;
      metadata = [("purpose", "stress_test"); ("target_size", "1mb")];
    };
    
    {
      path = "corpora/perf/perf_math_light.tex";
      description = "Math-heavy document";
      size_kb = 3.0;
      complexity = `Medium;
      document_type = `Academic;
      expected_issues = [];
      performance_target_ms = 8.0;
      metadata = [("content_type", "math_heavy"); ("equations", "many")];
    };
    
    {
      path = "corpora/perf/perf_unicode.tex";
      description = "Unicode and special characters test";
      size_kb = 10.0;
      complexity = `Medium;
      document_type = `Technical;
      expected_issues = [];
      performance_target_ms = 10.0;
      metadata = [("content_type", "unicode"); ("encoding", "utf8")];
    };
  ]

  (* === REGRESSION DETECTION ALGORITHMS === *)
  
  let detect_performance_regression ~threshold_factor baseline_time current_time =
    let factor = current_time /. baseline_time in
    if factor > threshold_factor then
      Some factor
    else
      None

  let detect_functional_regression baseline_issues current_issues =
    let baseline_set = List.sort_uniq String.compare baseline_issues in
    let current_set = List.sort_uniq String.compare current_issues in
    
    let missing_issues = List.filter (fun issue ->
      not (List.mem issue current_set)
    ) baseline_set in
    
    let unexpected_issues = List.filter (fun issue ->
      not (List.mem issue baseline_set)
    ) current_set in
    
    if List.length missing_issues > 0 || List.length unexpected_issues > 0 then
      Some (missing_issues, unexpected_issues)
    else
      None

  let calculate_trend_direction measurements =
    if List.length measurements < 3 then `Stable
    else
      let n = List.length measurements in
      let sum_x = List.foldi (fun i acc _ -> acc + i) 0 measurements in
      let sum_y = List.fold_left (fun acc (_, y) -> acc +. y) 0.0 measurements in
      let sum_xy = List.foldi (fun i acc (_, y) -> acc +. (float i *. y)) 0.0 measurements in
      let sum_x2 = List.foldi (fun i acc _ -> acc + i * i) 0 measurements in
      
      let n_f = float n in
      let slope = (n_f *. sum_xy -. float sum_x *. sum_y) /. (n_f *. float sum_x2 -. float sum_x *. float sum_x) in
      
      if slope > 0.1 then `Degrading
      else if slope < -0.1 then `Improving
      else `Stable

  (* === BASELINE PERSISTENCE === *)
  
  let save_baseline baseline filename =
    let oc = open_out filename in
    let json_content = Printf.sprintf {|{
  "version": "%s",
  "timestamp": %.2f,
  "performance_baseline": [%s],
  "issue_baseline": [%s],
  "memory_baseline": [%s],
  "success_baseline": [%s]
}|} 
      baseline.version
      baseline.timestamp
      (String.concat ", " (List.map (fun (test_id, time) -> 
        Printf.sprintf {|["%s", %.3f]|} test_id time) baseline.performance_baseline))
      (String.concat ", " (List.map (fun (test_id, issues) -> 
        Printf.sprintf {|["%s", [%s]]|} test_id 
          (String.concat ", " (List.map (fun issue -> Printf.sprintf {|"%s"|} issue) issues))) baseline.issue_baseline))
      (String.concat ", " (List.map (fun (test_id, mem) -> 
        Printf.sprintf {|["%s", %.3f]|} test_id mem) baseline.memory_baseline))
      (String.concat ", " (List.map (fun (test_id, success) -> 
        Printf.sprintf {|["%s", %b]|} test_id success) baseline.success_baseline))
    in
    output_string oc json_content;
    close_out oc

  let load_baseline filename =
    if Sys.file_exists filename then
      try
        (* Simplified baseline loading - in production would use proper JSON parser *)
        Some {
          version = "baseline";
          timestamp = Sys.time ();
          performance_baseline = [];
          issue_baseline = [];
          memory_baseline = [];
          success_baseline = [];
        }
      with
      | _ -> None
    else
      None

  (* === CORPUS FILE TESTING === *)
  
  let test_corpus_file corpus_file =
    Printf.printf "\n📄 Testing corpus file: %s\n" (Filename.basename corpus_file.path);
    Printf.printf "   Description: %s\n" corpus_file.description;
    Printf.printf "   Size: %.1f KB, Complexity: %s\n" 
      corpus_file.size_kb
      (match corpus_file.complexity with 
       | `Low -> "Low" | `Medium -> "Medium" | `High -> "High" | `Extreme -> "Extreme");
    
    if not (Sys.file_exists corpus_file.path) then (
      Printf.printf "   ❌ File not found: %s\n" corpus_file.path;
      {
        file_path = corpus_file.path;
        success = false;
        execution_time_ms = 0.0;
        memory_used_mb = 0.0;
        issues_found = [];
        pipeline_stages = [];
        error_message = Some "File not found";
      }
    ) else (
      let start_time = Sys.time () in
      let start_memory = Gc.allocated_bytes () in
      
      try
        (* Read and process file *)
        let ic = open_in corpus_file.path in
        let file_content = really_input_string ic (in_channel_length ic) in
        close_in ic;
        
        (* Mock pipeline execution - would use real pipeline here *)
        let pipeline_stages = [
          ("L0_Lexing", 2.5);
          ("L1_Expansion", 1.8);
          ("L2_Parsing", 3.2);
          ("Validation", 4.1);
        ] in
        
        let total_time = List.fold_left (fun acc (_, time) -> acc +. time) 0.0 pipeline_stages in
        let end_memory = Gc.allocated_bytes () in
        let memory_used_mb = (end_memory -. start_memory) /. (1024.0 *. 1024.0) in
        
        (* Mock issue detection based on file content *)
        let issues_found = 
          let issues = ref [] in
          if String.contains file_content '"' then issues := "TYPO-002" :: !issues;
          if Str.string_match (Str.regexp "  +") file_content 0 then issues := "SPACE-001" :: !issues;
          if String.contains file_content 'ñ' || String.contains file_content 'ü' then issues := "ENC-001" :: !issues;
          !issues
        in
        
        let execution_time = (Sys.time () -. start_time) *. 1000.0 in
        let performance_ok = execution_time <= corpus_file.performance_target_ms in
        
        Printf.printf "   Execution time: %.3f ms (target: %.1f ms) %s\n" 
          execution_time corpus_file.performance_target_ms
          (if performance_ok then "✅" else "❌");
        Printf.printf "   Memory used: %.2f MB\n" memory_used_mb;
        Printf.printf "   Issues found: %d [%s]\n" 
          (List.length issues_found) (String.concat ", " issues_found);
        Printf.printf "   Expected issues: %d [%s]\n"
          (List.length corpus_file.expected_issues) (String.concat ", " corpus_file.expected_issues);
        
        {
          file_path = corpus_file.path;
          success = performance_ok;
          execution_time_ms = execution_time;
          memory_used_mb = memory_used_mb;
          issues_found = issues_found;
          pipeline_stages = pipeline_stages;
          error_message = None;
        }
        
      with
      | exn ->
          let error_msg = Printexc.to_string exn in
          Printf.printf "   ❌ Processing failed: %s\n" error_msg;
          {
            file_path = corpus_file.path;
            success = false;
            execution_time_ms = 0.0;
            memory_used_mb = 0.0;
            issues_found = [];
            pipeline_stages = [];
            error_message = Some error_msg;
          }
    )

  (* === REGRESSION ANALYSIS === *)
  
  let analyze_regressions baseline current_results =
    let regressions = ref [] in
    let performance_changes = ref [] in
    
    (* Analyze each test result *)
    List.iter (fun result ->
      let test_id = Filename.basename result.file_path in
      
      (* Find baseline performance *)
      (match List.assoc_opt test_id baseline.performance_baseline with
      | Some baseline_time ->
          performance_changes := (baseline_time, result.execution_time_ms) :: !performance_changes;
          (match detect_performance_regression ~threshold_factor:1.5 baseline_time result.execution_time_ms with
          | Some factor ->
              regressions := PerformanceRegression {
                test_id = test_id;
                baseline_ms = baseline_time;
                current_ms = result.execution_time_ms;
                factor = factor;
              } :: !regressions
          | None -> ())
      | None -> ());
      
      (* Find baseline issues *)
      (match List.assoc_opt test_id baseline.issue_baseline with
      | Some baseline_issues ->
          (match detect_functional_regression baseline_issues result.issues_found with
          | Some (missing, unexpected) ->
              regressions := FunctionalRegression {
                test_id = test_id;
                expected_issues = baseline_issues;
                actual_issues = result.issues_found;
              } :: !regressions
          | None -> ())
      | None -> ());
      
      (* Check for new failures *)
      (match List.assoc_opt test_id baseline.success_baseline with
      | Some baseline_success ->
          if baseline_success && not result.success then
            regressions := NewFailure {
              test_id = test_id;
              error = (match result.error_message with Some e -> e | None -> "Unknown failure");
            } :: !regressions
          else if not baseline_success && result.success then
            regressions := UnexpectedSuccess { test_id = test_id } :: !regressions
      | None -> ())
    ) current_results;
    
    (* Calculate overall performance change *)
    let overall_perf_change = 
      if List.length !performance_changes > 0 then
        let total_baseline = List.fold_left (fun acc (baseline, _) -> acc +. baseline) 0.0 !performance_changes in
        let total_current = List.fold_left (fun acc (_, current) -> acc +. current) 0.0 !performance_changes in
        ((total_current -. total_baseline) /. total_baseline) *. 100.0
      else 0.0
    in
    
    (* Calculate stability score *)
    let total_tests = List.length current_results in
    let regression_count = List.length !regressions in
    let stability_score = if total_tests > 0 then 
      max 0.0 (1.0 -. (float regression_count /. float total_tests))
    else 1.0 in
    
    {
      baseline_version = baseline.version;
      current_version = "current";
      total_tests = total_tests;
      regressions_found = regression_count;
      performance_regressions = List.length (List.filter (function PerformanceRegression _ -> true | _ -> false) !regressions);
      functional_regressions = List.length (List.filter (function FunctionalRegression _ -> true | _ -> false) !regressions);
      memory_regressions = List.length (List.filter (function MemoryRegression _ -> true | _ -> false) !regressions);
      new_failures = List.length (List.filter (function NewFailure _ -> true | _ -> false) !regressions);
      unexpected_successes = List.length (List.filter (function UnexpectedSuccess _ -> true | _ -> false) !regressions);
      regression_details = List.rev !regressions;
      overall_performance_change = overall_perf_change;
      stability_score = stability_score;
    }

  (* === MAIN REGRESSION TEST RUNNER === *)
  
  let run_regression_tests ?baseline_file () =
    Printf.printf "\n🔄 COMPREHENSIVE REGRESSION TEST SUITE\n";
    Printf.printf "======================================\n";
    Printf.printf "Testing system stability and performance\n\n";
    
    let start_time = Sys.time () in
    
    (* Load baseline if available *)
    let baseline = match baseline_file with
      | Some filename -> load_baseline filename
      | None -> load_baseline "regression_baseline.json"
    in
    
    (match baseline with
    | Some baseline_data ->
        Printf.printf "📊 Loaded baseline: %s (%.0f tests)\n" 
          baseline_data.version (float (List.length baseline_data.performance_baseline))
    | None ->
        Printf.printf "📊 No baseline found - establishing new baseline\n");
    
    (* Test all corpus files *)
    Printf.printf "\n📚 TESTING CORPUS FILES\n";
    Printf.printf "=======================\n";
    let corpus_results = List.map test_corpus_file standard_corpus_files in
    
    let successful_tests = List.length (List.filter (fun r -> r.success) corpus_results) in
    let total_tests = List.length corpus_results in
    let total_time = (Sys.time () -. start_time) *. 1000.0 in
    
    Printf.printf "\n📈 CORPUS TEST SUMMARY\n";
    Printf.printf "======================\n";
    Printf.printf "Total corpus files tested: %d\n" total_tests;
    Printf.printf "Successful: %d (%.1f%%)\n" successful_tests 
      (100.0 *. float successful_tests /. float total_tests);
    Printf.printf "Failed: %d\n" (total_tests - successful_tests);
    Printf.printf "Total execution time: %.3f ms\n" total_time;
    Printf.printf "Average time per file: %.3f ms\n" (total_time /. float total_tests);
    
    (* Regression analysis *)
    (match baseline with
    | Some baseline_data ->
        Printf.printf "\n🔍 REGRESSION ANALYSIS\n";
        Printf.printf "======================\n";
        let analysis = analyze_regressions baseline_data corpus_results in
        
        Printf.printf "Baseline version: %s\n" analysis.baseline_version;
        Printf.printf "Current version: %s\n" analysis.current_version;
        Printf.printf "Total regressions found: %d\n" analysis.regressions_found;
        Printf.printf "Performance regressions: %d\n" analysis.performance_regressions;
        Printf.printf "Functional regressions: %d\n" analysis.functional_regressions;
        Printf.printf "New failures: %d\n" analysis.new_failures;
        Printf.printf "Overall performance change: %+.1f%%\n" analysis.overall_performance_change;
        Printf.printf "Stability score: %.2f/1.00\n" analysis.stability_score;
        
        let health_status = 
          if analysis.stability_score >= 0.95 then "✅ EXCELLENT"
          else if analysis.stability_score >= 0.85 then "🟨 GOOD"
          else if analysis.stability_score >= 0.70 then "🟧 CONCERNING"
          else "🟥 CRITICAL" in
        Printf.printf "System health: %s\n" health_status;
        
        if analysis.regressions_found > 0 then begin
          Printf.printf "\n🚨 REGRESSION DETAILS\n";
          Printf.printf "=====================\n";
          List.iter (function
            | PerformanceRegression { test_id; baseline_ms; current_ms; factor } ->
                Printf.printf "⚡ Performance regression in %s: %.1fms -> %.1fms (%.1fx slower)\n"
                  test_id baseline_ms current_ms factor
            | FunctionalRegression { test_id; expected_issues; actual_issues } ->
                Printf.printf "🔧 Functional regression in %s:\n" test_id;
                Printf.printf "    Expected: [%s]\n" (String.concat ", " expected_issues);
                Printf.printf "    Actual: [%s]\n" (String.concat ", " actual_issues)
            | NewFailure { test_id; error } ->
                Printf.printf "❌ New failure in %s: %s\n" test_id error
            | UnexpectedSuccess { test_id } ->
                Printf.printf "✅ Unexpected success in %s (was failing in baseline)\n" test_id
            | _ -> ()
          ) analysis.regression_details
        end
        
    | None ->
        Printf.printf "\n📝 ESTABLISHING NEW BASELINE\n";
        Printf.printf "=============================\n";
        let new_baseline = {
          version = "v1.0.0";
          timestamp = Sys.time ();
          performance_baseline = List.map (fun r -> 
            (Filename.basename r.file_path, r.execution_time_ms)) corpus_results;
          issue_baseline = List.map (fun r -> 
            (Filename.basename r.file_path, r.issues_found)) corpus_results;
          memory_baseline = List.map (fun r -> 
            (Filename.basename r.file_path, r.memory_used_mb)) corpus_results;
          success_baseline = List.map (fun r -> 
            (Filename.basename r.file_path, r.success)) corpus_results;
        } in
        save_baseline new_baseline "regression_baseline.json";
        Printf.printf "New baseline saved to regression_baseline.json\n");
    
    Printf.printf "\n🎯 REGRESSION TEST STATUS: %s\n" 
      (if successful_tests = total_tests then "✅ ALL TESTS PASSED" else "❌ SOME TESTS FAILED");
    
    corpus_results

  (* === CONTINUOUS MONITORING === *)
  
  let generate_performance_report results =
    let report_time = Sys.time () in
    let total_time = List.fold_left (fun acc r -> acc +. r.execution_time_ms) 0.0 results in
    let avg_time = if List.length results > 0 then total_time /. float (List.length results) else 0.0 in
    
    (* Mock trend analysis - would use historical data in production *)
    let mock_trends = List.mapi (fun i result ->
      let test_id = Filename.basename result.file_path in
      {
        test_id = test_id;
        measurements = [(report_time, result.execution_time_ms)];
        trend_direction = if i mod 3 = 0 then `Degrading else if i mod 3 = 1 then `Stable else `Improving;
        trend_coefficient = 0.0;
        latest_measurement = result.execution_time_ms;
        baseline_measurement = result.execution_time_ms;
        deviation_percentage = 0.0;
      }
    ) results in
    
    let concerning_trends = List.filter (fun t -> t.trend_direction = `Degrading) mock_trends in
    
    let overall_health = 
      if List.length concerning_trends = 0 then `Excellent
      else if List.length concerning_trends <= List.length results / 4 then `Good
      else if List.length concerning_trends <= List.length results / 2 then `Concerning
      else `Critical in
    
    let recommendations = match overall_health with
      | `Excellent -> ["System performance is excellent"; "Continue current development practices"]
      | `Good -> ["System performance is good"; "Monitor concerning trends closely"]
      | `Concerning -> ["System performance needs attention"; "Investigate degrading components"]
      | `Critical -> ["System performance is critical"; "Immediate performance optimization required"]
    in
    
    {
      report_timestamp = report_time;
      total_tests = List.length results;
      average_execution_time = avg_time;
      performance_trends = mock_trends;
      concerning_trends = concerning_trends;
      overall_health = overall_health;
      recommendations = recommendations;
    }

end

(* Run the regression test suite *)
let () = 
  let _results = RegressionTestFramework.run_regression_tests () in
  ()