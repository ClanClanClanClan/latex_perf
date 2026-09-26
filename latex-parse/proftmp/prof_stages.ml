module L = Latex_parse_lib

let t name f =
  let t0 = Unix.gettimeofday () and c0 = Sys.time () in
  let r = f () in
  Printf.printf "%-30s %8.1f ms wall %8.1f ms cpu\n%!" name ((Unix.gettimeofday () -. t0) *. 1000.) ((Sys.time () -. c0) *. 1000.);
  r

let read p =
  let ic = open_in_bin p in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let () =
  let path = Sys.argv.(1) in
  let mode = if Array.length Sys.argv > 2 then Sys.argv.(2) else "cli" in
  let src = read path in
  if mode = "cls" then begin
    let fresh () = Bytes.to_string (Bytes.of_string src) in
    ignore (t "comment_semantics_breaker" (fun () -> L.Validators_common.comment_semantics_breaker (fresh ())));
    ignore (t "defined_verbatim_env_names" (fun () -> L.Validators_common.defined_verbatim_env_names (fresh ())));
    ignore (t "comment_blanking_breakers" (fun () -> L.Validators_common.comment_blanking_breakers [fresh ()]));
    let b = t "blank_line_comments" (fun () -> L.Validators_common.blank_line_comments (fresh ())) in
    ignore (t "classify(blanked)" (fun () -> L.Language_profile.classify_source b));
    ignore (t "classification_view" (fun () -> L.Compile_contract.classification_view ~source:(fresh ()) ()));
    ignore (t "extract_body_verified" (fun () -> L.Compile_evidence.extract_body_verified (fresh ())));
    ignore (t "project_model" (fun () -> L.Project_model.of_root path));
  end
  else if mode = "detectors" then begin
    let fresh () = Bytes.to_string (Bytes.of_string src) in
    ignore (t "vcu_ranges" (fun () -> L.Validators_common.find_verbatim_comment_url_ranges (fresh ())));
    ignore (t "math_ranges" (fun () -> L.Validators_common.find_math_ranges (fresh ())));
    ignore (t "moving_arg_ranges" (fun () -> L.Compile_gate_checks.find_moving_arg_ranges (fresh ())));
    ignore (t "ref_alias_macros" (fun () -> L.Compile_gate_checks.find_ref_alias_macros (fresh ())));
    ignore (t "double_script" (fun () -> L.Compile_gate_checks.double_script_fatal (fresh ())));
    ignore (t "no_documentclass" (fun () -> L.Compile_gate_checks.no_documentclass_fatal (fresh ())));
    ignore (t "usepackage_after_begin" (fun () -> L.Compile_gate_checks.usepackage_after_begin_fatal (fresh ())));
    ignore (t "dup_begin_document" (fun () -> L.Compile_gate_checks.duplicate_begin_document_fatal (fresh ())));
    ignore (t "verb_broken_eol" (fun () -> L.Compile_gate_checks.verb_broken_eol_fatal (fresh ())));
    ignore (t "thmtools" (fun () -> L.Compile_gate_checks.thmtools_counter_collision_fatal (fresh ())));
    ignore (t "tabu" (fun () -> L.Compile_gate_checks.tabu_textmode_fatal (fresh ())));
    ignore (t "unbalanced_open_brace" (fun () -> L.Compile_gate_checks.unbalanced_open_brace (fresh ())));
    ignore (t "structural_fatal_reasons" (fun () -> L.Compile_gate_checks.structural_fatal_reasons (fresh ())))
  end
  else begin
    let _ = t "classify_source(banner)" (fun () -> L.Language_profile.classify_source src) in
    let base_dir = Filename.dirname path in
    let _ =
      t "file_analyzer" (fun () ->
          L.File_context.set_file_context
            (L.File_analyzer.analyze_files ~base_dir ~tex_path:path ~source:src ()))
    in
    let _ = t "tokenize(cmd_spans)" (fun () -> L.Tokenizer_lite.tokenize src) in
    let _ =
      t "build_profile+log" (fun () ->
          L.Build_profile.load_log (L.Build_profile.create ~tex_path:path ~base_dir))
    in
    let _ =
      t "user_macro_registry" (fun () ->
          L.User_macro_context.set (L.User_macro_registry.create src))
    in
    let proj =
      match t "project_model" (fun () -> L.Project_model.of_root path) with
      | Ok p -> p
      | Error _ -> failwith "proj"
    in
    let _ = t "closure_source" (fun () -> L.Compile_contract.read_closure_source proj ~root_src:src) in
    let _ = t "structural_fatal_reasons" (fun () -> L.Compile_gate_checks.structural_fatal_reasons src) in
    let _ = t "thmtools(root)" (fun () -> L.Compile_gate_checks.thmtools_counter_collision_fatal src) in
    let _ = t "tabu(root)" (fun () -> L.Compile_gate_checks.tabu_textmode_fatal src) in
    let _nodes, pe = t "parse_located" (fun () -> L.Parser_l2.parse_located src) in
    let pe = t "exonerate" (fun () -> L.Validators.exonerate_benign_end_in_group ~source:src pe) in
    let _ = t "run_compile_blocking" (fun () -> L.Validators.run_compile_blocking ~parse_errors:pe src) in
    let profile = L.Build_profile.create ~tex_path:path ~base_dir in
    let _ =
      t "check_ready_to_compile(all)" (fun () ->
          L.Compile_contract.check_ready_to_compile ~fast:true ~source:src proj profile)
    in
    let _ =
      t "classification_view+classify" (fun () ->
          L.Language_profile.classify_source (L.Compile_contract.classification_view ~source:src ()))
    in
    let closure = L.Compile_contract.read_closure_source proj ~root_src:src in
    let p, pf, order =
      t "CE.extract_of_project" (fun () ->
          L.Compile_evidence.extract_of_project ~breaker_probe:closure ~source:src proj)
    in
    let _ = t "CE.report" (fun () -> L.Compile_evidence.report p pf order) in
    ()
  end
