(** Measure L2 parser success rate on golden corpus (spec W43-45). Exit
    criteria: ≥ 90% parse success. *)

let () =
  let dirs =
    [
      "corpora/lint/style";
      "corpora/lint/locale";
      "corpora/lint/phase3";
      "corpora/lint/i18n_qa";
      "corpora/lint/pilot_v1";
      "corpora/lint/l2_approx";
      "corpora/lint/l2_batch3";
      "corpora/lint/l2_batch4";
      "corpora/lint/l3_text_approx";
      "corpora/lint/l5_expl3_tikz";
      "corpora/lint/stragglers2";
      "corpora/perf";
    ]
  in
  let total = ref 0 in
  let success = ref 0 in
  let failures = ref [] in
  (* Find base_dir *)
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [ Filename.concat exe_dir "../.."; "."; Filename.concat exe_dir "../../.." ]
  in
  let base_dir =
    try
      List.find
        (fun d -> Sys.file_exists (Filename.concat d "corpora/perf"))
        candidates
    with Not_found -> "."
  in
  List.iter
    (fun dir ->
      let full_dir = Filename.concat base_dir dir in
      if Sys.file_exists full_dir && Sys.is_directory full_dir then
        let files = Sys.readdir full_dir in
        Array.iter
          (fun f ->
            if Filename.check_suffix f ".tex" then (
              incr total;
              let path = Filename.concat full_dir f in
              let ic = open_in path in
              let n = in_channel_length ic in
              let s = Bytes.create n in
              really_input ic s 0 n;
              close_in ic;
              let content = Bytes.to_string s in
              if Latex_parse_lib.Parser_l2.parse_success content then
                incr success
              else failures := (dir ^ "/" ^ f) :: !failures))
          files)
    dirs;
  let rate =
    if !total > 0 then float_of_int !success /. float_of_int !total *. 100.0
    else 0.0
  in
  Printf.printf "[parser-corpus] %d / %d = %.1f%% parse success\n%!" !success
    !total rate;
  if !failures <> [] then (
    Printf.printf "[parser-corpus] Failures (%d):\n" (List.length !failures);
    List.iter (fun f -> Printf.printf "  %s\n" f) (List.rev !failures));
  if rate < 90.0 then (
    Printf.eprintf "[parser-corpus] FAIL: %.1f%% < 90%% target\n%!" rate;
    exit 1)
  else Printf.printf "[parser-corpus] PASS: %.1f%% >= 90%% target\n%!" rate
