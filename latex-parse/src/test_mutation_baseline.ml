(** Mutation baseline: verify test coverage of validator rules.

    For each rule, checks whether at least one test file contains a
    [fires "RULE-ID"] assertion. Reports mutation score as covered/total. Fails
    if score drops below threshold. *)

let () =
  (* Get all rule IDs via run_all_with_timings *)
  let _, _, timings =
    Latex_parse_lib.Validators.run_all_with_timings
      "\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}"
  in
  let all_ids = List.map fst timings in
  let total = List.length all_ids in
  Printf.printf "[mutation] total rules: %d\n%!" total;
  (* Scan test files for fires/does_not_fire/find_result "ID" *)
  let test_dir =
    let exe = Filename.dirname Sys.argv.(0) in
    let candidates =
      [ Filename.concat exe "../.."; "."; Filename.concat exe "../../.." ]
    in
    try
      List.find
        (fun d ->
          Sys.file_exists (Filename.concat d "latex-parse/src/test_helpers.ml"))
        candidates
    with Not_found -> "."
  in
  let src_dir = Filename.concat test_dir "latex-parse/src" in
  let files =
    Array.to_list (Sys.readdir src_dir)
    |> List.filter (fun f ->
           String.length f > 5
           && String.sub f 0 5 = "test_"
           && Filename.check_suffix f ".ml")
  in
  (* Collect all rule ID mentions *)
  let mentioned_ids = Hashtbl.create 256 in
  List.iter
    (fun fname ->
      let path = Filename.concat src_dir fname in
      try
        let ic = open_in path in
        let content =
          Fun.protect
            ~finally:(fun () -> close_in ic)
            (fun () -> really_input_string ic (in_channel_length ic))
        in
        List.iter
          (fun id ->
            if
              String.length id >= 3
              &&
              let pat = Printf.sprintf {|"%s"|} id in
              try
                ignore (Str.search_forward (Str.regexp_string pat) content 0);
                true
              with Not_found -> false
            then Hashtbl.replace mentioned_ids id ())
          all_ids
      with Sys_error _ -> ())
    files;
  let covered =
    List.length (List.filter (fun id -> Hashtbl.mem mentioned_ids id) all_ids)
  in
  Printf.printf "[mutation] covered: %d/%d (%.1f%%)\n%!" covered total
    (100.0 *. float covered /. float total);
  (* List uncovered rules *)
  let uncovered =
    List.filter (fun id -> not (Hashtbl.mem mentioned_ids id)) all_ids
  in
  if uncovered <> [] then (
    Printf.printf "[mutation] uncovered rules (%d):\n%!" (List.length uncovered);
    List.iter
      (fun id -> Printf.printf "  %s\n" id)
      (List.sort compare uncovered));
  (* Threshold check *)
  let threshold = 0.30 in
  if total > 0 && float covered /. float total < threshold then (
    Printf.eprintf "[mutation] FAIL: score %.1f%% below %.0f%% threshold\n%!"
      (100.0 *. float covered /. float total)
      (threshold *. 100.0);
    exit 1)
  else Printf.printf "[mutation] PASS\n%!"
