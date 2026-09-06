(** Rule-id TEST-MENTION coverage. NOT mutation testing, and not assertion
    coverage.

    OPEN-060. This file's name and its former docstring both overstated what it
    measures. It claimed to check "whether at least one test file contains a
    [fires \"RULE-ID\"] assertion" and to report a "mutation score". Neither is
    true:

    - Nothing is mutated. There is no fault injection anywhere in this file.
    - The search is [Str.regexp_string "\"RULE-ID\""] — the bare QUOTED ID,
      anywhere in any [test_*.ml]. It does not require [fires], does not require
      an assertion, and does not require executable code at all. A rule id
      sitting in an OCaml COMMENT counts as covered; that was reproduced in a
      scratch tree whose only "test" file was a comment listing rule ids, which
      scored 100.0% and PASSed.

    So the number is a floor on "somebody typed this id in a test file", which
    is a weak but non-zero signal: a rule whose id appears NOWHERE is certainly
    untested. Read it that way and it is useful. Read it as a mutation score and
    it is fiction.

    The filename is deliberately NOT changed: [check_memo_files.py] (in the
    required [spec-drift] gate) maps the memo path "testing/mutation/" to this
    exact path, and [check_regression_gates.py] execs it by name. The threshold
    stays 0.30. *)

let () =
  (* Get all rule IDs via run_all_with_timings *)
  let _, _, timings =
    Latex_parse_lib.Validators.run_all_with_timings
      "\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}"
  in
  let all_ids = List.map fst timings in
  let total = List.length all_ids in
  Printf.printf
    "[rule-id-mentions] NOTE: this is a name-presence scan, not mutation \
     testing (OPEN-060)\n\
     %!";
  Printf.printf "[rule-id-mentions] rules registered: %d\n%!" total;
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
  Printf.printf
    "[rule-id-mentions] id appears in some test file: %d/%d (%.1f%%)\n%!"
    covered total
    (100.0 *. float covered /. float total);
  (* List uncovered rules *)
  let uncovered =
    List.filter (fun id -> not (Hashtbl.mem mentioned_ids id)) all_ids
  in
  if uncovered <> [] then (
    Printf.printf "[rule-id-mentions] id appears nowhere (%d):\n%!"
      (List.length uncovered);
    List.iter
      (fun id -> Printf.printf "  %s\n" id)
      (List.sort compare uncovered));
  (* Threshold check *)
  let threshold = 0.30 in
  if total > 0 && float covered /. float total < threshold then (
    Printf.eprintf
      "[rule-id-mentions] FAIL: %.1f%% of ids are mentioned, below the %.0f%% \
       floor\n\
       %!"
      (100.0 *. float covered /. float total)
      (threshold *. 100.0);
    exit 1)
  else Printf.printf "[rule-id-mentions] PASS\n%!"
