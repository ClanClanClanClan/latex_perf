(** Differential correctness gate (v27.1.59): the FAST compile-readiness kernel
    ([Compile_contract.check_ready_to_compile ~fast:true]) must produce the
    PROVABLY-IDENTICAL verdict to the FULL path ([~fast:false]) on every
    document.

    The fast kernel is only sound as an optimisation if it is verdict-equivalent
    to running ALL ~641 rules and filtering to the 37 compile-blocking ones. This
    test asserts that empirically over every [.tex] under [corpora/]: for each
    file it computes BOTH verdicts and requires

      - the same Ready / NotReady tag, AND
      - for NotReady, the SAME set of reasons (compared as normalised, order-
        independent strings via [reason_to_string]).

    ANY divergence fails the test — a divergence means the fast kernel is NOT a
    faithful optimisation (most likely a missing shared-context setup for some
    compile-blocking rule) and must be fixed, never weakened away.

    The in-process harness deliberately mirrors what the CLI's [run_compile_check]
    does (see validators_cli.ml): it builds the same [Project_model] / profile and
    performs the same [setup_all] side-effects (File_context, command spans,
    Build_profile, User_macro_registry) BEFORE each check, so the fast and full
    paths observe identical ambient state. Both checks run on the in-memory
    [~source] read from disk. *)

open Latex_parse_lib

let fails = ref 0
let compared = ref 0
let divergences = ref []

(* Resolve the repo base_dir the same way test_parser_corpus.ml does. *)
let base_dir =
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [
      Filename.concat exe_dir "../..";
      ".";
      Filename.concat exe_dir "../../..";
      Filename.concat exe_dir "../../../..";
    ]
  in
  try
    List.find
      (fun d -> Sys.file_exists (Filename.concat d "corpora"))
      candidates
  with Not_found -> "."

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* Recursively collect every .tex under [root]. *)
let rec collect_tex root acc =
  if Sys.file_exists root && Sys.is_directory root then
    Array.fold_left
      (fun acc entry ->
        let p = Filename.concat root entry in
        if (try Sys.is_directory p with _ -> false) then collect_tex p acc
        else if Filename.check_suffix p ".tex" then p :: acc
        else acc)
      acc (Sys.readdir root)
  else acc

(* Mirror validators_cli.setup_all's side-effects so fast and full paths see
   identical ambient state. Failures are non-fatal (some fixtures are partial). *)
let setup_ambient ~path ~src =
  (try
     let base = Filename.dirname path in
     let fc =
       File_analyzer.analyze_files ~base_dir:base ~tex_path:path ~source:src ()
     in
     File_context.set_file_context fc
   with _ -> ());
  (try
     let reg = User_macro_registry.create src in
     User_macro_context.set reg
   with _ -> ())

(* Normalise a reason list into a sorted set of strings so ordering never
   causes a spurious divergence. *)
let reasons_key = function
  | Compile_contract.Ready -> (true, [])
  | Compile_contract.NotReady rs ->
      (false, List.sort compare (List.map Compile_contract.reason_to_string rs))

let verdict_to_string = function
  | Compile_contract.Ready -> "READY"
  | Compile_contract.NotReady rs ->
      "NOT-READY[ "
      ^ String.concat " | "
          (List.sort compare (List.map Compile_contract.reason_to_string rs))
      ^ " ]"

let compare_file path =
  match read_file path with
  | exception _ -> () (* unreadable fixture — skip *)
  | src -> (
      match Project_model.of_root path with
      | Error _ -> () (* not a LaTeX root (partial include etc.) — skip *)
      | Ok proj ->
          let profile =
            Build_profile.create ~tex_path:path
              ~base_dir:(Filename.dirname path)
          in
          let aux_path =
            let cand = Filename.remove_extension path ^ ".aux" in
            if Sys.file_exists cand then Some cand else None
          in
          incr compared;
          (* Full path first, then fast, each with the CLI's ambient setup. *)
          setup_ambient ~path ~src;
          let full =
            Compile_contract.check_ready_to_compile ~fast:false ?aux_path
              ~source:src proj profile
          in
          setup_ambient ~path ~src;
          let fast =
            Compile_contract.check_ready_to_compile ~fast:true ?aux_path
              ~source:src proj profile
          in
          if reasons_key fast <> reasons_key full then (
            incr fails;
            let rel =
              let b = base_dir ^ "/" in
              let lb = String.length b in
              if String.length path >= lb && String.sub path 0 lb = b then
                String.sub path lb (String.length path - lb)
              else path
            in
            divergences :=
              Printf.sprintf "%s\n    fast=%s\n    full=%s" rel
                (verdict_to_string fast) (verdict_to_string full)
              :: !divergences))

let () =
  let corpora = Filename.concat base_dir "corpora" in
  let files = List.sort compare (collect_tex corpora []) in
  List.iter compare_file files;
  Printf.printf "[fast-readiness-parity] docs_compared=%d\n%!" !compared;
  if !fails > 0 then (
    Printf.eprintf "[fast-readiness-parity] %d DIVERGENCE(S):\n%!" !fails;
    List.iter (fun d -> Printf.eprintf "  %s\n%!" d) (List.rev !divergences);
    exit 1)
  else
    Printf.printf "[fast-readiness-parity] PASS: fast==full on all %d docs\n%!"
      !compared
