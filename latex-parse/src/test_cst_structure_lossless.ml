(** Structure-lossless runtime gate (v26.3 §3 item C).

    Beyond v26.2's byte-lossless invariant ([serialize (of_source src) = src]),
    structure-lossless asserts that re-parsing the serialized CST yields the
    same CST tree. This is implied by byte-losslessness when the parser is
    deterministic, but a runtime check makes the property machine-verified
    on a curated subset.

    Curated subset: LP-Core fixtures under 1MB with no unclosed constructs.
    We use [corpora/roundtrip/] (15 synthetic edge cases shipped in v26.2)
    plus the v26.2.1 fix-integration fixtures. *)

let repo_root = Sys.getcwd ()

let candidate_dirs =
  [
    Filename.concat repo_root "corpora/roundtrip";
    Filename.concat repo_root "../../corpora/roundtrip";
    Filename.concat repo_root "../../../corpora/roundtrip";
    Filename.concat repo_root "corpora/fixtures/v26_2_1";
    Filename.concat repo_root "../../corpora/fixtures/v26_2_1";
    Filename.concat repo_root "../../../corpora/fixtures/v26_2_1";
  ]

let resolved_dirs =
  List.filter Sys.file_exists candidate_dirs

let collect_tex (dir : string) : string list =
  if not (Sys.file_exists dir) then []
  else
    Sys.readdir dir |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".tex")
    |> List.map (fun f -> Filename.concat dir f)

let read_all path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(** Drop fixtures that exceed 1 MB or contain unclosed constructs we
    pre-flagged. The roundtrip corpus has explicit "unclosed_*"
    files which v26.2 byte-tests but we exclude here. *)
let in_subset (path : string) : bool =
  let name = Filename.basename path in
  let too_big =
    try (Unix.stat path).Unix.st_size > 1024 * 1024
    with Unix.Unix_error _ -> false
  in
  let has_unclosed_marker =
    let prefixes = [ "unclosed_"; "incomplete_" ] in
    List.exists (fun p -> String.length name >= String.length p
                          && String.sub name 0 (String.length p) = p) prefixes
  in
  not too_big && not has_unclosed_marker

let () =
  let files =
    List.concat_map collect_tex resolved_dirs
    |> List.sort_uniq compare
    |> List.filter in_subset
  in
  if files = [] then begin
    Printf.eprintf
      "[cst-structure-lossless] FATAL: no fixtures found (cwd=%s)\n%!"
      repo_root;
    exit 1
  end;
  let total = List.length files in
  let failures = ref [] in
  List.iter
    (fun path ->
      let src = read_all path in
      let cst1 = Latex_parse_lib.Cst_of_ast.of_source src in
      let serialized = Latex_parse_lib.Cst.serialize cst1 in
      let cst2 = Latex_parse_lib.Cst_of_ast.of_source serialized in
      if not (cst1 = cst2) then failures := path :: !failures)
    files;
  let n_fail = List.length !failures in
  if n_fail = 0 then begin
    Printf.printf
      "[cst-structure-lossless] PASS: %d / %d fixtures parse-serialize-parse \
       identical\n"
      total total;
    exit 0
  end
  else begin
    Printf.eprintf
      "[cst-structure-lossless] FAIL: %d / %d fixtures diverged\n"
      n_fail total;
    List.iter
      (fun p -> Printf.eprintf "  diverged: %s\n" p)
      (List.rev !failures);
    exit 1
  end
