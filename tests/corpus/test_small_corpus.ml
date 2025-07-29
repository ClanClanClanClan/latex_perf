(* Test corpus runner on a small subset *)

#use "real_corpus_runner.ml";;

(* Override to test on just first 10 files *)
let run_small_test corpus_path =
  Printf.printf "🧪 SMALL CORPUS TEST (First 10 files)\n";
  Printf.printf "=====================================\n\n";
  
  let stats = create_stats () in
  
  (* Find tex files *)
  let tex_files = find_tex_files corpus_path in
  let test_files = 
    match tex_files with
    | [] -> []
    | files -> 
        let sorted = List.sort String.compare files in
        let rec take n = function
          | [] -> []
          | _ when n <= 0 -> []
          | h::t -> h :: take (n-1) t
        in
        take 10 sorted
  in
  
  Printf.printf "Testing on %d files:\n" (List.length test_files);
  List.iter (fun f -> Printf.printf "  - %s\n" f) test_files;
  Printf.printf "\n";
  
  (* Process files *)
  List.iter (fun file ->
    Printf.printf "Processing: %s\n" (Filename.basename file);
    process_file stats file
  ) test_files;
  
  Printf.printf "\n📊 Results:\n";
  Printf.printf "Files: %d\n" stats.files_processed;
  Printf.printf "Issues: %d\n" stats.total_issues;
  Printf.printf "Errors: %d\n" stats.errors;
  Printf.printf "Time: %.3fs\n" stats.processing_time

let () = run_small_test "corpus"