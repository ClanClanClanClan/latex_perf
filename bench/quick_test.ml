(* Quick performance test *)

let test_file = "corpora/perf/perf_smoke_big.tex"

let time_lexer name f input =
  let start = Unix.gettimeofday () in
  let tokens = f input in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  Printf.printf "%s: %.2f ms (%d tokens)\n" name elapsed (List.length tokens);
  tokens

let load_file filename =
  try
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    Some content
  with _ -> None

let () =
  match load_file test_file with
  | None -> Printf.printf "Cannot load %s\n" test_file
  | Some input ->
    Printf.printf "Testing with %d bytes\n" (String.length input);
    
    (* Warmup *)
    ignore (Core.Lexer_optimized_v25.tokenize_to_list input);
    
    (* Test *)
    let t1 = time_lexer "Lexer_optimized_v25 baseline" Core.Lexer_optimized_v25.tokenize_to_list input in
    let t2 = time_lexer "L0_lexer_track_a_simple" Core.L0_lexer_track_a_simple.tokenize input in
    
    if List.length t1 <> List.length t2 then
      Printf.printf "ERROR: Token count mismatch!\n"