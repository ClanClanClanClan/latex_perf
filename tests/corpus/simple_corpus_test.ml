(* Simplified corpus test - create tokens directly *)

#use "extracted_types.ml";;
#use "extracted_validators.ml";;
#use "validator_runner.ml";;

(* Helper functions *)
let s2c s = 
  let rec explode i acc =
    if i < 0 then acc else explode (i - 1) (s.[i] :: acc)
  in explode (String.length s - 1) []

let c2s chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

(* Simple tokenizer - just for testing *)
let simple_tokenize content =
  let tokens = ref [] in
  let i = ref 0 in
  let len = String.length content in
  
  while !i < len do
    match content.[!i] with
    | '\\' ->
        (* Command *)
        let j = ref (!i + 1) in
        while !j < len && 
              (content.[!j] >= 'a' && content.[!j] <= 'z' ||
               content.[!j] >= 'A' && content.[!j] <= 'Z') do
          incr j
        done;
        if !j > !i + 1 then begin
          let cmd = String.sub content (!i + 1) (!j - !i - 1) in
          tokens := TCommand (s2c cmd) :: !tokens;
          i := !j
        end else begin
          tokens := TText (s2c "\\") :: !tokens;
          incr i
        end
    | '{' -> tokens := TBeginGroup :: !tokens; incr i
    | '}' -> tokens := TEndGroup :: !tokens; incr i
    | '$' -> tokens := TMathShift :: !tokens; incr i
    | '^' -> tokens := TSuperscript :: !tokens; incr i
    | '_' -> tokens := TSubscript :: !tokens; incr i
    | '\n' -> tokens := TNewline :: !tokens; incr i
    | ' ' | '\t' -> tokens := TSpace :: !tokens; incr i
    | c -> 
        (* Text *)
        let j = ref (!i + 1) in
        while !j < len && 
              not (List.mem content.[!j] ['\\'; '{'; '}'; '$'; '^'; '_'; '\n'; ' '; '\t']) do
          incr j
        done;
        let text = String.sub content !i (!j - !i) in
        tokens := TText (s2c text) :: !tokens;
        i := !j
  done;
  
  List.rev !tokens

(* Process a file *)
let process_file filepath =
  try
    (* Read file *)
    let ic = open_in filepath in
    let content = 
      try really_input_string ic (in_channel_length ic)
      with _ -> close_in ic; "" in
    close_in ic;
    
    (* Simple tokenization *)
    let tokens = simple_tokenize content in
    
    (* Create document *)
    let doc = {
      tokens = tokens;
      expanded_tokens = Some tokens;
      ast = None;
      semantics = None;
      filename = s2c (Filename.basename filepath);
      doc_layer = L1_Expanded;
    } in
    
    (* Run validators *)
    let issues = run_all_validators doc in
    
    (List.length issues, None)
    
  with e ->
    (0, Some (Printexc.to_string e))

(* Test on real files *)
let () =
  Printf.printf "🧪 SIMPLE CORPUS TEST\n";
  Printf.printf "====================\n\n";
  
  (* Find some test files *)
  let test_files = [
    "corpus/papers/2507.07908v1/main.tex";
    "corpus/papers/2507.07717v1/main.tex";
    "corpus/papers/2506.20025v1/neurips.tex";
  ] in
  
  let total_issues = ref 0 in
  let errors = ref 0 in
  
  List.iter (fun file ->
    if Sys.file_exists file then begin
      Printf.printf "Processing: %s\n" (Filename.basename file);
      match process_file file with
      | (count, None) ->
          Printf.printf "  ✅ Found %d issues\n" count;
          total_issues := !total_issues + count
      | (_, Some err) ->
          Printf.printf "  ❌ Error: %s\n" err;
          incr errors
    end else
      Printf.printf "  ⚠️  File not found: %s\n" file
  ) test_files;
  
  Printf.printf "\n📊 Summary:\n";
  Printf.printf "Total issues found: %d\n" !total_issues;
  Printf.printf "Errors: %d\n" !errors;
  Printf.printf "\n✨ Test complete!\n"