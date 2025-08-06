(* Trace baseline behavior to understand exact logic *)

let trace_baseline input =
  Printf.printf "=== TRACING BASELINE FOR: %S ===\n" input;
  
  (* Create a modified baseline that prints what it's doing *)
  let buffer = Buffer.create 16 in
  let in_command = ref false in
  let in_comment = ref false in
  let tokens = ref [] in
  
  let emit_token tok =
    tokens := tok :: !tokens;
    Printf.printf "  EMIT: %s\n" (match tok with
    | Core.Lexer_v25.TChar (u, _) -> Printf.sprintf "TChar('%c')" (Uchar.to_char u)
    | Core.Lexer_v25.TMacro s -> Printf.sprintf "TMacro('%s')" s
    | Core.Lexer_v25.TGroupOpen -> "TGroupOpen"
    | Core.Lexer_v25.TGroupClose -> "TGroupClose"
    | _ -> "Other")
  in
  
  let flush_buffer typ =
    if Buffer.length buffer > 0 then (
      let content = Buffer.contents buffer in
      Printf.printf "  FLUSH BUFFER (%s): '%s'\n" typ content;
      Buffer.clear buffer;
      match typ with
      | "TEXT" -> 
        let c = content.[0] in
        emit_token (Core.Lexer_v25.TChar (Uchar.of_char c, Data.Catcode.Other))
      | "COMMAND" ->
        emit_token (Core.Lexer_v25.TMacro content)
      | _ -> ()
    )
  in
  
  for i = 0 to String.length input - 1 do
    let c = input.[i] in
    Printf.printf "Process '%c':\n" c;
    
    if !in_comment then (
      match c with
      | '\n' | '\r' -> 
        Printf.printf "  Exit comment\n";
        in_comment := false;
        emit_token (Core.Lexer_v25.TChar (Uchar.of_char c, Data.Catcode.EndLine))
      | _ -> 
        Printf.printf "  Skip (in comment)\n"
    ) else if !in_command then (
      if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') then (
        Printf.printf "  Add to command buffer\n";
        Buffer.add_char buffer c
      ) else (
        flush_buffer "COMMAND";
        in_command := false;
        Printf.printf "  End command, reprocess '%c'\n" c;
        match c with
        | '{' -> emit_token Core.Lexer_v25.TGroupOpen
        | '}' -> emit_token Core.Lexer_v25.TGroupClose
        | _ -> ()
      )
    ) else (
      match c with
      | '\\' ->
        Printf.printf "  Start command\n";
        flush_buffer "TEXT";
        in_command := true
      | '{' ->
        Printf.printf "  Group open (NO FLUSH)\n";
        emit_token Core.Lexer_v25.TGroupOpen
      | '}' ->
        Printf.printf "  Group close (NO FLUSH)\n";
        emit_token Core.Lexer_v25.TGroupClose
      | '%' ->
        Printf.printf "  Start comment\n";
        flush_buffer "TEXT";
        in_comment := true
      | '\n' | '\r' ->
        Printf.printf "  Newline (FLUSH)\n";
        flush_buffer "TEXT";
        emit_token (Core.Lexer_v25.TChar (Uchar.of_char c, Data.Catcode.EndLine))
      | ' ' | '\t' ->
        Printf.printf "  Space - skip\n"
      | _ ->
        Printf.printf "  Add to buffer\n";
        Buffer.add_char buffer c
    )
  done;
  
  Printf.printf "End of input:\n";
  flush_buffer (if !in_command then "COMMAND" else "TEXT");
  
  let final_tokens = List.rev !tokens in
  Printf.printf "\nFinal tokens:\n";
  List.iteri (fun i tok ->
    Printf.printf "%d: %s\n" i (match tok with
    | Core.Lexer_v25.TChar (u, _) -> Printf.sprintf "TChar('%c')" (Uchar.to_char u)
    | Core.Lexer_v25.TMacro s -> Printf.sprintf "TMacro('%s')" s
    | Core.Lexer_v25.TGroupOpen -> "TGroupOpen"
    | Core.Lexer_v25.TGroupClose -> "TGroupClose"
    | _ -> "Other")
  ) final_tokens

let () =
  trace_baseline "{hello}";
  Printf.printf "\n";
  trace_baseline "\\documentclass{article}"