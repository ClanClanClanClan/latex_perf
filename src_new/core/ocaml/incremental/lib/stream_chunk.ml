(* stream_chunk.ml - OCaml implementation of StreamChunk.v from master plans *)

open Formal_state

(* 
   This module implements the chunk-based processing primitive
   as specified in master plans section 3.1 StreamChunk.v,
   providing the foundation for incremental lexing with formal
   equivalence guarantees.
*)

(** Chunk primitive matching Coq specification *)
type chunk = {
  c_state : lexer_state;
  c_bytes : string;
}

(** Token types matching CoreLexer specification *)
type token = 
  | TCommand of string
  | TText of string
  | TMath of string
  | TComment of string
  | TVerbatim of string
  | TBrace of char  (* '{' or '}' *)
  | TNewline

(** Chunk processing function (OCaml version of lex_chunk) *)
let lex_chunk (ck : chunk) : token list * lexer_state =
  let bytes = ck.c_bytes in
  let initial_state = ck.c_state in
  let len = String.length bytes in
  
  let tokens = ref [] in
  let state = ref initial_state in
  let i = ref 0 in
  
  let emit_token tok = tokens := tok :: !tokens in
  
  let rec process_chars () =
    if !i >= len then ()
    else begin
      let c = bytes.[!i] in
      state := advance_position !state c;
      
      match c, !state with
      | '\n', _ ->
          emit_token TNewline;
          state := exit_comment !state;
          incr i;
          process_chars ()
          
      | '%', st when not st.in_verbatim ->
          state := enter_comment !state;
          let comment_start = !i in
          (* Consume rest of line as comment *)
          while !i < len && bytes.[!i] <> '\n' do
            incr i
          done;
          let comment_text = String.sub bytes comment_start (!i - comment_start) in
          emit_token (TComment comment_text);
          process_chars ()
          
      | '$', st when not st.in_verbatim && not st.in_comment ->
          state := toggle_math_mode !state;
          emit_token (TMath "$");
          incr i;
          process_chars ()
          
      | '{', st when not st.in_verbatim && not st.in_comment ->
          state := enter_brace !state;
          emit_token (TBrace '{');
          incr i;
          process_chars ()
          
      | '}', st when not st.in_verbatim && not st.in_comment ->
          state := exit_brace !state;
          emit_token (TBrace '}');
          incr i;
          process_chars ()
          
      | '\\', st when not st.in_verbatim && not st.in_comment && !i + 1 < len ->
          (* Command processing *)
          let cmd_start = !i + 1 in
          incr i; (* skip '\' *)
          incr i; (* move to first char of command *)
          
          (* Extract command name *)
          let cmd_end = ref !i in
          while !cmd_end < len && 
                ((bytes.[!cmd_end] >= 'a' && bytes.[!cmd_end] <= 'z') ||
                 (bytes.[!cmd_end] >= 'A' && bytes.[!cmd_end] <= 'Z')) do
            incr cmd_end
          done;
          
          if !cmd_end > !i then begin
            let cmd_name = String.sub bytes !i (!cmd_end - !i) in
            emit_token (TCommand cmd_name);
            
            (* Handle special commands *)
            (match cmd_name with
            | "verb" | "begin" when !cmd_end < len && bytes.[!cmd_end] = '{' ->
                (* Look for verbatim environment *)
                if String.contains bytes '}' then begin
                  state := enter_verbatim !state;
                end
            | "end" when !cmd_end < len && bytes.[!cmd_end] = '{' ->
                (* Check for end of verbatim *)
                state := exit_verbatim !state
            | _ -> ());
            
            i := !cmd_end
          end else begin
            (* Single character command like \\ *)
            emit_token (TCommand (String.make 1 bytes.[!i]));
            incr i
          end;
          process_chars ()
          
      | c, st when st.in_verbatim ->
          (* In verbatim mode, emit everything as verbatim *)
          let verb_start = !i in
          let verb_end = ref !i in
          
          (* Look for end of verbatim section *)
          while !verb_end < len && 
                not (String.sub bytes !verb_end (min 14 (len - !verb_end)) 
                     |> String.starts_with ~prefix:"\\end{verbatim}") do
            incr verb_end
          done;
          
          let verb_text = String.sub bytes verb_start (!verb_end - verb_start) in
          emit_token (TVerbatim verb_text);
          i := !verb_end;
          process_chars ()
          
      | c, st when st.in_comment ->
          (* Comment mode - consume until newline *)
          incr i;
          process_chars ()
          
      | c, _ ->
          (* Regular text character *)
          emit_token (TText (String.make 1 c));
          incr i;
          process_chars ()
    end
  in
  
  process_chars ();
  (List.rev !tokens, !state)

(** Chunk chain validation (OCaml version of chunk_chain_ok) *)
let rec validate_chunk_chain (chunks : chunk list) : bool =
  match chunks with
  | [] -> true
  | [ck] -> ck.c_state = init_state
  | ck1 :: ck2 :: rest ->
      let (_, end_state) = lex_chunk ck1 in
      ck2.c_state = end_state && validate_chunk_chain (ck2 :: rest)

(** Document processing functions *)
let lex_document (text : string) : token list =
  let chunk = { c_state = init_state; c_bytes = text } in
  let (tokens, _) = lex_chunk chunk in
  tokens

let rec lex_chunks (chunks : chunk list) (acc : token list) : token list =
  match chunks with
  | [] -> List.rev acc
  | ck :: rest ->
      let (tokens, _) = lex_chunk ck in
      lex_chunks rest (List.rev_append tokens acc)

(** Equivalence testing (incremental_equiv property) *)
let test_incremental_equivalence (text : string) (chunks : chunk list) : bool =
  (* Check that concatenated chunks equal original text *)
  let chunk_text = String.concat "" (List.map (fun ck -> ck.c_bytes) chunks) in
  if chunk_text <> text then false
  else begin
    (* Check that chunk chain is valid *)
    if not (validate_chunk_chain chunks) then false
    else begin
      (* Check that batch and incremental produce same tokens *)
      let batch_tokens = lex_document text in
      let incremental_tokens = lex_chunks chunks [] in
      batch_tokens = incremental_tokens
    end
  end

(** Adaptive chunk creation *)
let create_adaptive_chunks (text : string) ?(min_size=16) ?(max_size=1024) () : chunk list =
  let len = String.length text in
  let chunks = ref [] in
  let pos = ref 0 in
  let current_state = ref init_state in
  
  while !pos < len do
    let remaining = len - !pos in
    let chunk_size = 
      if remaining <= min_size then remaining
      else if remaining >= max_size then max_size
      else begin
        (* Find good break point (end of line or command) *)
        let target_size = min max_size (remaining / 2 + min_size) in
        let break_pos = ref (min (!pos + target_size) (len - 1)) in
        
        (* Look for natural break points *)
        while !break_pos > !pos + min_size && 
              text.[!break_pos] <> '\n' && 
              text.[!break_pos] <> '}' && 
              not (text.[!break_pos] = '\\' && !break_pos + 1 < len) do
          decr break_pos
        done;
        
        !break_pos - !pos + 1
      end
    in
    
    let chunk_text = String.sub text !pos chunk_size in
    let chunk = { c_state = !current_state; c_bytes = chunk_text } in
    chunks := chunk :: !chunks;
    
    (* Update state for next chunk *)
    let (_, end_state) = lex_chunk chunk in
    current_state := end_state;
    pos := !pos + chunk_size
  done;
  
  List.rev !chunks

(** Performance measurement utilities *)
let benchmark_chunk_processing (text : string) : float * float =
  let start_time = Unix.gettimeofday () in
  let _ = lex_document text in
  let batch_time = Unix.gettimeofday () -. start_time in
  
  let chunks = create_adaptive_chunks text () in
  let start_time = Unix.gettimeofday () in
  let _ = lex_chunks chunks [] in
  let chunk_time = Unix.gettimeofday () -. start_time in
  
  (batch_time, chunk_time)

(** Debug and testing utilities *)
let string_of_token = function
  | TCommand s -> "CMD(" ^ s ^ ")"
  | TText s -> "TXT(" ^ s ^ ")"
  | TMath s -> "MATH(" ^ s ^ ")"
  | TComment s -> "CMT(" ^ s ^ ")"
  | TVerbatim s -> "VERB(" ^ s ^ ")"
  | TBrace c -> "BRACE(" ^ String.make 1 c ^ ")"
  | TNewline -> "NL"

let print_tokens (tokens : token list) : unit =
  List.iter (fun tok -> Printf.printf "%s " (string_of_token tok)) tokens;
  Printf.printf "\n"

let string_of_chunk (ck : chunk) : string =
  Printf.sprintf "{ state=%s, bytes=%S }" 
    (string_of_state ck.c_state) ck.c_bytes

(** Self-test for chunk processing *)
let run_chunk_tests () : bool =
  let test_cases = [
    "";
    "hello world";
    "% comment\ntext";
    "$x^2 + y^2 = z^2$";
    "\\section{Title}";
    "{nested {braces}}";
    "\\begin{verbatim}\nraw text\n\\end{verbatim}";
  ] in
  
  List.for_all (fun text ->
    let chunks = create_adaptive_chunks text () in
    test_incremental_equivalence text chunks
  ) test_cases