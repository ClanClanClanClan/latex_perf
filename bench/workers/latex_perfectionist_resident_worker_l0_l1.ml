(* Resident Worker with L0 + L1 Zero-Copy Integration *)
(* Phase 2: Add L1 expansion without breaking P99 performance *)

open Unix
open Printf
open Bigarray

(* ========== Pre-paging Support ========== *)
let prepage_bigarray ba =
  let len = Array1.dim ba in
  let page_size = 4096 in
  let acc = ref 0 in
  let rec touch i =
    if i < len then begin
      acc := !acc land (Char.code (Array1.unsafe_get ba i));
      touch (i + page_size)
    end
  in
  touch 0;
  Sys.opaque_identity !acc |> ignore

(* ========== GC Fence ========== *)  
let with_quiet_gc f =
  let old_gc = Gc.get () in
  let quiet_gc = { old_gc with
    Gc.minor_heap_size = 128 * 1024 * 1024;
    space_overhead = 10_000;
    max_overhead = 1_000_000;
  } in
  Gc.full_major ();
  Gc.set quiet_gc;
  try
    let result = f () in
    Gc.set old_gc;
    result
  with exn ->
    Gc.set old_gc;
    raise exn

let time_user_visible f =
  let t0 = Unix.gettimeofday () in
  let result = f () in
  let t1 = Unix.gettimeofday () in
  (result, (t1 -. t0) *. 1000.0)

(* ========== Off-heap Structure of Arrays ========== *)
type tokens_soa = {
  kind      : (int32, int32_elt, c_layout) Array1.t;
  char_code : (int32, int32_elt, c_layout) Array1.t;
  start_pos : (int32, int32_elt, c_layout) Array1.t;
  end_pos   : (int32, int32_elt, c_layout) Array1.t;
  line      : (int32, int32_elt, c_layout) Array1.t;
  col       : (int32, int32_elt, c_layout) Array1.t;
  mutable n : int;
  capacity  : int;
}

let make_tokens_soa ~capacity =
  let mk () = Array1.create Int32 C_layout capacity in
  { 
    kind = mk (); char_code = mk (); start_pos = mk (); 
    end_pos = mk (); line = mk (); col = mk (); 
    n = 0; capacity = capacity;
  }

let clear_soa soa = soa.n <- 0

let[@inline always] push_token_direct soa ~catcode ~char_code ~pos ~line ~col =
  if soa.n < soa.capacity then (
    let i = soa.n in
    Array1.unsafe_set soa.kind i (Int32.of_int catcode);
    Array1.unsafe_set soa.char_code i (Int32.of_int char_code);
    Array1.unsafe_set soa.start_pos i (Int32.of_int pos);
    Array1.unsafe_set soa.end_pos i (Int32.of_int (pos + 1));
    Array1.unsafe_set soa.line i (Int32.of_int line);
    Array1.unsafe_set soa.col i (Int32.of_int col);
    soa.n <- i + 1;
    true
  ) else false

let global_soa = make_tokens_soa ~capacity:600_000

(* ========== L1 Macro Table (Compact) ========== *)
module L1Macros = struct
  (* Simplified but realistic macro table *)
  let macro_expansions = [|
    ("\\alpha", "α"); ("\\beta", "β"); ("\\gamma", "γ"); ("\\delta", "δ");
    ("\\epsilon", "ε"); ("\\lambda", "λ"); ("\\mu", "μ"); ("\\pi", "π");
    ("\\sigma", "σ"); ("\\tau", "τ"); ("\\phi", "φ"); ("\\omega", "ω");
    ("\\sum", "Σ"); ("\\prod", "Π"); ("\\int", "∫"); ("\\infty", "∞");
    ("\\partial", "∂"); ("\\nabla", "∇"); ("\\pm", "±"); ("\\times", "×");
    ("\\ldots", "…"); ("\\cdots", "⋯"); ("\\vdots", "⋮");
    ("\\textbf", "@BOLD@"); ("\\textit", "@ITALIC@"); ("\\emph", "@EMPH@");
  |]
  
  let macro_hash = 
    let h = Hashtbl.create 64 in
    Array.iter (fun (pattern, expansion) -> 
      Hashtbl.add h pattern expansion
    ) macro_expansions;
    h
  
  let find_expansion pattern = 
    try Some (Hashtbl.find macro_hash pattern)
    with Not_found -> None
end

(* ========== L0 Lexer (Enhanced with macro text extraction) ========== *)
module L0LexerDirect = struct
  let catcode_table = Bytes.create 256
  let () =
    Bytes.fill catcode_table 0 256 (Char.chr 12);
    let set_catcode ascii catcode = Bytes.set_uint8 catcode_table ascii catcode in
    set_catcode 92 0;   (* \ escape *)
    set_catcode 123 1;  (* { begin group *)
    set_catcode 125 2;  (* } end group *)
    set_catcode 36 3;   (* $ math *)
    set_catcode 32 10;  (* space *)
    set_catcode 10 5;   (* newline *)
    set_catcode 37 14;  (* % comment *)
    for i = 97 to 122 do set_catcode i 11 done;  (* a-z letter *)
    for i = 65 to 90 do set_catcode i 11 done    (* A-Z letter *)
  
  (* Enhanced tokenizer that records exact positions for macro extraction *)
  let tokenize_into_soa_mmap input_ba soa max_tokens =
    let len = Array1.dim input_ba in
    if len = 0 then () else begin
      clear_soa soa;
      let pos = ref 0 in
      let line = ref 1 in
      let col = ref 1 in
      let token_count = ref 0 in
      
      while !pos < len && !token_count < max_tokens do
        let c = Array1.unsafe_get input_ba !pos in
        let code = Char.code c in
        let catcode = Bytes.get_uint8 catcode_table code in
        
        match catcode with
        | 0 -> (* escape - record exact start/end for macro extraction *)
            let start_pos = !pos in
            let start_col = !col in
            incr pos; incr col;
            
            (* Consume letters for command name *)
            while !pos < len && 
                  let c = Array1.unsafe_get input_ba !pos in
                  let code = Char.code c in
                  (code >= 97 && code <= 122) || (code >= 65 && code <= 90) do
              incr pos; incr col
            done;
            
            (* Store with exact end position for later text extraction *)
            if soa.n < soa.capacity then (
              let i = soa.n in
              Array1.unsafe_set soa.kind i (Int32.of_int catcode);
              Array1.unsafe_set soa.char_code i (Int32.of_int 0);
              Array1.unsafe_set soa.start_pos i (Int32.of_int start_pos);
              Array1.unsafe_set soa.end_pos i (Int32.of_int !pos);  (* Exact end *)
              Array1.unsafe_set soa.line i (Int32.of_int !line);
              Array1.unsafe_set soa.col i (Int32.of_int start_col);
              soa.n <- i + 1;
              incr token_count
            ) else
              pos := len
              
        | 14 -> (* comment - skip to end of line *)
            incr pos; incr col;
            while !pos < len && Array1.unsafe_get input_ba !pos <> '\n' do 
              incr pos; incr col 
            done
            
        | 5 -> (* newline *)
            if push_token_direct soa ~catcode ~char_code:code ~pos:!pos 
                                    ~line:!line ~col:!col then
              incr token_count
            else
              pos := len;
            incr pos;
            incr line;
            col := 1
            
        | _ -> (* regular token *)
            if push_token_direct soa ~catcode ~char_code:code ~pos:!pos 
                                    ~line:!line ~col:!col then
              incr token_count
            else
              pos := len;
            incr pos;
            incr col
      done
    end
end

(* ========== Zero-Copy L1 Expansion ========== *)
module L1ExpansionIterator = struct
  type expanded_token = 
    | Original of int                    (* Index in SoA *)
    | Synthetic of string * int * int    (* Expansion text, line, col *)
  
  type iterator = {
    soa: tokens_soa;
    source_text: (char, int8_unsigned_elt, c_layout) Array1.t;
    mutable position: int;
    mutable expansions: expanded_token list;
    mutable total_tokens: int;
  }
  
  let create_iterator soa source_text =
    { soa; source_text; position = 0; expansions = []; total_tokens = 0 }
  
  (* Extract macro text using start/end positions *)
  let extract_macro_text source_text start_pos end_pos =
    let len = end_pos - start_pos in
    if len > 0 && len < 64 then (* reasonable macro length *)
      let buffer = Bytes.create len in
      for i = 0 to len - 1 do
        Bytes.set buffer i (Array1.unsafe_get source_text (start_pos + i))
      done;
      Some (Bytes.to_string buffer)
    else None
  
  (* Process all tokens with L1 expansion *)
  let expand_all iter =
    iter.position <- 0;
    iter.expansions <- [];
    iter.total_tokens <- 0;
    
    while iter.position < iter.soa.n do
      let catcode = Array1.get iter.soa.kind iter.position |> Int32.to_int in
      
      if catcode = 0 then (* macro token *)
        let start_pos = Array1.get iter.soa.start_pos iter.position |> Int32.to_int in
        let end_pos = Array1.get iter.soa.end_pos iter.position |> Int32.to_int in
        let line = Array1.get iter.soa.line iter.position |> Int32.to_int in
        let col = Array1.get iter.soa.col iter.position |> Int32.to_int in
        
        match extract_macro_text iter.source_text start_pos end_pos with
        | Some macro_text ->
            (match L1Macros.find_expansion macro_text with
             | Some expansion ->
                 (* Macro found - emit synthetic token *)
                 iter.expansions <- Synthetic (expansion, line, col) :: iter.expansions;
                 iter.total_tokens <- iter.total_tokens + 1
             | None ->
                 (* Unknown macro - emit original *)
                 iter.expansions <- Original iter.position :: iter.expansions;
                 iter.total_tokens <- iter.total_tokens + 1)
        | None ->
            (* Invalid macro - emit original *)
            iter.expansions <- Original iter.position :: iter.expansions;
            iter.total_tokens <- iter.total_tokens + 1
      else (
        (* Regular token - emit original *)
        iter.expansions <- Original iter.position :: iter.expansions;
        iter.total_tokens <- iter.total_tokens + 1
      );
      
      iter.position <- iter.position + 1
    done;
    
    iter.expansions <- List.rev iter.expansions
  
  let get_expansion_count iter =
    List.fold_left (fun acc -> function
      | Synthetic _ -> acc + 1
      | Original _ -> acc
    ) 0 iter.expansions
end

(* ========== Memory-mapped file I/O ========== *)
let map_file path =
  let fd = Unix.(openfile path [O_RDONLY] 0) in
  let stat = Unix.LargeFile.fstat fd in
  let len = stat.Unix.LargeFile.st_size in
  
  if len = 0L then begin
    Unix.close fd;
    Array1.create Char c_layout 0
  end else begin
    let mapped = Unix.map_file fd Char c_layout false [| Int64.to_int len |] in
    let mapped_1d = Bigarray.array1_of_genarray mapped in
    Unix.close fd;
    mapped_1d
  end

(* ========== Enhanced Validators (operate on expanded tokens) ========== *)
type issue = {
  file: string;
  line: int;
  column: int;
  severity: string;
  message: string;
}

let validate_expanded_tokens iter =
  let issues = ref [] in
  
  (* Check for unexpanded ellipsis patterns *)
  let tokens = iter.L1ExpansionIterator.expansions in
  let rec check_ellipsis = function
    | L1ExpansionIterator.Synthetic ("…", line, col) :: _ ->
        (* Good - ellipsis was expanded from \ldots *)
        ()
    | L1ExpansionIterator.Original i1 :: L1ExpansionIterator.Original i2 :: L1ExpansionIterator.Original i3 :: rest ->
        (* Check for raw ... pattern *)
        let c1 = Array1.get iter.soa.char_code i1 |> Int32.to_int in
        let c2 = Array1.get iter.soa.char_code i2 |> Int32.to_int in  
        let c3 = Array1.get iter.soa.char_code i3 |> Int32.to_int in
        if c1 = 46 && c2 = 46 && c3 = 46 then (
          let line = Array1.get iter.soa.line i1 |> Int32.to_int in
          let col = Array1.get iter.soa.col i1 |> Int32.to_int in
          issues := { 
            file = ""; line; column = col; 
            severity = "warning"; 
            message = "Use \\ldots instead of three periods" 
          } :: !issues
        );
        check_ellipsis rest
    | _ :: rest -> check_ellipsis rest
    | [] -> ()
  in
  
  check_ellipsis tokens;
  !issues

(* ========== Core Processing with L0 + L1 Integration ========== *)
module FastPath = struct
  let expected_tokens_canonical = 276_331
  
  let process_document file_path =
    let mmap_ba = map_file file_path in
    let file_size = Array1.dim mmap_ba in
    
    prepage_bigarray mmap_ba;
    
    let max_tokens = min global_soa.capacity (file_size / 4 + 1000) in
    
    with_quiet_gc (fun () ->
      (* L0: Tokenize directly to SoA *)
      L0LexerDirect.tokenize_into_soa_mmap mmap_ba global_soa max_tokens;
      let l0_token_count = global_soa.n in
      
      (* L1: Zero-copy expansion *)
      let l1_iter = L1ExpansionIterator.create_iterator global_soa mmap_ba in
      L1ExpansionIterator.expand_all l1_iter;
      let expansion_count = L1ExpansionIterator.get_expansion_count l1_iter in
      let total_tokens = l1_iter.total_tokens in
      
      (* Validation: Operate on expanded token stream *)
      let issues = validate_expanded_tokens l1_iter in
      let issue_count = List.length issues in
      
      (* Capacity check *)
      if l0_token_count >= global_soa.capacity then
        failwith (sprintf "Token capacity exceeded: %d >= %d" 
          l0_token_count global_soa.capacity);
      
      (* Token count validation *)
      if l0_token_count <> expected_tokens_canonical && 
         Filename.basename file_path = "perf_smoke_big.tex" then
        Printf.eprintf "Warning: L0 token drift: expected %d, got %d\n" 
          expected_tokens_canonical l0_token_count;
      
      sprintf 
        "{\"file\":\"%s\",\"l0_tokens\":%d,\"l1_total_tokens\":%d,\"l1_expansions\":%d,\"issues\":%d,\"file_size\":%d}"
        file_path l0_token_count total_tokens expansion_count issue_count file_size
    )
end

(* ========== Protocol & Server (same as before) ========== *)
let write_length_prefixed oc data =
  let len = String.length data in
  output_binary_int oc len;
  output_string oc data;
  flush oc

let read_length_prefixed ic =
  let len = input_binary_int ic in
  if len < 0 || len > 10_000_000 then
    failwith "Invalid message length";
  really_input_string ic len

let handle_request payload =
  let file_path = String.trim payload in
  
  let (json_result, user_ms) = time_user_visible (fun () ->
    try
      FastPath.process_document file_path
    with exn ->
      sprintf "{\"error\":\"%s\",\"file\":\"%s\"}" 
        (Printexc.to_string exn) file_path
  ) in
  
  let json_with_timing = 
    if String.contains json_result '{' && String.contains json_result '}' then
      let insert_pos = String.rindex json_result '}' in
      let before = String.sub json_result 0 insert_pos in
      sprintf "%s,\"user_ms\":%.3f}" before user_ms
    else json_result
  in
  
  Printf.printf "Request: %s -> %.2fms (L0+L1 integrated)\n" 
    (Filename.basename file_path) user_ms;
  flush Stdlib.stdout;
  
  json_with_timing

let serve sock_path =
  (try Unix.unlink sock_path with _ -> ());
  
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  bind sock (ADDR_UNIX sock_path);
  listen sock 32;
  
  Printf.printf "🚀 Persistent Worker with L0 + L1 Integration\n";
  Printf.printf "Socket: %s\n" sock_path;
  Printf.printf "Features: Real L0 + Zero-copy L1 + %d macros\n" 
    (Array.length L1Macros.macro_expansions);
  Printf.printf "Expected P99: <5ms (maintain performance with L1)\n\n";
  flush Stdlib.stdout;
  
  Gc.full_major ();
  
  let rec loop () =
    try
      let (client_fd, _) = accept sock in
      let ic = in_channel_of_descr client_fd in
      let oc = out_channel_of_descr client_fd in
      
      let request = read_length_prefixed ic in
      let response = handle_request request in
      write_length_prefixed oc response;
      
      close client_fd;
      loop ()
    with
    | Unix_error (EINTR, _, _) -> loop ()
    | exn ->
        Printf.eprintf "Worker error: %s\n" (Printexc.to_string exn);
        flush Stdlib.stderr;
        loop ()
  in
  loop ()

let () =
  let sock_path = 
    try Sys.getenv "LP_SOCKET"
    with Not_found -> "/tmp/latex_perfectionist.sock"
  in
  
  match Sys.argv with
  | [| _ |] | [| _; "--serve" |] -> 
      serve sock_path
  | [| _; "--help" |] ->
      printf "Usage: %s [--serve]\n" Sys.argv.(0);
      printf "Persistent worker with L0 + L1 integration\n";
      printf "Maintains P99 < 5ms while expanding macros\n"
  | _ ->
      Printf.eprintf "Unknown arguments\n";
      exit 1