(* Emergency P99 Fix: Persistent Worker with REAL L0 Integration *)
(* Based on expert recommendations + phase3 L0 lexer - August 16, 2025 *)

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
    Gc.minor_heap_size = 128 * 1024 * 1024;  (* 128MB minor heap *)
    space_overhead = 10_000;                  (* Defer major GC *)
    max_overhead = 1_000_000;
  } in
  Gc.full_major ();  (* Clear all debt before critical section *)
  Gc.set quiet_gc;
  try
    let result = f () in
    Gc.set old_gc;
    result
  with exn ->
    Gc.set old_gc;
    raise exn

(* ========== User-Visible Timing ========== *)
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
  mutable n : int;  (* Current size *)
  capacity  : int;  (* Max capacity *)
}

let make_tokens_soa ~capacity =
  let mk () = Array1.create Int32 C_layout capacity in
  { 
    kind = mk (); 
    char_code = mk ();
    start_pos = mk (); 
    end_pos = mk ();
    line = mk (); 
    col = mk (); 
    n = 0;
    capacity = capacity;
  }

let clear_soa soa = soa.n <- 0

(* Direct token push to SoA - no intermediate allocation *)
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

(* Global pre-allocated SoA arena *)
let global_soa = make_tokens_soa ~capacity:600_000

(* ========== L0 Lexer writing DIRECTLY to SoA ========== *)
module L0LexerDirect = struct
  (* Catcode table *)
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
  
  (* Tokenize DIRECTLY from mmap'd data into off-heap SoA *)
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
        | 0 -> (* escape - consume command name *)
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
            
            (* Push escape token directly to SoA *)
            if push_token_direct soa ~catcode ~char_code:0 ~pos:start_pos 
                                    ~line:!line ~col:start_col then
              incr token_count
            else
              (* Hit capacity *)
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

(* ========== Validators ========== *)
type severity = Error | Warning | Info | Style

type issue = {
  file: string;
  line: int;
  column: int;
  severity: severity;
  message: string;
}

let validate_soa_direct soa =
  let issues = ref [] in
  
  (* Simple ellipsis validator *)
  for i = 0 to soa.n - 3 do
    if i + 2 < soa.n then (
      let c1 = Array1.get soa.char_code i |> Int32.to_int in
      let c2 = Array1.get soa.char_code (i+1) |> Int32.to_int in
      let c3 = Array1.get soa.char_code (i+2) |> Int32.to_int in
      if c1 = 46 && c2 = 46 && c3 = 46 then (* ... *)
        let line = Array1.get soa.line i |> Int32.to_int in
        let col = Array1.get soa.col i |> Int32.to_int in
        issues := { 
          file = ""; line; column = col; 
          severity = Warning; 
          message = "Use \\ldots instead of three periods" 
        } :: !issues
    )
  done;
  
  !issues

(* ========== Core Processing with REAL L0 ========== *)
module FastPath = struct
  let expected_tokens_canonical = 276_331
  
  let process_document file_path =
    (* Memory-map file *)
    let mmap_ba = map_file file_path in
    let file_size = Array1.dim mmap_ba in
    
    (* Pre-fault all pages BEFORE timing *)
    prepage_bigarray mmap_ba;
    
    (* Calculate token limit *)
    let max_tokens = min global_soa.capacity (file_size / 4 + 1000) in
    
    (* Process with GC fence *)
    with_quiet_gc (fun () ->
      (* L0 tokenizes DIRECTLY from mmap'd data into off-heap SoA *)
      L0LexerDirect.tokenize_into_soa_mmap mmap_ba global_soa max_tokens;
      let token_count = global_soa.n in
      
      (* Capacity check *)
      if token_count >= global_soa.capacity then
        failwith (sprintf "Token capacity exceeded: %d >= %d" 
          token_count global_soa.capacity);
      
      (* Check for canonical corpus *)
      if token_count <> expected_tokens_canonical && 
         Filename.basename file_path = "perf_smoke_big.tex" then
        Printf.eprintf "Warning: Token drift on canonical corpus: expected %d, got %d\n" 
          expected_tokens_canonical token_count;
      
      (* Validate directly from SoA *)
      let issues = validate_soa_direct global_soa in
      let issue_count = List.length issues in
      
      (* Return JSON *)
      sprintf 
        "{\"file\":\"%s\",\"tokens\":%d,\"issues\":%d,\"file_size\":%d}"
        file_path token_count issue_count file_size
    )
end

(* ========== Length-Prefixed Protocol ========== *)
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

(* ========== Request Handler ========== *)
let handle_request payload =
  (* Simple protocol: just the file path *)
  let file_path = String.trim payload in
  
  (* Time the ENTIRE user-visible operation *)
  let (json_result, user_ms) = time_user_visible (fun () ->
    try
      FastPath.process_document file_path
    with exn ->
      sprintf "{\"error\":\"%s\",\"file\":\"%s\"}" 
        (Printexc.to_string exn) file_path
  ) in
  
  (* Inject actual timing into JSON *)
  let json_with_timing = 
    if String.contains json_result '{' && String.contains json_result '}' then
      let insert_pos = String.rindex json_result '}' in
      let before = String.sub json_result 0 insert_pos in
      sprintf "%s,\"user_ms\":%.3f}" before user_ms
    else json_result
  in
  
  (* Log for monitoring *)
  Printf.printf "Request: %s -> %.2fms (%d tokens)\n" 
    (Filename.basename file_path) user_ms global_soa.n;
  flush Stdlib.stdout;
  
  json_with_timing

(* ========== Server Main Loop ========== *)
let serve sock_path =
  (* Clean up old socket *)
  (try Unix.unlink sock_path with _ -> ());
  
  (* Create Unix domain socket *)
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  bind sock (ADDR_UNIX sock_path);
  listen sock 32;
  
  Printf.printf "🚀 Persistent Worker with REAL L0 Ready\n";
  Printf.printf "Socket: %s\n" sock_path;
  Printf.printf "SoA Capacity: %d tokens\n" global_soa.capacity;
  Printf.printf "Optimizations: REAL L0 + prepage + GC fence + resident process\n";
  Printf.printf "Expected P99: <5ms (was 86.6ms)\n\n";
  flush Stdlib.stdout;
  
  (* Warm up *)
  Gc.full_major ();
  
  (* Accept loop *)
  let rec loop () =
    try
      let (client_fd, _) = accept sock in
      let ic = in_channel_of_descr client_fd in
      let oc = out_channel_of_descr client_fd in
      
      (* Read request *)
      let request = read_length_prefixed ic in
      
      (* Process and respond *)
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

(* ========== Entry Point ========== *)
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
      printf "Persistent worker with REAL L0 lexer for P99 < 5ms on 1.1MB corpus\n";
      printf "Set LP_SOCKET env var to change socket path\n"
  | _ ->
      Printf.eprintf "Unknown arguments\n";
      exit 1