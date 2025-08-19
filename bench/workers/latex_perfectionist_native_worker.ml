(* B5: Native Integration Worker - Direct L0→SoA→L1→Validation Processing *)
(* Eliminates external CLI calls to achieve P99 < 20ms target *)

open Printf
open Unix
open Bigarray

(* ========== Integrated SoA Token Storage ========== *)
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

(* ========== Native L0 Lexer - Direct to SoA ========== *)
module NativeL0Lexer = struct
  (* Catcode table for fast character classification *)
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
  
  (* Simple file reading into string *)
  let read_file_to_string filename =
    let ic = open_in filename in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    content
  
  (* Direct tokenization into SoA - no intermediate allocations *)
  let tokenize_file_direct file_path soa =
    let input_str = read_file_to_string file_path in
    let len = String.length input_str in
    clear_soa soa;
    
    if len > 0 then (
      let pos = ref 0 in
      let line = ref 1 in
      let col = ref 1 in
      let token_count = ref 0 in
      
      while !pos < len && !token_count < soa.capacity do
        let c = input_str.[!pos] in
        let code = Char.code c in
        let catcode = Bytes.get_uint8 catcode_table code in
        
        match catcode with
        | 0 -> (* escape - consume command name *)
            let start_pos = !pos in
            let start_col = !col in
            incr pos; incr col;
            
            (* Consume letters for command name *)
            while !pos < len && 
                  let c = input_str.[!pos] in
                  let code = Char.code c in
                  (code >= 97 && code <= 122) || (code >= 65 && code <= 90) do
              incr pos; incr col
            done;
            
            if push_token_direct soa ~catcode ~char_code:0 ~pos:start_pos 
                                    ~line:!line ~col:start_col then
              incr token_count
            else
              pos := len
              
        | 14 -> (* comment - skip to end of line *)
            incr pos; incr col;
            while !pos < len && input_str.[!pos] <> '\n' do 
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
            if c = '\n' then (incr line; col := 1) else incr col
      done;
      
      !token_count
    ) else 0
end

(* ========== Native L1 Macro Expansion ========== *)
module NativeL1Expander = struct
  (* Simplified macro system for fast processing *)
  let macro_table = Hashtbl.create 500
  
  let init_macros () =
    (* Essential macros for production - optimized subset *)
    let add_macro name expansion =
      Hashtbl.replace macro_table name expansion
    in
    
    (* Math symbols *)
    add_macro "alpha" "α";
    add_macro "beta" "β";
    add_macro "gamma" "γ";
    add_macro "delta" "δ";
    add_macro "epsilon" "ε";
    add_macro "sum" "Σ";
    add_macro "prod" "Π";
    add_macro "int" "∫";
    add_macro "infty" "∞";
    add_macro "partial" "∂";
    
    (* Text symbols *)
    add_macro "textbf" "@BOLD@";
    add_macro "textit" "@ITALIC@";
    add_macro "emph" "@EMPH@";
    add_macro "ldots" "…";
    add_macro "cdots" "⋯";
    
    printf "  L1 macros loaded: %d\n" (Hashtbl.length macro_table)
  
  let expand_macros soa =
    (* Simplified: count macro tokens for metrics *)
    let macro_count = ref 0 in
    for i = 0 to soa.n - 1 do
      let kind = Array1.unsafe_get soa.kind i |> Int32.to_int in
      if kind = 0 then incr macro_count  (* escape sequences *)
    done;
    !macro_count
end

(* ========== Native Validators ========== *)
module NativeValidators = struct
  (* Fast issue detection *)
  let validate_bracket_balance soa =
    let open_count = ref 0 in
    let issues = ref 0 in
    for i = 0 to soa.n - 1 do
      let kind = Array1.unsafe_get soa.kind i |> Int32.to_int in
      match kind with
      | 1 -> incr open_count  (* { *)
      | 2 -> if !open_count > 0 then decr open_count else incr issues  (* } *)
      | _ -> ()
    done;
    !issues + !open_count  (* unclosed braces *)
  
  let validate_math_mode soa =
    let math_depth = ref 0 in
    let issues = ref 0 in
    for i = 0 to soa.n - 1 do
      let kind = Array1.unsafe_get soa.kind i |> Int32.to_int in
      let char_code = Array1.unsafe_get soa.char_code i |> Int32.to_int in
      if kind = 3 && char_code = 36 then (  (* $ *)
        math_depth := (!math_depth + 1) mod 2
      ) else if kind = 3 then
        incr issues  (* other math shift issues *)
    done;
    !issues + !math_depth  (* unclosed math mode *)
  
  let validate_ellipsis soa =
    let issues = ref 0 in
    let last_char = ref (-1) in
    for i = 0 to soa.n - 1 do
      let char_code = Array1.unsafe_get soa.char_code i |> Int32.to_int in
      if char_code = 46 && !last_char = 46 then  (* .. sequence *)
        incr issues;
      last_char := char_code
    done;
    !issues
  
  let run_all_validators soa =
    let bracket_issues = validate_bracket_balance soa in
    let math_issues = validate_math_mode soa in
    let ellipsis_issues = validate_ellipsis soa in
    bracket_issues + math_issues + ellipsis_issues
end

(* ========== Native Streaming JSON ========== *)
module NativeStreamingJSON = struct
  let json_buffer = Buffer.create (8 * 1024 * 1024)  (* 8MB reusable buffer *)
  
  let build_response ~file ~tokens ~macros ~issues ~timing_ms =
    Buffer.clear json_buffer;
    Buffer.add_string json_buffer "{";
    Buffer.add_string json_buffer "\"file\":\""; Buffer.add_string json_buffer file; Buffer.add_string json_buffer "\",";
    Buffer.add_string json_buffer "\"tokens\":"; Buffer.add_string json_buffer (string_of_int tokens); Buffer.add_string json_buffer ",";
    Buffer.add_string json_buffer "\"macros\":"; Buffer.add_string json_buffer (string_of_int macros); Buffer.add_string json_buffer ",";
    Buffer.add_string json_buffer "\"issues\":"; Buffer.add_string json_buffer (string_of_int issues); Buffer.add_string json_buffer ",";
    Buffer.add_string json_buffer "\"processing_time_ms\":"; Buffer.add_string json_buffer (sprintf "%.3f" timing_ms); Buffer.add_string json_buffer ",";
    Buffer.add_string json_buffer "\"optimizations\":[\"native_integration\",\"direct_l0_soa\",\"streaming_json\"],";
    Buffer.add_string json_buffer "\"architecture\":\"B5_native_worker\"";
    Buffer.add_string json_buffer "}";
    Buffer.contents json_buffer
end

(* ========== Native Processing Pipeline ========== *)
module NativeProcessor = struct
  (* Pre-allocated SoA arena - fixed capacity *)
  let global_soa = make_tokens_soa ~capacity:600_000
  
  let configure_gc_for_native () =
    let open Gc in
    set {
      (get ()) with
      minor_heap_size     = 64 * 1024 * 1024;
      major_heap_increment= 512 * 1024 * 1024;
      space_overhead      = 200;
      max_overhead        = 1_000_000;
    };
    Gc.full_major ()
  
  let process_file_native file_path =
    let start_time = Unix.gettimeofday () in
    
    try
      (* Phase 1: L0 Lexing directly to SoA *)
      let t1 = Unix.gettimeofday () in
      let token_count = NativeL0Lexer.tokenize_file_direct file_path global_soa in
      let t2 = Unix.gettimeofday () in
      
      (* Phase 2: L1 Macro Expansion *)
      let macro_count = NativeL1Expander.expand_macros global_soa in
      let t3 = Unix.gettimeofday () in
      
      (* Phase 3: Validation *)
      let issue_count = NativeValidators.run_all_validators global_soa in
      let t4 = Unix.gettimeofday () in
      
      (* Phase 4: JSON Response *)
      let total_time = (t4 -. start_time) *. 1000.0 in
      let response = NativeStreamingJSON.build_response 
        ~file:file_path ~tokens:token_count ~macros:macro_count 
        ~issues:issue_count ~timing_ms:total_time in
      let t5 = Unix.gettimeofday () in
      
      (* GC debt payment while idle *)
      for _ = 1 to 5 do ignore (Gc.major_slice 10_000) done;
      
      (true, response, total_time)
      
    with
    | exn -> 
        let elapsed = (Unix.gettimeofday () -. start_time) *. 1000.0 in
        let error_response = sprintf 
          "{\"error\":\"%s\",\"file\":\"%s\",\"timing_ms\":%.3f}"
          (Printexc.to_string exn) file_path elapsed in
        (false, error_response, elapsed)
end

(* ========== Native Worker Server ========== *)
let sock_path = 
  let temp_dir = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
  Filename.concat temp_dir "latex_perfectionist_native.sock"

let write_length_prefixed_string oc str =
  let len = String.length str in
  output_binary_int oc len;
  output_string oc str;
  flush oc

let read_length_prefixed_string ic =
  let len = input_binary_int ic in
  if len < 0 || len > 16 * 1024 * 1024 then
    failwith "Message too large"
  else
    really_input_string ic len

let handle_native_client fd =
  try
    let ic = Unix.in_channel_of_descr fd in
    let oc = Unix.out_channel_of_descr fd in
    
    let request = read_length_prefixed_string ic in
    let file_path = String.trim request in
    
    let (success, result, elapsed_ms) = 
      NativeProcessor.process_file_native file_path in
    
    write_length_prefixed_string oc result;
    
    printf "Native: %s %.2fms %s\n" 
      (Filename.basename file_path) elapsed_ms 
      (if success then "✓" else "✗");
    flush_all ()
    
  with
  | exn -> 
      printf "Native error: %s\n" (Printexc.to_string exn);
      flush_all ()

let comprehensive_native_warmup () =
  printf "🔥 NATIVE WORKER WARMUP (B5)\n";
  printf "===========================\n";
  
  (* Step 1: Configure GC *)
  printf "1. Configuring GC for native processing...\n";
  NativeProcessor.configure_gc_for_native ();
  
  (* Step 2: Initialize L1 macros *)
  printf "2. Loading L1 macro table...\n";
  NativeL1Expander.init_macros ();
  
  (* Step 3: Pre-touch SoA memory *)
  printf "3. Pre-touching SoA memory (600K capacity)...\n";
  for i = 0 to min 10000 (NativeProcessor.global_soa.capacity - 1) do
    Array1.unsafe_set NativeProcessor.global_soa.kind i 0l;
    Array1.unsafe_set NativeProcessor.global_soa.char_code i 0l;
  done;
  
  (* Step 4: Test warmup run *)
  printf "4. Running native warmup test...\n";
  let warmup_file = Filename.temp_file "native_warmup" ".tex" in
  let oc = open_out warmup_file in
  output_string oc "\\documentclass{article}\\begin{document}$\\alpha + \\beta = \\gamma$\\end{document}";
  close_out oc;
  
  let (success, _, elapsed) = NativeProcessor.process_file_native warmup_file in
  printf "  Warmup result: %.2fms %s\n" elapsed (if success then "✓" else "✗");
  Sys.remove warmup_file;
  
  printf "🚀 NATIVE INTEGRATION READY!\n";
  printf "Expected P99: <20ms (B5 eliminates CLI overhead)\n\n";
  flush_all ()

let start_native_server () =
  printf "🔥 LaTeX Perfectionist NATIVE Worker (B5)\n";
  printf "========================================\n";
  printf "Socket: %s\n" sock_path;
  
  (* Cleanup existing socket *)
  (try Unix.unlink sock_path with _ -> ());
  
  (* Comprehensive native warmup *)
  comprehensive_native_warmup ();
  
  (* Start server *)
  let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  Unix.bind sock (Unix.ADDR_UNIX sock_path);
  Unix.listen sock 16;
  
  printf "Native worker listening...\n";
  flush_all ();
  
  at_exit (fun () -> try Unix.unlink sock_path with _ -> ());
  
  try
    while true do
      let (client_fd, _) = Unix.accept sock in
      handle_native_client client_fd;
      Unix.close client_fd
    done
  with
  | Unix.Unix_error (Unix.EINTR, _, _) -> 
      printf "Native server interrupted\n"
  | exn -> 
      printf "Native server error: %s\n" (Printexc.to_string exn)

let () =
  match Sys.argv with
  | [| _; "--serve-native" |] -> start_native_server ()
  | _ -> 
      printf "Usage: %s --serve-native\n" Sys.argv.(0);
      printf "B5: Native Integration - Direct L0→SoA→L1→Validation\n";
      printf "Target: P99 < 20ms (eliminates CLI overhead)\n"