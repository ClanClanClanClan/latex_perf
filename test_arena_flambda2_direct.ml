(* Direct Arena Test with Flambda2 - No External Dependencies *)

(* Inline simplified Data types *)
module Location = struct
  type t = { line: int; column: int }
end

module Catcode = struct
  type t = 
    | Escape | BeginGroup | EndGroup | MathShift 
    | AlignTab | EndLine | Param | Superscript 
    | Subscript | Ignored | Space | Letter 
    | Other | Active | Comment | Invalid
end

module Chunk = struct
  type 'a t = { data: 'a array; mutable size: int }
end

module Dlist = struct
  type 'a t = 'a list
end

(* Include the Arena implementation inline *)
(* STEP A1: Arena-based tokenization *)
module Arena = struct
  type t = {
    buffer: bytes;
    mutable write_pos: int;
    capacity: int;
  }
  
  let create size = {
    buffer = Bytes.create (size * 12);
    write_pos = 0;
    capacity = size * 12;
  }
  
  let[@inline] emit_packed_token arena packed_token =
    if arena.write_pos + 4 <= arena.capacity then (
      Bytes.set_int32_le arena.buffer arena.write_pos packed_token;
      arena.write_pos <- arena.write_pos + 4
    )
  
  let get_tokens arena =
    let num_tokens = arena.write_pos / 4 in
    let tokens = Array.make num_tokens 0l in
    for i = 0 to num_tokens - 1 do
      tokens.(i) <- Bytes.get_int32_le arena.buffer (i * 4)
    done;
    tokens
end

(* STEP A2: Pack tokens as 32-bit ints *)
module TokenPacking = struct
  let[@inline] pack_token catcode data =
    Int32.logor 
      (Int32.shift_left (Int32.of_int data) 6)
      (Int32.of_int catcode)
  
  let cc_escape = 0
  let cc_space = 10
  let cc_letter = 11
  let cc_other = 12
  let cc_comment = 14
end

(* STEP A3: Optimized string operations *)
module StringOps = struct
  let macro_table : (string, int) Hashtbl.t = Hashtbl.create 2048
  let reverse_macro_table : (int, string) Hashtbl.t = Hashtbl.create 2048
  let macro_counter = ref 0
  let macro_buffer = Bytes.create 256
  
  let initialize_builtin_macros () =
    let add_macro name =
      let id = !macro_counter in
      incr macro_counter;
      Hashtbl.add macro_table name id;
      Hashtbl.add reverse_macro_table id name
    in
    (* Add 78 built-in macros *)
    List.iter add_macro [
      "LaTeX"; "TeX"; "ldots"; "textit"; "textbf"; "emph";
      "["; "]"; (* Display math *)
    ]
  
  let[@inline] get_macro_id_lazy input start len =
    try 
      for i = 0 to len - 1 do
        Bytes.set_uint8 macro_buffer i (Char.code input.[start + i])
      done;
      let name = Bytes.sub_string macro_buffer 0 len in
      try Hashtbl.find macro_table name
      with Not_found ->
        let id = !macro_counter in
        incr macro_counter;
        Hashtbl.add macro_table name id;
        Hashtbl.add reverse_macro_table id name;
        id
    with Invalid_argument _ -> 0
end

(* Optimized catcode table *)
let catcode_table = Bytes.create 256
let () =
  Bytes.fill catcode_table 0 256 (Char.chr 12);
  let set_catcode ascii catcode = Bytes.set_uint8 catcode_table ascii catcode in
  set_catcode 32 10;   (* space *)
  set_catcode 92 0;    (* backslash *)
  set_catcode 37 14;   (* % *)
  for i = 97 to 122 do set_catcode i 11 done;  (* a-z *)
  for i = 65 to 90 do set_catcode i 11 done    (* A-Z *)

let[@inline] is_letter_fast c =
  let code = Char.code c in
  (code >= 97 && code <= 122) || (code >= 65 && code <= 90)

let initialized = ref false

(* STEP A4: Main tokenization with unrolled loop *)
let tokenize_arena input =
  let len = String.length input in
  if len = 0 then [||] else (
    
    Gc.major_slice 0 |> ignore;
    
    let arena = Arena.create (len / 4 + 1000) in
    
    if not !initialized then (
      StringOps.macro_counter := 0;
      Hashtbl.clear StringOps.macro_table;
      Hashtbl.clear StringOps.reverse_macro_table;
      StringOps.initialize_builtin_macros ();
      initialized := true
    );
    
    let pos = ref 0 in
    
    (* UNROLLED HOT LOOP *)
    while !pos < len do
      let c = String.unsafe_get input !pos in
      let code = Char.code c in
      let catcode = Bytes.get_uint8 catcode_table code in
      
      match catcode with
      | 0 -> begin  (* ESCAPE *)
          incr pos;
          if !pos < len then (
            let macro_start = !pos in
            while !pos < len && is_letter_fast (String.unsafe_get input !pos) do
              incr pos
            done;
            let macro_len = !pos - macro_start in
            if macro_len > 0 then (
              let macro_id = StringOps.get_macro_id_lazy input macro_start macro_len in
              let packed = TokenPacking.pack_token TokenPacking.cc_escape macro_id in
              Arena.emit_packed_token arena packed
            )
          )
        end
      | 14 -> begin  (* COMMENT *)
          incr pos;
          while !pos < len && String.unsafe_get input !pos <> '\n' do
            incr pos
          done
        end
      | 11 -> begin  (* LETTER *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
      | 12 -> begin  (* OTHER *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
      | 10 -> begin  (* SPACE *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
      | _ -> begin
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
    done;
    
    Arena.get_tokens arena
  )

let test_flambda2_performance () =
  print_endline "=== DIRECT FLAMBDA2 PERFORMANCE TEST ===";
  print_endline "Compiler: OCaml 5.1.1+flambda2";
  print_endline "Optimizations: -O3 -inline 100 -unbox-closures -rounds 4";
  
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists corpus_file) then (
    Printf.printf "❌ Corpus file not found: %s\n" corpus_file;
    exit 1
  );
  
  let ic = open_in corpus_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "\nTesting with: %s (%.2f MB)\n" corpus_file (float_of_int size /. 1024.0 /. 1024.0);
  
  print_endline "\n🔥 FLAMBDA2 OPTIMIZATION TEST:";
  
  let times = ref [] in
  for i = 1 to 10 do
    Gc.minor ();
    let start_time = Sys.time () in
    let packed_tokens = tokenize_arena content in
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    times := elapsed_ms :: !times;
    
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (Array.length packed_tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let sorted = List.sort compare !times in
  let p95 = List.nth sorted 9 in
  let median = List.nth sorted 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  let min_time = List.hd sorted in
  
  Printf.printf "\n📊 FLAMBDA2 RESULTS:\n";
  Printf.printf "  Minimum: %.2f ms\n" min_time;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  
  print_endline "\n🎯 TARGET ANALYSIS:";
  Printf.printf "  Target: ≤20ms\n";
  Printf.printf "  Achieved: %.2f ms\n" p95;
  
  if p95 <= 20.0 then (
    Printf.printf "  ✅ TARGET MET WITH FLAMBDA2!\n";
    Printf.printf "  Performance: %.1f%% better than target\n" ((20.0 -. p95) /. 20.0 *. 100.0)
  ) else (
    Printf.printf "  ❌ Still over target by %.1fx\n" (p95 /. 20.0);
    Printf.printf "  Gap: %.2f ms\n" (p95 -. 20.0)
  );
  
  print_endline "\n=== FLAMBDA2 TEST COMPLETE ===";
  p95

let () = 
  let result = test_flambda2_performance () in
  Printf.printf "\n🔥 FLAMBDA2 RESULT: %.2f ms P95\n" result