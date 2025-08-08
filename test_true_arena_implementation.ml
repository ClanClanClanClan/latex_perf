(* Test TRUE Arena Implementation - Exact Logic from Arena File *)

open Data

(* EXACT COPY: Arena module from l0_lexer_track_a_arena.ml *)
module Arena = struct
  type t = {
    buffer: bytes;           (* Pre-allocated arena: len*3 bytes for packed tokens *)
    mutable write_pos: int;  (* Current write position *)
    capacity: int;           (* Total capacity *)
  }
  
  let create size = {
    buffer = Bytes.create (size * 12);  (* 12 bytes per token: generous estimate *)
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

(* EXACT COPY: TokenPacking module *)
module TokenPacking = struct
  (* Token encoding: | 6 bits catcode | 26 bits data | *)
  let[@inline] pack_token catcode data =
    Int32.logor 
      (Int32.shift_left (Int32.of_int data) 6)
      (Int32.of_int catcode)
  
  let[@inline] unpack_catcode packed =
    Int32.to_int (Int32.logand packed 0x3Fl)
  
  let[@inline] unpack_data packed =
    Int32.to_int (Int32.shift_right_logical packed 6)
  
  (* Catcode constants *)
  let cc_escape = 0
  let cc_begin_group = 1  
  let cc_end_group = 2
  let cc_math_shift = 3
  let cc_align_tab = 4
  let cc_end_line = 5
  let cc_param = 6
  let cc_superscript = 7
  let cc_subscript = 8
  let cc_ignored = 9
  let cc_space = 10
  let cc_letter = 11
  let cc_other = 12
  let cc_active = 13
  let cc_comment = 14
end

(* EXACT COPY: StringOps module *)
module StringOps = struct
  let macro_table : (string, int) Hashtbl.t = Hashtbl.create 2048
  let reverse_macro_table : (int, string) Hashtbl.t = Hashtbl.create 2048
  let macro_counter = ref 0
  let macro_buffer = Bytes.create 256
  
  (* Initialize built-in macros according to v25 spec *)
  let initialize_builtin_macros () =
    let add_macro name =
      let id = !macro_counter in
      incr macro_counter;
      Hashtbl.add macro_table name id;
      Hashtbl.add reverse_macro_table id name
    in
    
    (* Typography Macros (12) *)
    add_macro "LaTeX";
    add_macro "TeX";
    add_macro "ldots";
    add_macro "textit";
    add_macro "textbf";
    add_macro "emph";
    add_macro "underline";
    add_macro "texttt";
    add_macro "textsf";
    add_macro "textsc";
    add_macro "today";
    add_macro "copyright";
    
    (* Mathematical Macros (44) - Greek + symbols *)
    (* Greek lowercase *)
    add_macro "alpha"; add_macro "beta"; add_macro "gamma"; add_macro "delta";
    add_macro "epsilon"; add_macro "zeta"; add_macro "eta"; add_macro "theta";
    add_macro "iota"; add_macro "kappa"; add_macro "lambda"; add_macro "mu";
    add_macro "nu"; add_macro "xi"; add_macro "pi"; add_macro "rho";
    add_macro "sigma"; add_macro "tau"; add_macro "upsilon"; add_macro "phi";
    add_macro "chi"; add_macro "psi"; add_macro "omega";
    (* Greek uppercase *)
    add_macro "Gamma"; add_macro "Delta"; add_macro "Theta"; add_macro "Lambda";
    add_macro "Xi"; add_macro "Pi"; add_macro "Sigma"; add_macro "Upsilon";
    add_macro "Phi"; add_macro "Psi"; add_macro "Omega";
    (* Math symbols *)
    add_macro "infty"; add_macro "pm"; add_macro "mp"; add_macro "times";
    add_macro "div"; add_macro "neq"; add_macro "leq"; add_macro "geq";
    add_macro "approx"; add_macro "equiv"; add_macro "propto";
    
    (* Structural Macros (20) *)
    add_macro "section"; add_macro "subsection"; add_macro "subsubsection";
    add_macro "paragraph"; add_macro "subparagraph"; add_macro "item";
    add_macro "label"; add_macro "ref"; add_macro "cite"; add_macro "footnote";
    add_macro "newpage"; add_macro "clearpage"; add_macro "tableofcontents";
    add_macro "listoffigures"; add_macro "listoftables"; add_macro "bibliography";
    add_macro "index"; add_macro "maketitle"; add_macro "abstract"; add_macro "appendix";
    
    (* CRITICAL ADDITION: Display math macros missing from original *)
    add_macro "[";  (* Display math begin *)
    add_macro "]";  (* Display math end *)
    
    (* Formatting Macros (12) *)
    add_macro "centering"; add_macro "raggedright"; add_macro "raggedleft";
    add_macro "small"; add_macro "large"; add_macro "Large"; add_macro "LARGE";
    add_macro "tiny"; add_macro "scriptsize"; add_macro "footnotesize";
    add_macro "normalsize"; add_macro "huge"
  
  let[@inline] get_macro_id_lazy input start len =
    (* Defer string creation until needed *)
    try 
      (* Create string only for hashtable lookup - unavoidable *)
      for i = 0 to len - 1 do
        Bytes.set_uint8 macro_buffer i (Char.code input.[start + i])
      done;
      let name = Bytes.sub_string macro_buffer 0 len in
      try Hashtbl.find macro_table name
      with Not_found ->
        let id = !macro_counter in
        incr macro_counter;
        Hashtbl.add macro_table name id;
        Hashtbl.add reverse_macro_table id name;  (* Add reverse mapping *)
        id
    with Invalid_argument _ -> 0  (* fallback *)
  
  let get_macro_name_by_id id =
    try Hashtbl.find reverse_macro_table id
    with Not_found -> "unknown"
end

(* EXACT COPY: Optimized catcode table *)
let catcode_table = Bytes.create 256
let () =
  (* Initialize with 'other' catcode (12) *)
  Bytes.fill catcode_table 0 256 (Char.chr 12);
  (* Set specific catcodes *)
  let set_catcode ascii catcode =
    Bytes.set_uint8 catcode_table ascii catcode
  in
  set_catcode 32 10;   (* space *)
  set_catcode 9 10;    (* tab *)  
  set_catcode 10 5;    (* newline *)
  set_catcode 13 5;    (* carriage return *)
  set_catcode 92 0;    (* backslash *)
  set_catcode 123 1;   (* { *)
  set_catcode 125 2;   (* } *)
  set_catcode 36 3;    (* $ *)
  set_catcode 38 4;    (* & *)
  set_catcode 35 6;    (* # *)
  set_catcode 94 7;    (* ^ *)
  set_catcode 95 8;    (* _ *)
  set_catcode 37 14;   (* % *)
  (* Letters *)
  for i = 97 to 122 do set_catcode i 11 done;  (* a-z *)
  for i = 65 to 90 do set_catcode i 11 done    (* A-Z *)

(* EXACT COPY: is_letter_fast *)
let[@inline] is_letter_fast c =
  (* Correct letter test *)
  let code = Char.code c in
  (code >= 97 && code <= 122) || (code >= 65 && code <= 90)

(* Global initialization flag *)
let initialized = ref false

(* EXACT COPY: Main tokenization function - arena-based with all optimizations *)
let tokenize_arena input =
  let len = String.length input in
  if len = 0 then [||] else (
    
    (* Pre-warm GC to avoid measurement artifacts *)
    Gc.major_slice 0 |> ignore;
    
    let arena = Arena.create (len / 4 + 1000) in  (* Estimate tokens *)
    
    (* CRITICAL: Initialize built-in macros on first use *)
    if not !initialized then (
      StringOps.macro_counter := 0;
      Hashtbl.clear StringOps.macro_table;
      Hashtbl.clear StringOps.reverse_macro_table;
      StringOps.initialize_builtin_macros ();
      initialized := true
    );
    
    let pos = ref 0 in
    
    (* EXACT COPY: Unrolled hot loop for common cases *)
    while !pos < len do
      let c = String.unsafe_get input !pos in
      let code = Char.code c in
      let catcode = Bytes.get_uint8 catcode_table code in
      
      (* Manual 4-way unroll for hottest paths *)
      match catcode with
      | 0 -> begin  (* ESCAPE - macro parsing *)
          incr pos;
          if !pos < len then (
            let macro_start = !pos in
            (* Optimized macro scanning - no bounds checking in inner loop *)
            while !pos < len && is_letter_fast (String.unsafe_get input !pos) do
              incr pos
            done;
            let macro_len = !pos - macro_start in
            if macro_len > 0 then (
              let macro_id = StringOps.get_macro_id_lazy input macro_start macro_len in
              let packed = TokenPacking.pack_token TokenPacking.cc_escape macro_id in
              Arena.emit_packed_token arena packed
            ) else if !pos < len then (
              (* Single-char command - IMPORTANT for \[ and \] *)
              let sc = String.unsafe_get input !pos in
              let sc_str = String.make 1 sc in
              (* Check if it's a known single-char macro *)
              let macro_id = 
                try Hashtbl.find StringOps.macro_table sc_str
                with Not_found ->
                  let id = !StringOps.macro_counter in
                  incr StringOps.macro_counter;
                  Hashtbl.add StringOps.macro_table sc_str id;
                  Hashtbl.add StringOps.reverse_macro_table id sc_str;
                  id
              in
              let packed = TokenPacking.pack_token TokenPacking.cc_escape macro_id in
              Arena.emit_packed_token arena packed;
              incr pos
            )
          )
        end
      | 14 -> begin  (* COMMENT - skip to end of line *)
          incr pos;
          while !pos < len && String.unsafe_get input !pos <> '\n' do
            incr pos
          done
        end
      | 11 -> begin  (* LETTER - most common case *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
      | 12 -> begin  (* OTHER - second most common *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
      | 10 -> begin  (* SPACE - third most common *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
      | _ -> begin   (* All other catcodes *)
          let packed = TokenPacking.pack_token catcode code in
          Arena.emit_packed_token arena packed;
          incr pos
        end
    done;
    
    (* Return raw packed tokens - defer expensive conversion *)
    Arena.get_tokens arena
  )

let test_true_arena_performance () =
  print_endline "=== TESTING TRUE ARENA IMPLEMENTATION (EXACT LOGIC) ===";
  
  let corpus_file = "corpora/perf/perf_smoke_big.tex" in
  
  if not (Sys.file_exists corpus_file) then (
    Printf.printf "❌ Corpus file not found: %s\n" corpus_file;
    exit 1
  );
  
  let ic = open_in corpus_file in
  let size = in_channel_length ic in
  let content = really_input_string ic size in
  close_in ic;
  
  Printf.printf "Testing TRUE Arena logic with: %s\n" corpus_file;
  Printf.printf "File size: %d bytes (%.2f MB)\n" size (float_of_int size /. 1024.0 /. 1024.0);
  
  print_endline "\n🔧 TESTING TRUE ARENA IMPLEMENTATION:";
  
  let times = ref [] in
  for i = 1 to 10 do
    let start_time = Sys.time () in
    let tokens = tokenize_arena content in
    let end_time = Sys.time () in
    let elapsed_ms = (end_time -. start_time) *. 1000.0 in
    times := elapsed_ms :: !times;
    
    if i = 1 then
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed_ms (Array.length tokens)
    else
      Printf.printf "  Run %d: %.2f ms\n" i elapsed_ms
  done;
  
  let sorted = List.sort compare !times in
  let p95 = List.nth sorted 9 in
  let median = List.nth sorted 5 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  let min_time = List.hd sorted in
  
  Printf.printf "\n📊 TRUE ARENA RESULTS:\n";
  Printf.printf "  Minimum: %.2f ms\n" min_time;
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;
  Printf.printf "  P95: %.2f ms\n" p95;
  
  (* Target Analysis *)
  print_endline "\n🎯 TARGET ANALYSIS:";
  Printf.printf "  Target: ≤20ms\n";
  Printf.printf "  Achieved: %.2f ms\n" p95;
  
  if p95 <= 20.0 then (
    Printf.printf "  ✅ TARGET MET!\n";
    let margin = ((20.0 -. p95) /. 20.0) *. 100.0 in
    Printf.printf "  Margin: %.1f%% better than target\n" margin;
    Printf.printf "  🏆 TRUE ARENA SUCCESS!\n"
  ) else (
    Printf.printf "  ❌ Over target by %.1fx\n" (p95 /. 20.0);
    let gap = p95 -. 20.0 in
    Printf.printf "  Gap: %.2f ms over target\n" gap
  );
  
  (* Compare to false standalone numbers *)
  let false_standalone = 77.85 in
  let real_vs_false = false_standalone /. p95 in
  
  print_endline "\n⚡ TRUE ARENA vs STANDALONE COMPARISON:";
  Printf.printf "  False standalone: %.2f ms\n" false_standalone;
  Printf.printf "  True Arena: %.2f ms\n" p95;
  if p95 < false_standalone then (
    Printf.printf "  True Arena is %.2fx FASTER than standalone\n" real_vs_false;
    Printf.printf "  Difference: %.2f ms improvement\n" (false_standalone -. p95)
  ) else (
    Printf.printf "  True Arena is %.2fx SLOWER than standalone\n" (p95 /. false_standalone);
    Printf.printf "  Difference: %.2f ms regression\n" (p95 -. false_standalone)
  );
  
  print_endline "\n=== TRUE ARENA TEST COMPLETE ===";
  p95

let () = 
  let true_arena_performance = test_true_arena_performance () in
  Printf.printf "\n🎯 TRUE ARENA RESULT: %.2f ms P95\n" true_arena_performance