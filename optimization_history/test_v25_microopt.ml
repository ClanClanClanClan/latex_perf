(* test_v25_microopt.ml - Phase 4: Hot-loop micro-optimizations *)

open Printf

(* Include arena implementation with micro-optimizations *)
module Arena = struct
  type t = {
    mutable arr: int64 array;
    mutable len: int;
    mutable capacity: int;
  }

  let create capacity =
    {
      arr = Array.make capacity 0L;
      len = 0;
      capacity;
    }

  (* Hot path - completely inlined push with no bounds checking *)
  let[@inline always] push_unsafe arena value =
    Array.unsafe_set arena.arr arena.len value;
    arena.len <- arena.len + 1

  let length arena = arena.len

  let[@inline] get_raw arena index =
    Array.unsafe_get arena.arr index
end

(* Micro-optimized token packing *)
module TokenPacking = struct
  (* Pre-computed tag shifts for branchless operations *)
  let tag_shift_0 = 0L  (* TChar *)
  let tag_shift_1 = 268435456L  (* TMacro = 1L << 28 *)
  let tag_shift_2 = 536870912L  (* TParam = 2L << 28 *)
  let tag_shift_3 = 805306368L  (* TGroupOpen = 3L << 28 *)
  let tag_shift_4 = 1073741824L (* TGroupClose = 4L << 28 *)
  let tag_shift_5 = 1342177280L (* TEOF = 5L << 28 *)

  let[@inline always] pack_char uchar_code catcode_val =
    let base = Int64.of_int uchar_code in
    let catcode_bits = Int64.shift_left (Int64.of_int catcode_val) 24 in
    Int64.logor base catcode_bits

  let[@inline always] pack_macro name_hash =
    Int64.logor (Int64.of_int (name_hash land 0xFFFFFF)) tag_shift_1

  let[@inline always] pack_param param_num =
    Int64.logor (Int64.of_int param_num) tag_shift_2

  let[@inline always] pack_group_open () = tag_shift_3
  let[@inline always] pack_group_close () = tag_shift_4
  let[@inline always] pack_eof () = tag_shift_5
end

(* Micro-optimized string interning *)
module StringTable = struct
  type t = {
    mutable table: (string, int) Hashtbl.t;
    mutable names: string array;
    mutable count: int;
  }

  let create capacity = {
    table = Hashtbl.create capacity;
    names = Array.make capacity "";
    count = 0;
  }

  let[@inline always] intern_unsafe st name =
    try
      Hashtbl.find st.table name
    with Not_found ->
      let id = st.count in
      Hashtbl.add st.table name id;
      Array.unsafe_set st.names id name;
      st.count <- st.count + 1;
      id
end

(* Ultra-optimized lexer - Phase 4 implementation *)
module V25_lexer_microopt = struct
  let tokenize content =
    let len = String.length content in
    let bytes = Bytes.unsafe_of_string content in
    
    (* Pre-allocate with exact capacity to avoid reallocation *)
    let estimated_tokens = len + (len / 8) in
    let arena = Arena.create estimated_tokens in
    let strings = StringTable.create 8000 in
    
    (* Micro-optimized catcode table with branchless lookups *)
    let ascii_catcodes = Array.make 128 12 in (* Default: Other = 12 *)
    let () =
      ascii_catcodes.(0) <- 9;   ascii_catcodes.(9) <- 10;  ascii_catcodes.(32) <- 10;
      ascii_catcodes.(10) <- 5;  ascii_catcodes.(13) <- 5;  ascii_catcodes.(35) <- 6;
      ascii_catcodes.(36) <- 3;  ascii_catcodes.(37) <- 14; ascii_catcodes.(38) <- 4;
      ascii_catcodes.(92) <- 0;  ascii_catcodes.(94) <- 7;  ascii_catcodes.(95) <- 8;
      ascii_catcodes.(123) <- 1; ascii_catcodes.(125) <- 2; ascii_catcodes.(126) <- 13;
      (* Unroll letter assignment for better cache performance *)
      ascii_catcodes.(65) <- 11; ascii_catcodes.(66) <- 11; ascii_catcodes.(67) <- 11; ascii_catcodes.(68) <- 11;
      ascii_catcodes.(69) <- 11; ascii_catcodes.(70) <- 11; ascii_catcodes.(71) <- 11; ascii_catcodes.(72) <- 11;
      ascii_catcodes.(73) <- 11; ascii_catcodes.(74) <- 11; ascii_catcodes.(75) <- 11; ascii_catcodes.(76) <- 11;
      ascii_catcodes.(77) <- 11; ascii_catcodes.(78) <- 11; ascii_catcodes.(79) <- 11; ascii_catcodes.(80) <- 11;
      ascii_catcodes.(81) <- 11; ascii_catcodes.(82) <- 11; ascii_catcodes.(83) <- 11; ascii_catcodes.(84) <- 11;
      ascii_catcodes.(85) <- 11; ascii_catcodes.(86) <- 11; ascii_catcodes.(87) <- 11; ascii_catcodes.(88) <- 11;
      ascii_catcodes.(89) <- 11; ascii_catcodes.(90) <- 11;
      ascii_catcodes.(97) <- 11; ascii_catcodes.(98) <- 11; ascii_catcodes.(99) <- 11; ascii_catcodes.(100) <- 11;
      ascii_catcodes.(101) <- 11; ascii_catcodes.(102) <- 11; ascii_catcodes.(103) <- 11; ascii_catcodes.(104) <- 11;
      ascii_catcodes.(105) <- 11; ascii_catcodes.(106) <- 11; ascii_catcodes.(107) <- 11; ascii_catcodes.(108) <- 11;
      ascii_catcodes.(109) <- 11; ascii_catcodes.(110) <- 11; ascii_catcodes.(111) <- 11; ascii_catcodes.(112) <- 11;
      ascii_catcodes.(113) <- 11; ascii_catcodes.(114) <- 11; ascii_catcodes.(115) <- 11; ascii_catcodes.(116) <- 11;
      ascii_catcodes.(117) <- 11; ascii_catcodes.(118) <- 11; ascii_catcodes.(119) <- 11; ascii_catcodes.(120) <- 11;
      ascii_catcodes.(121) <- 11; ascii_catcodes.(122) <- 11;
    in
    
    (* Ultra-fast catcode lookup - no bounds checking *)
    let[@inline always] get_catcode_ultra_fast c =
      Array.unsafe_get ascii_catcodes (Char.code c)
    in
    
    (* Micro-optimized token pushing *)
    let[@inline always] push_char_micro uchar_code catcode_val =
      let packed = TokenPacking.pack_char uchar_code catcode_val in
      Arena.push_unsafe arena packed
    in
    
    let[@inline always] push_macro_micro name =
      let name_id = StringTable.intern_unsafe strings name in
      let packed = TokenPacking.pack_macro name_id in
      Arena.push_unsafe arena packed
    in
    
    let[@inline always] push_param_micro param_num =
      let packed = TokenPacking.pack_param param_num in
      Arena.push_unsafe arena packed
    in
    
    let[@inline always] push_group_open_micro () =
      Arena.push_unsafe arena (TokenPacking.pack_group_open ())
    in
    
    let[@inline always] push_group_close_micro () =
      Arena.push_unsafe arena (TokenPacking.pack_group_close ())
    in
    
    (* Micro-optimized control sequence reader with manual loop unrolling *)
    let read_control_sequence_micro pos =
      let start = !pos in
      incr pos; (* skip \ *)
      
      if !pos >= len then ("", !pos) else
      
      let c = Bytes.unsafe_get bytes !pos in
      if get_catcode_ultra_fast c = 11 then begin (* Letter *)
        incr pos;
        (* Manual loop unrolling for common short commands *)
        if !pos < len && get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 11 then begin
          incr pos;
          if !pos < len && get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 11 then begin
            incr pos;
            if !pos < len && get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 11 then begin
              incr pos;
              (* Continue with normal loop for longer commands *)
              while !pos < len && 
                    get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 11 do
                incr pos
              done
            end
          end
        end;
        (* Skip spaces with manual unrolling *)
        if !pos < len && get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 10 then begin
          incr pos;
          while !pos < len && 
                get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 10 do
            incr pos
          done
        end;
        let name_len = !pos - start - 1 in
        if name_len > 0 then
          (Bytes.sub_string bytes (start + 1) name_len, !pos)
        else ("", !pos)
      end else begin
        incr pos;
        (String.make 1 c, !pos)
      end
    in
    
    (* Main tokenization loop with aggressive micro-optimizations *)
    let pos = ref 0 in
    
    (* Use computed goto pattern with explicit state tracking *)
    while !pos < len do
      let c = Bytes.unsafe_get bytes !pos in
      let cc = get_catcode_ultra_fast c in
      
      (* Hot-path optimizations with manual branch prediction hints *)
      if cc = 12 then begin (* Other - most common case *)
        push_char_micro (Char.code c) cc;
        incr pos
      end else if cc = 11 then begin (* Letter - second most common *)
        push_char_micro (Char.code c) cc;
        incr pos
      end else if cc = 10 then begin (* Space - common *)
        (* Skip consecutive spaces with unrolled loop *)
        incr pos;
        if !pos < len && get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 10 then begin
          incr pos;
          while !pos < len && 
                get_catcode_ultra_fast (Bytes.unsafe_get bytes !pos) = 10 do
            incr pos
          done
        end;
        push_char_micro 32 10 (* single space char *)
      end else if cc = 0 then begin (* Escape - less common but hot *)
        let (name, new_pos) = read_control_sequence_micro pos in
        pos := new_pos;
        push_macro_micro name
      end else if cc = 14 then begin (* Comment *)
        (* Fast comment skipping with manual loop unrolling *)
        incr pos;
        if !pos < len then begin
          let c1 = Bytes.unsafe_get bytes !pos in
          if c1 <> '\n' then begin
            incr pos;
            if !pos < len then begin
              let c2 = Bytes.unsafe_get bytes !pos in
              if c2 <> '\n' then begin
                incr pos;
                while !pos < len && Bytes.unsafe_get bytes !pos <> '\n' do
                  incr pos
                done
              end
            end
          end
        end
      end else if cc = 1 then begin (* BeginGroup *)
        incr pos;
        push_group_open_micro ()
      end else if cc = 2 then begin (* EndGroup *)
        incr pos;
        push_group_close_micro ()
      end else if cc = 6 then begin (* Param *)
        incr pos;
        if !pos < len then
          let c2 = Bytes.unsafe_get bytes !pos in
          if c2 >= '1' && c2 <= '9' then begin
            incr pos;
            push_param_micro (Char.code c2 - 48) (* 48 = Char.code '0' *)
          end else
            push_char_micro (Char.code c) cc
        else
          push_char_micro (Char.code c) cc
      end else if cc = 5 then begin (* Endline *)
        incr pos;
        if !pos < len && Bytes.unsafe_get bytes !pos = '\n' then begin
          incr pos;
          push_macro_micro "par"
        end else
          push_char_micro 32 10 (* newline becomes space *)
      end else begin
        (* All other catcodes *)
        push_char_micro (Char.code c) cc;
        incr pos
      end
    done;
    
    Arena.push_unsafe arena (TokenPacking.pack_eof ());
    (arena, strings)
end

(* Simple materialization for testing *)
let materialize_token packed_value strings =
  let tag = Int64.to_int (Int64.shift_right (Int64.logand packed_value 0x70000000L) 28) in
  match tag with
  | 0 -> (* TChar *) "CHAR"
  | 1 -> (* TMacro *) "MACRO" 
  | 2 -> (* TParam *) "PARAM"
  | 3 -> "GROUP_OPEN"
  | 4 -> "GROUP_CLOSE"
  | 5 -> "EOF"
  | _ -> "INVALID"

(* ===== MAIN TEST ===== *)
let () =
  printf "⚡ MICRO-OPTIMIZED V25 TEST (PHASE 4)\n";
  printf "====================================\n";
  
  let content = 
    try
      let ic = open_in "corpora/perf/perf_smoke_big.tex" in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      printf "✅ Loaded corpus: %d bytes\n" n;
      s
    with _ ->
      printf "❌ Using synthetic test\n";
      String.concat "\n" [
        "% Test document";
        "\\documentclass[12pt]{article}";
        "\\begin{document}";
        "Hello world! This is a test.";
        "$x^2 + y^2 = z^2$";
        "\\end{document}"
      ]
  in
  
  (* Phase 4 Micro-optimized test *)
  printf "\n--- MICRO-OPTIMIZED LEXER (PHASE 4) ---\n";
  for _ = 1 to 3 do
    let _ = V25_lexer_microopt.tokenize content in
    Gc.full_major ()
  done;
  
  let micro_times = ref [] in
  let micro_count = ref 0 in
  
  for i = 1 to 15 do
    Gc.full_major ();
    let start = Sys.time () in
    let (arena, strings) = V25_lexer_microopt.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    micro_times := elapsed :: !micro_times;
    if i = 1 then micro_count := Arena.length arena
  done;
  
  let micro_sorted = List.sort compare !micro_times in
  let micro_median = List.nth micro_sorted 7 in
  printf "Tokens: %d\n" !micro_count;
  printf "Median: %.2f ms\n" micro_median;
  
  (* Compare with Phase 2 baseline *)
  let phase2_baseline = 31.58 in
  let speedup = phase2_baseline /. micro_median in
  
  printf "\n--- PHASE 4 RESULTS ---\n";
  printf "Micro vs Expected 944K: %s (%d tokens)\n"
    (if abs (!micro_count - 944614) < 1000 then "✅ CLOSE" else "❌ DIFFERENT") !micro_count;
  printf "Phase 2 → Phase 4: %.2fx %s (%.2fms → %.2fms)\n"
    speedup (if speedup > 1.0 then "faster" else "slower") phase2_baseline micro_median;
  
  printf "\nPhase 4 Targets:\n";
  printf "≤25ms (Phase 4): %s (%.2fms)\n"
    (if micro_median <= 25.0 then "✅ PASS" else "❌ FAIL") micro_median;
  printf "≤20ms (Final): %s (%.2fms)\n"
    (if micro_median <= 20.0 then "✅ PASS" else "❌ FAIL") micro_median;
  
  printf "\n⚡ MICRO-OPTIMIZATION PHASE 4 COMPLETE\n"