(* L0 Lexer Track A - ULTRA-OPTIMIZED IMPLEMENTATION V3 *)
(* Target: 32ms -> 20ms (37.5% improvement) via hotpath optimizations *)

open Data

(* OPTIMIZATION O1: Eliminate string allocations in macro lookup *)
module UltraStringOps = struct
  (* Pre-allocated arrays for common single-char macros *)
  let single_char_macro_ids = Array.make 256 (-1)
  let macro_table : (string, int) Hashtbl.t = Hashtbl.create 2048
  let reverse_macro_table : (int, string) Hashtbl.t = Hashtbl.create 2048
  let macro_counter = ref 0
  
  (* CRITICAL: Pre-register single character macros for O(1) lookup *)
  let register_single_char_macro char =
    let code = Char.code char in
    if single_char_macro_ids.(code) = -1 then (
      let id = !macro_counter in
      incr macro_counter;
      single_char_macro_ids.(code) <- id;
      let name = String.make 1 char in
      Hashtbl.add reverse_macro_table id name
    );
    single_char_macro_ids.(code)
  
  (* Initialize built-in macros with pre-computed single-char ones *)
  let initialize_builtin_macros () =
    let add_macro name =
      let id = !macro_counter in
      incr macro_counter;
      Hashtbl.add macro_table name id;
      Hashtbl.add reverse_macro_table id name
    in
    
    (* Pre-register common single-char macros *)
    ignore (register_single_char_macro '[');  (* \[ *)
    ignore (register_single_char_macro ']');  (* \] *)
    ignore (register_single_char_macro '\\'); (* \\ *)
    ignore (register_single_char_macro '{');  (* \{ *)
    ignore (register_single_char_macro '}');  (* \} *)
    ignore (register_single_char_macro '$');  (* \$ *)
    ignore (register_single_char_macro '&');  (* \& *)
    ignore (register_single_char_macro '%');  (* \% *)
    ignore (register_single_char_macro '#');  (* \# *)
    ignore (register_single_char_macro '_');  (* \_ *)
    ignore (register_single_char_macro '^');  (* \^ *)
    ignore (register_single_char_macro '~');  (* \~ *)
    ignore (register_single_char_macro ' ');  (* \  (space) *)
    
    (* Standard macros (same as before) *)
    add_macro "LaTeX"; add_macro "TeX"; add_macro "ldots";
    add_macro "textit"; add_macro "textbf"; add_macro "emph";
    add_macro "underline"; add_macro "texttt"; add_macro "textsf";
    add_macro "textsc"; add_macro "today"; add_macro "copyright";
    
    (* Greek lowercase *)
    add_macro "alpha"; add_macro "beta"; add_macro "gamma"; add_macro "delta";
    add_macro "epsilon"; add_macro "zeta"; add_macro "eta"; add_macro "theta";
    add_macro "iota"; add_macro "kappa"; add_macro "lambda"; add_macro "mu";
    add_macro "nu"; add_macro "xi"; add_macro "omicron"; add_macro "pi";
    add_macro "rho"; add_macro "sigma"; add_macro "tau"; add_macro "upsilon";
    add_macro "phi"; add_macro "chi"; add_macro "psi"; add_macro "omega";
    
    (* Greek uppercase *)
    add_macro "Alpha"; add_macro "Beta"; add_macro "Gamma"; add_macro "Delta";
    add_macro "Epsilon"; add_macro "Zeta"; add_macro "Eta"; add_macro "Theta";
    add_macro "Iota"; add_macro "Kappa"; add_macro "Lambda"; add_macro "Mu";
    add_macro "Nu"; add_macro "Xi"; add_macro "Omicron"; add_macro "Pi";
    add_macro "Rho"; add_macro "Sigma"; add_macro "Tau"; add_macro "Upsilon";
    add_macro "Phi"; add_macro "Chi"; add_macro "Psi"; add_macro "Omega";
    
    (* Math symbols *)
    add_macro "sum"; add_macro "int"; add_macro "prod"; add_macro "lim";
    add_macro "sin"; add_macro "cos"; add_macro "tan"; add_macro "log";
    add_macro "ln"; add_macro "exp"; add_macro "sqrt"; add_macro "frac";
    add_macro "infty"; add_macro "partial"; add_macro "nabla"; add_macro "pm";
    add_macro "mp"; add_macro "times"; add_macro "div"; add_macro "cdot"
  
  (* OPTIMIZATION O2: Zero-allocation macro lookup *)
  let[@inline] get_single_char_macro_id char_code =
    single_char_macro_ids.(char_code)
  
  (* Fast multi-char macro lookup with minimal allocation *)
  let get_macro_id_optimized input start len =
    if len = 1 then
      (* Single char - use pre-computed table *)
      let char_code = Char.code (String.unsafe_get input start) in
      let id = single_char_macro_ids.(char_code) in
      if id >= 0 then id else register_single_char_macro (Char.chr char_code)
    else
      (* Multi-char - need to create string (unavoidable for hashtable) *)
      let name = String.sub input start len in
      try Hashtbl.find macro_table name
      with Not_found ->
        let id = !macro_counter in
        incr macro_counter;
        Hashtbl.add macro_table name id;
        Hashtbl.add reverse_macro_table id name;
        id
  
  let get_macro_name_by_id id =
    try Hashtbl.find reverse_macro_table id
    with Not_found -> "unknown"
end

(* OPTIMIZATION O3: Ultra-fast arena with better memory layout *)
module UltraArena = struct
  type t = {
    buffer: bytes;
    mutable write_pos: int;
    capacity: int;
  }
  
  let create size = {
    buffer = Bytes.create (size * 4);  (* Exactly 4 bytes per token *)
    write_pos = 0;
    capacity = size * 4;
  }
  
  let[@inline] emit_packed_token arena packed_token =
    if arena.write_pos < arena.capacity - 4 then (
      Bytes.set_int32_le arena.buffer arena.write_pos packed_token;
      arena.write_pos <- arena.write_pos + 4
    )
  
  (* OPTIMIZATION O4: Direct array creation without intermediate operations *)
  let get_tokens arena =
    let num_tokens = arena.write_pos / 4 in
    let tokens = Array.make num_tokens 0l in
    for i = 0 to num_tokens - 1 do
      tokens.(i) <- Bytes.get_int32_le arena.buffer (i * 4)
    done;
    tokens
end

(* Token packing (same as before, already optimized) *)
module TokenPacking = struct
  let[@inline] pack_token catcode data =
    Int32.logor 
      (Int32.shift_left (Int32.of_int data) 6)
      (Int32.of_int catcode)
  
  let[@inline] unpack_catcode packed =
    Int32.to_int (Int32.logand packed 0x3Fl)
  
  let[@inline] unpack_data packed =
    Int32.to_int (Int32.shift_right_logical packed 6)
  
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

(* OPTIMIZATION O5: Branchless catcode table *)
let catcode_table = Bytes.create 256

let build_catcode_table () =
  let set_catcode ascii_code catcode = 
    Bytes.set_uint8 catcode_table ascii_code catcode 
  in
  
  (* Fill with 'other' by default *)
  for i = 0 to 255 do set_catcode i 12 done;
  
  (* Special characters *)
  set_catcode 92 0;   (* \ escape *)
  set_catcode 123 1;  (* { begin group *)
  set_catcode 125 2;  (* } end group *)
  set_catcode 36 3;   (* $ math shift *)
  set_catcode 38 4;   (* & align tab *)
  set_catcode 13 5;   (* CR end line *)
  set_catcode 10 5;   (* LF end line *)
  set_catcode 35 6;   (* # param *)
  set_catcode 94 7;   (* ^ superscript *)
  set_catcode 95 8;   (* _ subscript *)
  set_catcode 0 9;    (* null ignored *)
  set_catcode 32 10;  (* space *)
  set_catcode 9 10;   (* tab as space *)
  set_catcode 37 14;  (* % comment *)
  
  (* Letters - most common, put last to avoid branch misprediction *)
  for i = 97 to 122 do set_catcode i 11 done;  (* a-z *)
  for i = 65 to 90 do set_catcode i 11 done    (* A-Z *)

(* OPTIMIZATION O6: Fixed letter test - correct and fast *)
let[@inline] is_letter_ultra_fast c =
  let code = Char.code c in
  (* Correct letter test: A-Z (65-90) or a-z (97-122) *)
  (code >= 65 && code <= 90) || (code >= 97 && code <= 122)

let initialized = ref false

(* MAIN OPTIMIZATION: Ultra-hot tokenization loop *)
let tokenize_ultra input =
  let len = String.length input in
  if len = 0 then [||] else (
    
    (* One-time initialization *)
    if not !initialized then (
      build_catcode_table ();
      UltraStringOps.initialize_builtin_macros ();
      initialized := true
    );
    
    let arena = UltraArena.create (len / 4 + 1000) in
    let pos = ref 0 in
    
    (* OPTIMIZATION O7: Unroll most common cases first *)
    while !pos < len do
      let c = String.unsafe_get input !pos in
      let code = Char.code c in
      let catcode = Bytes.get_uint8 catcode_table code in
      
      match catcode with
      (* HOTTEST PATH: Letters (most common) *)
      | 11 -> 
          let packed = TokenPacking.pack_token catcode code in
          UltraArena.emit_packed_token arena packed;
          incr pos
      
      (* SECOND HOTTEST: Other characters *)
      | 12 -> 
          let packed = TokenPacking.pack_token catcode code in
          UltraArena.emit_packed_token arena packed;
          incr pos
      
      (* THIRD: Space *)
      | 10 -> 
          let packed = TokenPacking.pack_token catcode code in
          UltraArena.emit_packed_token arena packed;
          incr pos
      
      (* ESCAPE - optimized macro parsing *)
      | 0 -> 
          incr pos;
          if !pos < len then (
            let macro_start = !pos in
            (* Fast letter scanning *)
            while !pos < len && is_letter_ultra_fast (String.unsafe_get input !pos) do
              incr pos
            done;
            let macro_len = !pos - macro_start in
            if macro_len > 0 then (
              (* Multi-char macro *)
              let macro_id = UltraStringOps.get_macro_id_optimized input macro_start macro_len in
              let packed = TokenPacking.pack_token TokenPacking.cc_escape macro_id in
              UltraArena.emit_packed_token arena packed
            ) else if !pos < len then (
              (* Single-char command - OPTIMIZED *)
              let sc_code = Char.code (String.unsafe_get input !pos) in
              let macro_id = UltraStringOps.get_single_char_macro_id sc_code in
              let final_id = if macro_id >= 0 then macro_id 
                           else UltraStringOps.register_single_char_macro (Char.chr sc_code) in
              let packed = TokenPacking.pack_token TokenPacking.cc_escape final_id in
              UltraArena.emit_packed_token arena packed;
              incr pos
            )
          )
      
      (* COMMENT - optimized line skipping *)
      | 14 -> 
          incr pos;
          (* Optimize comment skipping *)
          while !pos < len && String.unsafe_get input !pos <> '\n' do
            incr pos
          done
      
      (* All other catcodes - less common *)
      | _ -> 
          let packed = TokenPacking.pack_token catcode code in
          UltraArena.emit_packed_token arena packed;
          incr pos
    done;
    
    UltraArena.get_tokens arena
  )

(* Convert packed tokens to Lexer_v25 format *)
let convert_packed_tokens packed_tokens =
  Array.to_list (Array.map (fun packed ->
    let catcode = TokenPacking.unpack_catcode packed in
    let data = TokenPacking.unpack_data packed in
    
    match catcode with
    | c when c = TokenPacking.cc_escape ->
        let name = UltraStringOps.get_macro_name_by_id data in
        Lexer_v25.TMacro name
    | c when c = TokenPacking.cc_begin_group -> Lexer_v25.TGroupOpen
    | c when c = TokenPacking.cc_end_group -> Lexer_v25.TGroupClose  
    | c when c = TokenPacking.cc_param -> Lexer_v25.TParam 1
    | _ -> 
        let ascii = data land 0xFF in
        let catcode_val = match catcode with
          | c when c = TokenPacking.cc_escape -> Catcode.Escape
          | c when c = TokenPacking.cc_begin_group -> Catcode.BeginGroup
          | c when c = TokenPacking.cc_end_group -> Catcode.EndGroup
          | c when c = TokenPacking.cc_math_shift -> Catcode.MathShift
          | c when c = TokenPacking.cc_align_tab -> Catcode.AlignTab
          | c when c = TokenPacking.cc_end_line -> Catcode.EndLine
          | c when c = TokenPacking.cc_param -> Catcode.Param
          | c when c = TokenPacking.cc_superscript -> Catcode.Superscript
          | c when c = TokenPacking.cc_subscript -> Catcode.Subscript
          | c when c = TokenPacking.cc_ignored -> Catcode.Ignored
          | c when c = TokenPacking.cc_space -> Catcode.Space
          | c when c = TokenPacking.cc_letter -> Catcode.Letter
          | c when c = TokenPacking.cc_other -> Catcode.Other
          | c when c = TokenPacking.cc_active -> Catcode.Active
          | c when c = TokenPacking.cc_comment -> Catcode.Comment
          | _ -> Catcode.Invalid
        in
        Lexer_v25.TChar (Uchar.of_int ascii, catcode_val)
  ) packed_tokens)

(* ULTRA-FAST: Primary interface *)
let tokenize input = tokenize_ultra input

(* Legacy compatibility *)
let tokenize_legacy input =
  let packed = tokenize_ultra input in
  convert_packed_tokens packed

(* Utilities for working with packed tokens *)
module PackedToken = struct
  type t = int32
  
  let get_catcode = TokenPacking.unpack_catcode
  let get_data = TokenPacking.unpack_data
  
  let is_macro token =
    let catcode = get_catcode token in
    catcode = TokenPacking.cc_escape
    
  let get_macro_name token =
    if is_macro token then
      let macro_id = get_data token in
      UltraStringOps.get_macro_name_by_id macro_id
    else
      failwith "Not a macro token"
      
  let is_char token =
    let catcode = get_catcode token in
    catcode <> TokenPacking.cc_escape &&
    catcode <> TokenPacking.cc_begin_group &&
    catcode <> TokenPacking.cc_end_group &&
    catcode <> TokenPacking.cc_param
    
  let get_char token =
    if is_char token then
      let ascii = (get_data token) land 0xFF in
      Char.chr ascii
    else
      failwith "Not a character token"
      
  let to_string token =
    if is_macro token then
      Printf.sprintf "TMacro(\"%s\")" (get_macro_name token)
    else if is_char token then
      Printf.sprintf "TChar('%c')" (get_char token)
    else
      let catcode = get_catcode token in
      if catcode = TokenPacking.cc_begin_group then "TGroupOpen"
      else if catcode = TokenPacking.cc_end_group then "TGroupClose"
      else if catcode = TokenPacking.cc_param then "TParam"
      else Printf.sprintf "Token(cc=%d)" catcode
end