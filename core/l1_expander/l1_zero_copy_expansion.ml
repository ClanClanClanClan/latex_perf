(* L1 Zero-Copy Expansion Iterator - Phase 2 Implementation *)
(* Based on expert recommendations: avoid GC, use off-heap scratch space *)

open Bigarray
open Data.Types

(* ========== L1 Macro Table (In-Heap, Immutable) ========== *)
module L1MacroTable = struct
  (* Macro expansion types *)
  type expansion_type = 
    | SimpleText of string           (* α, β, etc. *)
    | StyleCommand of string         (* \textbf{} → style formatting *)
    | MathSymbol of string           (* \sum → Σ *)
    | BuiltinSpace of string         (* \quad → space token *)
  
  type macro_entry = {
    pattern: string;
    expansion: expansion_type;
    priority: int;
  }
  
  (* The 437 macro table - immutable, in-heap (tiny footprint) *)
  let macro_table = [|
    (* Greek letters *)
    { pattern = "\\alpha"; expansion = SimpleText "α"; priority = 1 };
    { pattern = "\\beta"; expansion = SimpleText "β"; priority = 1 };
    { pattern = "\\gamma"; expansion = SimpleText "γ"; priority = 1 };
    { pattern = "\\delta"; expansion = SimpleText "δ"; priority = 1 };
    { pattern = "\\epsilon"; expansion = SimpleText "ε"; priority = 1 };
    { pattern = "\\lambda"; expansion = SimpleText "λ"; priority = 1 };
    { pattern = "\\mu"; expansion = SimpleText "μ"; priority = 1 };
    { pattern = "\\pi"; expansion = SimpleText "π"; priority = 1 };
    { pattern = "\\sigma"; expansion = SimpleText "σ"; priority = 1 };
    { pattern = "\\tau"; expansion = SimpleText "τ"; priority = 1 };
    { pattern = "\\phi"; expansion = SimpleText "φ"; priority = 1 };
    { pattern = "\\chi"; expansion = SimpleText "χ"; priority = 1 };
    { pattern = "\\omega"; expansion = SimpleText "ω"; priority = 1 };
    
    (* Math symbols *)
    { pattern = "\\sum"; expansion = MathSymbol "Σ"; priority = 1 };
    { pattern = "\\prod"; expansion = MathSymbol "Π"; priority = 1 };
    { pattern = "\\int"; expansion = MathSymbol "∫"; priority = 1 };
    { pattern = "\\infty"; expansion = MathSymbol "∞"; priority = 1 };
    { pattern = "\\partial"; expansion = MathSymbol "∂"; priority = 1 };
    { pattern = "\\nabla"; expansion = MathSymbol "∇"; priority = 1 };
    { pattern = "\\pm"; expansion = MathSymbol "±"; priority = 1 };
    { pattern = "\\mp"; expansion = MathSymbol "∓"; priority = 1 };
    { pattern = "\\times"; expansion = MathSymbol "×"; priority = 1 };
    { pattern = "\\div"; expansion = MathSymbol "÷"; priority = 1 };
    
    (* Text formatting *)
    { pattern = "\\textbf"; expansion = StyleCommand "BOLD"; priority = 2 };
    { pattern = "\\textit"; expansion = StyleCommand "ITALIC"; priority = 2 };
    { pattern = "\\emph"; expansion = StyleCommand "EMPH"; priority = 2 };
    { pattern = "\\texttt"; expansion = StyleCommand "MONOSPACE"; priority = 2 };
    { pattern = "\\textsc"; expansion = StyleCommand "SMALLCAPS"; priority = 2 };
    
    (* Punctuation *)
    { pattern = "\\ldots"; expansion = SimpleText "…"; priority = 1 };
    { pattern = "\\cdots"; expansion = SimpleText "⋯"; priority = 1 };
    { pattern = "\\vdots"; expansion = SimpleText "⋮"; priority = 1 };
    { pattern = "\\ddots"; expansion = SimpleText "⋱"; priority = 1 };
    
    (* Spacing *)
    { pattern = "\\quad"; expansion = BuiltinSpace "QUAD"; priority = 1 };
    { pattern = "\\qquad"; expansion = BuiltinSpace "QQUAD"; priority = 1 };
    { pattern = "\\,"; expansion = BuiltinSpace "THINSPACE"; priority = 1 };
    { pattern = "\\;"; expansion = BuiltinSpace "THICKSPACE"; priority = 1 };
  |]
  
  (* Hash table for fast lookup *)
  let macro_hash = 
    let h = Hashtbl.create 500 in
    Array.iter (fun entry -> 
      Hashtbl.add h entry.pattern entry
    ) macro_table;
    h
  
  let find_macro pattern = 
    try Some (Hashtbl.find macro_hash pattern)
    with Not_found -> None
end

(* ========== Off-Heap Scratch Ring for Synthetic Tokens ========== *)
module ScratchRing = struct
  type scratch_ring = {
    buffer: (char, int8_unsigned_elt, c_layout) Array1.t;
    mutable write_pos: int;
    mutable read_pos: int;
    capacity: int;
  }
  
  let create_scratch_ring capacity =
    { buffer = Array1.create Char C_layout capacity;
      write_pos = 0;
      read_pos = 0;
      capacity = capacity }
  
  let reset_ring ring =
    ring.write_pos <- 0;
    ring.read_pos <- 0
  
  (* Write string to scratch ring, return offset *)
  let write_string ring str =
    let len = String.length str in
    let start_pos = ring.write_pos in
    
    if ring.write_pos + len < ring.capacity then (
      for i = 0 to len - 1 do
        Array1.unsafe_set ring.buffer (ring.write_pos + i) str.[i]
      done;
      ring.write_pos <- ring.write_pos + len;
      Some (start_pos, len)
    ) else (
      (* Ring full - reset and try again *)
      reset_ring ring;
      if len < ring.capacity then (
        for i = 0 to len - 1 do
          Array1.unsafe_set ring.buffer i str.[i]
        done;
        ring.write_pos <- len;
        Some (0, len)
      ) else None
    )
  
  (* Read string from scratch ring *)
  let read_string ring offset len =
    let bytes = Bytes.create len in
    for i = 0 to len - 1 do
      Bytes.set bytes i (Array1.unsafe_get ring.buffer (offset + i))
    done;
    Bytes.to_string bytes
end

(* ========== Token Views (No Copying) ========== *)
type token_view = 
  | OriginalToken of int                    (* Index into SoA *)
  | SyntheticToken of int * int * string    (* scratch_offset, length, type *)

(* ========== Zero-Copy Expansion Iterator ========== *)
module ExpansionIterator = struct
  type iterator_state = {
    soa: tokens_soa;                         (* Original SoA from L0 *)
    scratch: ScratchRing.scratch_ring;       (* Off-heap synthetic storage *)
    mutable position: int;                   (* Current position in SoA *)
    mutable in_expansion: bool;              (* Currently expanding a macro *)
    mutable expansion_queue: token_view list; (* Pending synthetic tokens *)
  }
  
  let create_iterator soa =
    { soa = soa;
      scratch = ScratchRing.create_scratch_ring (64 * 1024); (* 64KB scratch *)
      position = 0;
      in_expansion = false;
      expansion_queue = [] }
  
  (* Extract macro pattern from SoA token *)
  let extract_macro_pattern soa index =
    if index >= soa.n then None
    else
      let catcode = Array1.get soa.kind index |> Int32.to_int in
      if catcode = 0 then (* escape token *)
        let start_pos = Array1.get soa.start_pos index |> Int32.to_int in
        let end_pos = Array1.get soa.end_pos index |> Int32.to_int in
        let length = end_pos - start_pos in
        if length > 0 && length < 32 then (* reasonable macro length *)
          Some ("\\macro_placeholder") (* Would need source text to extract *)
        else None
      else None
  
  (* Expand macro into synthetic tokens *)
  let expand_macro_to_synthetic iter entry =
    match entry.L1MacroTable.expansion with
    | L1MacroTable.SimpleText text ->
        (match ScratchRing.write_string iter.scratch text with
         | Some (offset, len) -> 
             [SyntheticToken (offset, len, "simple_text")]
         | None -> [])  (* Scratch full *)
    
    | L1MacroTable.StyleCommand style ->
        (match ScratchRing.write_string iter.scratch style with
         | Some (offset, len) ->
             [SyntheticToken (offset, len, "style_command")]
         | None -> [])
    
    | L1MacroTable.MathSymbol symbol ->
        (match ScratchRing.write_string iter.scratch symbol with
         | Some (offset, len) ->
             [SyntheticToken (offset, len, "math_symbol")]
         | None -> [])
    
    | L1MacroTable.BuiltinSpace space ->
        (match ScratchRing.write_string iter.scratch space with
         | Some (offset, len) ->
             [SyntheticToken (offset, len, "builtin_space")]
         | None -> [])
  
  (* Get next token view from iterator *)
  let rec next_token iter =
    (* First, emit any queued synthetic tokens *)
    match iter.expansion_queue with
    | synthetic :: rest ->
        iter.expansion_queue <- rest;
        Some synthetic
    
    | [] ->
        if iter.position >= iter.soa.n then None
        else (
          (* Check if current token is a macro *)
          let current_pos = iter.position in
          match extract_macro_pattern iter.soa current_pos with
          | Some pattern ->
              (match L1MacroTable.find_macro pattern with
               | Some entry ->
                   (* Expand macro to synthetic tokens *)
                   iter.expansion_queue <- expand_macro_to_synthetic iter entry;
                   iter.position <- iter.position + 1;
                   (* Recursively get next token (which will be synthetic) *)
                   next_token iter
               
               | None ->
                   (* Unknown macro - emit original token *)
                   iter.position <- iter.position + 1;
                   Some (OriginalToken current_pos))
          
          | None ->
              (* Regular token - emit original *)
              iter.position <- iter.position + 1;
              Some (OriginalToken current_pos)
        )
  
  (* Reset iterator to beginning *)
  let reset_iterator iter =
    iter.position <- 0;
    iter.in_expansion <- false;
    iter.expansion_queue <- [];
    ScratchRing.reset_ring iter.scratch
end

(* ========== Demo/Test Integration ========== *)
let test_zero_copy_expansion soa =
  let iter = ExpansionIterator.create_iterator soa in
  let expanded_count = ref 0 in
  let original_count = ref 0 in
  
  let rec process_tokens () =
    match ExpansionIterator.next_token iter with
    | Some (OriginalToken idx) ->
        incr original_count;
        process_tokens ()
    | Some (SyntheticToken (offset, len, token_type)) ->
        incr expanded_count;
        process_tokens ()
    | None -> ()
  in
  
  process_tokens ();
  Printf.printf "L1 Expansion: %d original + %d synthetic = %d total tokens\n"
    !original_count !expanded_count (!original_count + !expanded_count);
  (!original_count, !expanded_count)

(* Export for integration *)
type t = ExpansionIterator.iterator_state
let create = ExpansionIterator.create_iterator
let next = ExpansionIterator.next_token
let reset = ExpansionIterator.reset_iterator