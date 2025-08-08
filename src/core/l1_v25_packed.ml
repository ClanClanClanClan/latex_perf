(* L1 V25 - Packed Token Version
   Processes packed tokens from L0 without conversion overhead *)

type packed_token = int32

(* Expanded result with packed tokens *)
type expanded_result = {
  tokens: packed_token array;
  macros_expanded: int;
  fuel_consumed: int;
}

(* Simple expansion state *)
type expansion_state = {
  builtin_macros: (string * string) list; (* name -> expansion *)
  mutable expansions_done: int;
}

let create_initial_state () = {
  builtin_macros = [
    (* Display math expansions *)
    ("[", "⟨display-math-begin⟩");
    ("]", "⟨display-math-end⟩");
    (* Basic expansions *)
    ("LaTeX", "LaTeX");
    ("TeX", "TeX");
  ];
  expansions_done = 0;
}

(* Check if a packed token is a macro *)
let is_macro_token (token: packed_token) =
  let open L0_lexer_track_a_arena.TokenPacking in
  let catcode = unpack_catcode token in
  catcode = cc_escape

(* Get macro name from packed token *)
let get_macro_name (token: packed_token) =
  if is_macro_token token then
    let open L0_lexer_track_a_arena in
    let macro_id = TokenPacking.unpack_data token in
    StringOps.get_macro_name_by_id macro_id
  else
    failwith "Not a macro token"

(* Simple expansion - for now just pass through tokens *)
let expand_tokens (state: expansion_state) (tokens: packed_token array) =
  (* For now, pass through all tokens unchanged *)
  (* Real expansion would process macros here but keep in packed format *)
  
  (* Count macros for statistics *)
  let macro_count = Array.fold_left (fun acc token ->
    if is_macro_token token then acc + 1 else acc
  ) 0 tokens in
  
  state.expansions_done <- state.expansions_done + macro_count;
  
  {
    tokens = tokens; (* Pass through unchanged for now *)
    macros_expanded = macro_count;
    fuel_consumed = macro_count * 2; (* Simple fuel calculation *)
  }

(* Expand tokens from L0 packed format *)
let expand_packed_tokens (packed_tokens: packed_token array) =
  let state = create_initial_state () in
  expand_tokens state packed_tokens

(* Debug function to show what's in packed tokens *)
let debug_packed_tokens (tokens: packed_token array) limit =
  Printf.printf "Packed tokens (%d total, showing first %d):\n" 
    (Array.length tokens) (min limit (Array.length tokens));
  for i = 0 to min (limit - 1) (Array.length tokens - 1) do
    let token = tokens.(i) in
    let token_str = 
      try L0_lexer_track_a_arena.PackedToken.to_string token
      with _ -> Printf.sprintf "Token(%ld)" token
    in
    Printf.printf "  [%d] %s\n" i token_str
  done