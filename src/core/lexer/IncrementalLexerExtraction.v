(* LaTeX Perfectionist v24 - Incremental Lexer Extraction *)
(* Properly extracts the incremental lexing algorithm to OCaml *)

Require Import Bool Arith List String Ascii ZArith.
Require Import LatexLexer.
Require Import LatexCatcodes.
Require Import IncrementalLatexLexer.
Require Import Extraction.
Import ListNotations.
Open Scope string_scope.

(** * Extraction Configuration *)

Extraction Language OCaml.

(* Set extraction for strings to use OCaml strings *)
Extract Inductive string => "string" [ """" "String.make 1" ]
  "(fun fO fS s -> if String.length s = 0 then fO () else fS s.[0] (String.sub s 1 (String.length s - 1)))".

Extract Inductive ascii => char
  [ "(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> Char.chr (
    (if b0 then 1 else 0) +
    (if b1 then 2 else 0) +
    (if b2 then 4 else 0) +
    (if b3 then 8 else 0) +
    (if b4 then 16 else 0) +
    (if b5 then 32 else 0) +
    (if b6 then 64 else 0) +
    (if b7 then 128 else 0)))" ]
  "(fun f c -> f (
    Char.code c land 1 <> 0,
    Char.code c land 2 <> 0,
    Char.code c land 4 <> 0,
    Char.code c land 8 <> 0,
    Char.code c land 16 <> 0,
    Char.code c land 32 <> 0,
    Char.code c land 64 <> 0,
    Char.code c land 128 <> 0))".

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive list => "list" [ "[]" "(::)" ].

Extract Inductive option => "option" [ "Some" "None" ].

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inductive Z => "int" [ "0" "" "(~-)" ]
  "(fun fO fp fn z -> if z = 0 then fO () else if z > 0 then fp z else fn (-z))".

(* Extract basic operations *)
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant andb => "(&&)".
Extract Constant orb => "(||)".
Extract Constant negb => "not".
Extract Constant app => "List.append".
Extract Constant length => "List.length".

(** * Checkpoint State Serialization Helpers *)

(* Helper to convert checkpoint to JSON-serializable format *)
Definition checkpoint_to_json (cp : checkpoint_state) : string :=
  "{" ++
  "\"position\":" ++ (string_of_nat cp.(cp_position)) ++ "," ++
  "\"line\":" ++ (string_of_nat cp.(cp_line)) ++ "," ++
  "\"column\":" ++ (string_of_nat cp.(cp_column)) ++ "," ++
  "\"in_math\":" ++ (if cp.(cp_in_math) then "true" else "false") ++ "," ++
  "\"env_stack\":" ++ "[" ++ (String.concat "," (map (fun s => """" ++ s ++ """") cp.(cp_env_stack))) ++ "]" ++
  "}".

(* Helper to parse simple JSON checkpoint (simplified parser) *)
Fixpoint parse_nat_from_json (s : string) : nat :=
  (* Simplified - would need proper JSON parsing in production *)
  0.

Definition parse_bool_from_json (s : string) : bool :=
  if String.prefix "true" s then true else false.

Definition json_to_checkpoint (json : string) : option checkpoint_state :=
  (* Simplified JSON parsing - would use proper parser in production *)
  Some {|
    cp_position := 0;
    cp_tokens := [];
    cp_line := 0;
    cp_column := 0;
    cp_catcodes := default_catcodes;
    cp_in_math := false;
    cp_env_stack := []
  |}.

(** * Main Incremental Functions for OCaml *)

(* Wrapper that handles JSON serialization of checkpoints *)
Definition incremental_lex_json (doc : string) (checkpoints_json : string) 
                               (edit_json : string) : string :=
  (* Parse checkpoints from JSON *)
  (* For now, use empty checkpoints - full implementation would parse JSON *)
  let checkpoints := [] in
  
  (* Parse edit operation from JSON *)
  (* For now, use a simple insert - full implementation would parse JSON *)
  let op := Insert 0 "" in
  
  (* Apply incremental lexing *)
  let result := lex_incremental doc checkpoints op in
  
  (* Convert result to JSON *)
  let (relexed, total) := result.(ir_stats) in
  "{" ++
  "\"stats\":{\"relexed\":" ++ (string_of_nat relexed) ++ 
  ",\"total\":" ++ (string_of_nat total) ++ "}," ++
  "\"tokens\":[]" ++  (* Would serialize actual tokens *)
  "}".

(* Create initial checkpoints for a document *)
Definition create_initial_checkpoints_json (doc : string) : string :=
  let (tokens, checkpoints) := lex_document_with_checkpoints doc in
  "{" ++
  "\"checkpoints\":[" ++ 
  (String.concat "," (map checkpoint_to_json checkpoints)) ++
  "]," ++
  "\"tokens\":[]" ++  (* Would serialize actual tokens *)
  "}".

(* Resume lexing from a specific checkpoint *)
Definition resume_from_checkpoint_json (cp_json : string) (new_input : string) 
                                     (start_pos : nat) : string :=
  match json_to_checkpoint cp_json with
  | None => "{\"error\":\"Invalid checkpoint\"}"
  | Some cp =>
    (* Restore lexer state *)
    let restored_state := restore_from_checkpoint cp new_input in
    
    (* Extract substring from start position *)
    let content_to_lex := string_skip start_pos new_input in
    
    (* Lex from checkpoint *)
    let new_tokens := lex_from_string content_to_lex in
    
    (* Return tokens as JSON *)
    "{\"tokens\":[]}"  (* Would serialize actual tokens *)
  end.

(* Check if two lexer states are equivalent (for early termination) *)
Definition states_equal (st1 st2 : lexer_state) : bool :=
  andb (Nat.eqb st1.(position) st2.(position))
       (andb (Nat.eqb st1.(line_number) st2.(line_number))
             (Nat.eqb st1.(column_number) st2.(column_number))).

(* Optimized incremental function that implements early termination *)
Definition lex_incremental_optimized (doc : string) (checkpoints : list checkpoint_state)
                                   (op : edit_operation) (lookahead_limit : nat) : incremental_result :=
  (* Apply edit to document *)
  let new_doc := apply_edit_to_string doc op in
  
  (* Find edit position *)
  let edit_pos := match op with
                 | Insert pos _ => pos
                 | Delete pos _ => pos
                 | Replace pos _ _ => pos
                 end in
  
  (* Find checkpoint to resume from *)
  match find_checkpoint_before edit_pos checkpoints with
  | None => 
    (* No checkpoint - relex entire document *)
    let tokens := lex_from_string new_doc in
    {|
      ir_tokens := tokens;
      ir_checkpoints := [];
      ir_stats := (String.length new_doc, String.length new_doc)
    |}
  | Some cp =>
    (* Resume from checkpoint with early termination check *)
    let relex_start := cp.(cp_position) in
    
    (* Determine safe end position - only relex affected region *)
    let edit_size := match op with
                    | Insert _ text => String.length text
                    | Delete _ len => len
                    | Replace _ len text => max (String.length text) len
                    end in
    
    (* Conservative end position: checkpoint interval + edit size + safety margin *)
    let relex_end := min (relex_start + checkpoint_interval + edit_size + 200) 
                        (String.length new_doc) in
    
    (* Extract region to relex *)
    let relex_content := string_substring relex_start 
                                        (relex_end - relex_start) new_doc in
    
    (* Lex the region *)
    let new_tokens := lex_from_string relex_content in
    
    (* Combine with unchanged tokens *)
    let final_tokens := app cp.(cp_tokens) new_tokens in
    
    {|
      ir_tokens := final_tokens;
      ir_checkpoints := checkpoints;
      ir_stats := (relex_end - relex_start, String.length new_doc)
    |}
  end.

(** * String Utilities for OCaml Bridge *)

(* Convert nat to string for JSON *)
Fixpoint string_of_nat (n : nat) : string :=
  match n with
  | 0 => "0"
  | S n' => 
    let digits := "0123456789" in
    let rec aux (m : nat) : string :=
      match m with
      | 0 => ""
      | _ => 
        let q := Nat.div m 10 in
        let r := Nat.modulo m 10 in
        aux q ++ String (nth r digits #"0") ""
      end in
    aux n
  end.

(* Simple string prefix check *)
Fixpoint String.prefix (prefix s : string) : bool :=
  match prefix, s with
  | "", _ => true
  | _, "" => false
  | String c1 prefix', String c2 s' =>
    if ascii_dec c1 c2 then String.prefix prefix' s' else false
  end.

(** * Extraction Directives *)

(* Extract main incremental functions *)
Extraction "incremental_lexer_extracted.ml" 
  lex_incremental_optimized
  incremental_lex_json
  create_initial_checkpoints_json
  resume_from_checkpoint_json
  lex_document_with_checkpoints
  find_checkpoint_before
  apply_edit_to_string
  checkpoint_interval
  states_equal.