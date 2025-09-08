(* Core data types for LaTeX Perfectionist v25_R1 *)

module Location = struct
  type t = {
    line: int;
    column: int;
    offset: int;
  }

  let make line column offset = { line; column; offset }
  
  let zero = { line = 1; column = 1; offset = 0 }
  
  let to_string loc = 
    Printf.sprintf "%d:%d" loc.line loc.column
end

module Catcode = struct
  type catcode = 
    | Escape     (* \ *)
    | BeginGrp   (* { *)
    | EndGrp     (* } *)
    | Math       (* $ *)
    | AlignTab   (* & *)
    | Newline    (* ^M *)
    | Param      (* # *)
    | Superscr   (* ^ *)
    | Subscr     (* _ *)
    | Ignored    (* null *)
    | Space      (* space *)
    | Letter     (* a-zA-Z *)
    | Other      (* punctuation *)
    | Active     (* ~ *)
    | Comment    (* % *)
    | Invalid    (* delete *)

  let catcode_to_string = function
    | Escape -> "Escape"
    | BeginGrp -> "BeginGrp"
    | EndGrp -> "EndGrp"
    | Math -> "Math"
    | AlignTab -> "AlignTab"
    | Newline -> "Newline"
    | Param -> "Param"
    | Superscr -> "Superscr"
    | Subscr -> "Subscr"
    | Ignored -> "Ignored"
    | Space -> "Space"
    | Letter -> "Letter"
    | Other -> "Other"
    | Active -> "Active"
    | Comment -> "Comment"
    | Invalid -> "Invalid"
    
  let catcode_to_int = function
    | Escape -> 0 | BeginGrp -> 1 | EndGrp -> 2 | Math -> 3
    | AlignTab -> 4 | Newline -> 5 | Param -> 6 | Superscr -> 7
    | Subscr -> 8 | Ignored -> 9 | Space -> 10 | Letter -> 11
    | Other -> 12 | Active -> 13 | Comment -> 14 | Invalid -> 15
end

(* Core token type - matches v25 specification *)
type token =
  | TChar of Uchar.t * Catcode.catcode      (* Character with category code *)
  | TMacro of string                        (* Control sequence *)
  | TParam of int                          (* Parameter #1-#9 *)
  | TGroupOpen                             (* Begin group { *)
  | TGroupClose                            (* End group } *)
  | TEOF                                   (* End of file *)

(* Located token for position tracking *)
type located_token = {
  token: token;
  location: Location.t;
}

(* Structure of Arrays token representation for performance *)
type tokens_soa = {
  kind: (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t;
  start_pos: (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t;
  end_pos: (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t;
  n: int;
}