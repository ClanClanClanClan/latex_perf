(* Catcode Module Interface - Week 1-2 Deliverable *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.1.3 *)

(** LaTeX character category codes *)
type catcode = 
  | Escape      (* 0: Starts commands like \ *)
  | BeginGroup  (* 1: Begin group { *)
  | EndGroup    (* 2: End group } *)
  | MathShift   (* 3: Math mode $ *)
  | AlignTab    (* 4: Alignment & *)
  | EndLine     (* 5: Line ending *)
  | Param       (* 6: Parameter # *)
  | Superscript (* 7: Superscript ^ *)
  | Subscript   (* 8: Subscript _ *)
  | Ignored     (* 9: Ignored characters *)
  | Space       (* 10: Space characters *)
  | Letter      (* 11: Letters a-z A-Z *)
  | Other       (* 12: Other characters *)
  | Active      (* 13: Active characters *)
  | Comment     (* 14: Comment % *)
  | Invalid     (* 15: Invalid characters *)

(** TeX engine types *)
type engine = 
  | PdfTeX 
  | XeTeX 
  | LuaTeX
  | ConTeXt
  | PlainTeX
  | ETeX
  | Omega
  | Aleph

(** Main catcode lookup function 
    Returns the character category for a given Unicode character 
    under the specified TeX engine *)
val catcode_of : engine -> Uchar.t -> catcode

(** Decidable equality for catcodes *)
val catcode_eq : catcode -> catcode -> bool

(** Convert catcode to integer (0-15) for serialization *)
val catcode_to_int : catcode -> int

(** Convert integer to catcode (for deserialization) 
    Returns None if integer is out of range *)
val int_to_catcode : int -> catcode option

(** String representation for debugging *)
val catcode_to_string : catcode -> string