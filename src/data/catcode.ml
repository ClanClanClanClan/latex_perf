(* Catcode Module - Week 1-2 Deliverable *)
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

(** Catcode lookup tables for each engine *)
module Tables = struct
  (* Default catcode assignments - TeX82 standard *)
  let default_table = 
    let tbl = Array.make 256 Other in
    (* Escape *)
    tbl.(Char.code '\\') <- Escape;
    (* Groups *)
    tbl.(Char.code '{') <- BeginGroup;
    tbl.(Char.code '}') <- EndGroup;
    (* Math *)
    tbl.(Char.code '$') <- MathShift;
    (* Alignment *)
    tbl.(Char.code '&') <- AlignTab;
    (* Line endings *)
    tbl.(Char.code '\r') <- EndLine;
    tbl.(Char.code '\n') <- EndLine;
    (* Parameters *)
    tbl.(Char.code '#') <- Param;
    (* Super/subscripts *)
    tbl.(Char.code '^') <- Superscript;
    tbl.(Char.code '_') <- Subscript;
    (* Ignored - null character *)
    tbl.(0) <- Ignored;
    (* Spaces *)
    tbl.(Char.code ' ') <- Space;
    tbl.(Char.code '\t') <- Space;
    (* Letters *)
    for i = Char.code 'a' to Char.code 'z' do
      tbl.(i) <- Letter
    done;
    for i = Char.code 'A' to Char.code 'Z' do
      tbl.(i) <- Letter
    done;
    (* Comment *)
    tbl.(Char.code '%') <- Comment;
    (* Invalid - high ASCII in original TeX *)
    for i = 128 to 255 do
      tbl.(i) <- Invalid
    done;
    tbl
  
  (* XeTeX/LuaTeX extend Letters to Unicode *)
  let unicode_letter_ranges = [
    (0x00C0, 0x00D6);   (* Latin-1 Supplement *)
    (0x00D8, 0x00F6);   (* Latin-1 Supplement cont. *)
    (0x00F8, 0x02FF);   (* Latin Extended-A, B *)
    (0x0370, 0x037D);   (* Greek *)
    (0x037F, 0x1FFF);   (* Greek Extended *)
    (0x200C, 0x200D);   (* Zero-width joiners *)
    (0x2070, 0x218F);   (* Superscripts/Subscripts *)
    (0x2C00, 0x2FEF);   (* Glagolitic, Coptic *)
    (0x3001, 0xD7FF);   (* CJK *)
    (0xF900, 0xFDCF);   (* CJK Compatibility *)
    (0xFDF0, 0xFFFD);   (* Arabic Presentation *)
    (0x10000, 0xEFFFF); (* Supplementary Planes *)
  ]
  
  let is_unicode_letter code =
    List.exists (fun (start, stop) -> 
      code >= start && code <= stop
    ) unicode_letter_ranges
end

(** Main catcode lookup function *)
let catcode_of (eng : engine) (u : Uchar.t) : catcode =
  let code = Uchar.to_int u in
  
  (* ASCII range - use lookup table *)
  if code < 256 then
    Tables.default_table.(code)
  else
    (* Unicode handling depends on engine *)
    match eng with
    | XeTeX | LuaTeX ->
        if Tables.is_unicode_letter code then Letter
        else Other
    | _ -> 
        (* Other engines treat high Unicode as invalid *)
        Invalid

(** Decidable equality for catcodes *)
let catcode_eq (c1 : catcode) (c2 : catcode) : bool =
  match c1, c2 with
  | Escape, Escape -> true
  | BeginGroup, BeginGroup -> true
  | EndGroup, EndGroup -> true
  | MathShift, MathShift -> true
  | AlignTab, AlignTab -> true
  | EndLine, EndLine -> true
  | Param, Param -> true
  | Superscript, Superscript -> true
  | Subscript, Subscript -> true
  | Ignored, Ignored -> true
  | Space, Space -> true
  | Letter, Letter -> true
  | Other, Other -> true
  | Active, Active -> true
  | Comment, Comment -> true
  | Invalid, Invalid -> true
  | _, _ -> false

(** Convert catcode to integer (for serialization) *)
let catcode_to_int = function
  | Escape -> 0
  | BeginGroup -> 1
  | EndGroup -> 2
  | MathShift -> 3
  | AlignTab -> 4
  | EndLine -> 5
  | Param -> 6
  | Superscript -> 7
  | Subscript -> 8
  | Ignored -> 9
  | Space -> 10
  | Letter -> 11
  | Other -> 12
  | Active -> 13
  | Comment -> 14
  | Invalid -> 15

(** Convert integer to catcode (for deserialization) *)
let int_to_catcode = function
  | 0 -> Some Escape
  | 1 -> Some BeginGroup
  | 2 -> Some EndGroup
  | 3 -> Some MathShift
  | 4 -> Some AlignTab
  | 5 -> Some EndLine
  | 6 -> Some Param
  | 7 -> Some Superscript
  | 8 -> Some Subscript
  | 9 -> Some Ignored
  | 10 -> Some Space
  | 11 -> Some Letter
  | 12 -> Some Other
  | 13 -> Some Active
  | 14 -> Some Comment
  | 15 -> Some Invalid
  | _ -> None

(** String representation for debugging *)
let catcode_to_string = function
  | Escape -> "Escape"
  | BeginGroup -> "BeginGroup"
  | EndGroup -> "EndGroup"
  | MathShift -> "MathShift"
  | AlignTab -> "AlignTab"
  | EndLine -> "EndLine"
  | Param -> "Param"
  | Superscript -> "Superscript"
  | Subscript -> "Subscript"
  | Ignored -> "Ignored"
  | Space -> "Space"
  | Letter -> "Letter"
  | Other -> "Other"
  | Active -> "Active"
  | Comment -> "Comment"
  | Invalid -> "Invalid"