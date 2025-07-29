(** Core types for LaTeX Perfectionist v25 
    Based on the Coq token definitions in src/coq/lexer/Lexer.v *)

(** Token type matching Coq definition *)
type token =
  | TText of string              (* Plain text content *)
  | TCommand of string           (* LaTeX commands like \section *)
  | TMathShift                   (* $ delimiter for math mode *)
  | TBeginGroup                  (* { opening brace *)
  | TEndGroup                    (* } closing brace *)
  | TParameter of int            (* #1, #2, etc. for macros *)
  | TSpace                       (* Explicit space token *)
  | TNewline                     (* Line break *)
  | TVerbatim of string          (* Verbatim content *)
  | TAlignment                   (* & table alignment *)
  | TSuperscript                 (* ^ superscript *)
  | TSubscript                   (* _ subscript *)
  | TComment of string           (* % comment to end of line *)
  | TEOF                         (* End of file *)

(** Position in source *)
type position = {
  byte_offset : int;
  line : int;
  column : int;
}

(** Token with position information *)
type located_token = {
  token : token;
  start_pos : position;
  end_pos : position;
}

(** Catcode as defined in LaTeX *)
type catcode = 
  | Escape      (* \ *)
  | BeginGroup  (* { *)
  | EndGroup    (* } *)
  | MathShift   (* $ *)
  | AlignTab    (* & *)
  | EndOfLine   (* \n *)
  | Parameter   (* # *)
  | Superscript (* ^ *)
  | Subscript   (* _ *)
  | Ignored     (* NUL *)
  | Space       (* space, tab *)
  | Letter      (* a-z, A-Z *)
  | Other       (* everything else *)
  | Active      (* ~ *)
  | Comment     (* % *)
  | Invalid     (* DEL *)

(** Convert token to string for debugging *)
let token_to_string = function
  | TText s -> Printf.sprintf "Text(%S)" s
  | TCommand s -> Printf.sprintf "Command(\\%s)" s
  | TMathShift -> "MathShift($)"
  | TBeginGroup -> "BeginGroup({)"
  | TEndGroup -> "EndGroup(})"
  | TParameter n -> Printf.sprintf "Parameter(#%d)" n
  | TSpace -> "Space"
  | TNewline -> "Newline"
  | TVerbatim s -> Printf.sprintf "Verbatim(%S)" s
  | TAlignment -> "Alignment(&)"
  | TSuperscript -> "Superscript(^)"
  | TSubscript -> "Subscript(_)"
  | TComment s -> Printf.sprintf "Comment(%%%s)" s
  | TEOF -> "EOF"

(** Get catcode for ASCII character *)
let catcode_of_char = function
  | '\\' -> Escape
  | '{' -> BeginGroup
  | '}' -> EndGroup
  | '$' -> MathShift
  | '&' -> AlignTab
  | '\n' -> EndOfLine
  | '#' -> Parameter
  | '^' -> Superscript
  | '_' -> Subscript
  | '\000' -> Ignored
  | ' ' | '\t' -> Space
  | '~' -> Active
  | '%' -> Comment
  | '\127' -> Invalid
  | c when (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') -> Letter
  | _ -> Other

(** Default catcode table (256 entries) *)
let default_catcode_table () =
  Array.init 256 (fun i -> catcode_of_char (Char.chr i))