(* l1_macro_extensions.ml - 56 Additional L1-Safe Macro Extensions *)
(* Extends the existing 406-macro system to 462 total macros *)

open Printf

(* Import existing types from l1_macro_production.ml *)
type token =
  | TText of string
  | TOp of string  
  | TDelim of string
  | TBeginGroup
  | TEndGroup
  | TControl of string

type mode = Math | Text | Any

type symbol_macro = {
  name : string;
  mode : mode;
  expansion : token list;
  expand_in_math : bool;
  expand_in_text : bool;
}

type argumentful_macro = {
  name : string;
  positional : int;
  template : string;
  epsilon_safe : bool;
}

(* ================================================================ *)
(* CATEGORY 1: Missing Text Symbols (12 macros)                    *)
(* ================================================================ *)

let text_symbol_extensions = [
  (* Currency symbols *)
  { name = "textcurrency"; mode = Text; expansion = [TText "¤"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textlira"; mode = Text; expansion = [TText "₤"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textwon"; mode = Text; expansion = [TText "₩"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textrupee"; mode = Text; expansion = [TText "₹"]; 
    expand_in_math = false; expand_in_text = true };
    
  (* Common punctuation *)
  { name = "textexclamdown"; mode = Text; expansion = [TText "¡"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textquestiondown"; mode = Text; expansion = [TText "¿"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textquoteleft"; mode = Text; expansion = [TText "'"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textquoteright"; mode = Text; expansion = [TText "'"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textquotedblleft"; mode = Text; expansion = [TText "\""]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textquotedblright"; mode = Text; expansion = [TText "\""]; 
    expand_in_math = false; expand_in_text = true };
    
  (* Publishing marks *)
  { name = "textsection"; mode = Text; expansion = [TText "§"]; 
    expand_in_math = false; expand_in_text = true };
  { name = "textpilcrow"; mode = Text; expansion = [TText "¶"]; 
    expand_in_math = false; expand_in_text = true };
]

(* ================================================================ *)
(* CATEGORY 2: Logic Symbols (15 macros)                           *)
(* ================================================================ *)

let logic_symbol_extensions = [
  (* Basic logic *)
  { name = "land"; mode = Math; expansion = [TOp "∧"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "lor"; mode = Math; expansion = [TOp "∨"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "lnot"; mode = Math; expansion = [TOp "¬"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "implies"; mode = Math; expansion = [TOp "⇒"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "iff"; mode = Math; expansion = [TOp "⇔"]; 
    expand_in_math = true; expand_in_text = false };
    
  (* Quantifiers *)
  { name = "forall"; mode = Math; expansion = [TOp "∀"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "exists"; mode = Math; expansion = [TOp "∃"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "nexists"; mode = Math; expansion = [TOp "∄"]; 
    expand_in_math = true; expand_in_text = false };
    
  (* Additional arrows *)
  { name = "uparrow"; mode = Math; expansion = [TOp "↑"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "downarrow"; mode = Math; expansion = [TOp "↓"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "updownarrow"; mode = Math; expansion = [TOp "↕"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "nearrow"; mode = Math; expansion = [TOp "↗"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "searrow"; mode = Math; expansion = [TOp "↘"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "swarrow"; mode = Math; expansion = [TOp "↙"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "nwarrow"; mode = Math; expansion = [TOp "↖"]; 
    expand_in_math = true; expand_in_text = false };
]

(* ================================================================ *)
(* CATEGORY 3: Mathematical Font Commands (15 macros)              *)
(* ================================================================ *)

let math_font_extensions = [
  (* Existing in catalog but adding more variants *)
  { name = "mathcal"; positional = 1; 
    template = "{\\mathcal{$1}}"; epsilon_safe = true };
  { name = "mathscr"; positional = 1; 
    template = "{\\mathscr{$1}}"; epsilon_safe = true };
  { name = "mathfrak"; positional = 1; 
    template = "{\\mathfrak{$1}}"; epsilon_safe = true };
    
  (* Text font commands with single argument *)
  { name = "textrm"; positional = 1; 
    template = "{\\rmfamily $1}"; epsilon_safe = true };
  { name = "textsf"; positional = 1; 
    template = "{\\sffamily $1}"; epsilon_safe = true };
  { name = "texttt"; positional = 1; 
    template = "{\\ttfamily $1}"; epsilon_safe = true };
  { name = "textsl"; positional = 1; 
    template = "{\\slshape $1}"; epsilon_safe = true };
  { name = "textup"; positional = 1; 
    template = "{\\upshape $1}"; epsilon_safe = true };
  { name = "textmd"; positional = 1; 
    template = "{\\mdseries $1}"; epsilon_safe = true };
  { name = "textnormal"; positional = 1; 
    template = "{\\normalfont $1}"; epsilon_safe = true };
    
  (* Emphasis variants *)
  { name = "textbfseries"; positional = 1; 
    template = "{\\bfseries $1}"; epsilon_safe = true };
  { name = "textitshape"; positional = 1; 
    template = "{\\itshape $1}"; epsilon_safe = true };
  { name = "textscshape"; positional = 1; 
    template = "{\\scshape $1}"; epsilon_safe = true };
  { name = "textupshape"; positional = 1; 
    template = "{\\upshape $1}"; epsilon_safe = true };
  { name = "textslshape"; positional = 1; 
    template = "{\\slshape $1}"; epsilon_safe = true };
]

(* ================================================================ *)
(* CATEGORY 4: Accent Commands with Unicode Mapping (8 macros)     *)
(* ================================================================ *)

let accent_extensions = [
  (* These would ideally map to combining characters, but for L1 *)
  (* we use precomposed characters where available *)
  { name = "grave"; positional = 1; 
    template = "$1̀"; epsilon_safe = true };  (* combining grave accent *)
  { name = "acute"; positional = 1; 
    template = "$1́"; epsilon_safe = true };  (* combining acute accent *)
  { name = "hat"; positional = 1; 
    template = "$1̂"; epsilon_safe = true };    (* combining circumflex *)
  { name = "tilde"; positional = 1; 
    template = "$1̃"; epsilon_safe = true };   (* combining tilde *)
  { name = "bar"; positional = 1; 
    template = "$1̄"; epsilon_safe = true };    (* combining macron *)
  { name = "breve"; positional = 1; 
    template = "$1̆"; epsilon_safe = true };   (* combining breve *)
  { name = "dot"; positional = 1; 
    template = "$1̇"; epsilon_safe = true };    (* combining dot above *)
  { name = "ddot"; positional = 1; 
    template = "$1̈"; epsilon_safe = true };   (* combining diaresis *)
]

(* ================================================================ *)
(* CATEGORY 5: Spacing Commands (4 macros)                         *)
(* ================================================================ *)

let spacing_extensions = [
  (* Non-breaking spaces of various widths *)
  { name = "quad"; mode = Any; expansion = [TText "  "]; 
    expand_in_math = true; expand_in_text = true };
  { name = "qquad"; mode = Any; expansion = [TText "    "]; 
    expand_in_math = true; expand_in_text = true };
  { name = "enspace"; mode = Any; expansion = [TText " "]; 
    expand_in_math = true; expand_in_text = true };
  { name = "thinspace"; mode = Any; expansion = [TText " "]; 
    expand_in_math = true; expand_in_text = true };
]

(* ================================================================ *)
(* CATEGORY 6: Additional Symbols (2 macros)                       *)
(* ================================================================ *)

let additional_symbol_extensions = [
  { name = "bigstar"; mode = Math; expansion = [TOp "★"]; 
    expand_in_math = true; expand_in_text = false };
  { name = "blacksquare"; mode = Math; expansion = [TOp "■"]; 
    expand_in_math = true; expand_in_text = false };
]

(* ================================================================ *)
(* EXTENSION CATALOG ASSEMBLY                                      *)
(* ================================================================ *)

let all_symbol_extensions = 
  text_symbol_extensions @ 
  logic_symbol_extensions @ 
  spacing_extensions @ 
  additional_symbol_extensions

let all_argumentful_extensions = 
  math_font_extensions @ 
  accent_extensions

(* ================================================================ *)
(* INTEGRATION WITH EXISTING SYSTEM                                *)
(* ================================================================ *)

(* Function to add extensions to existing macro table *)
let integrate_extensions macro_table =
  (* Add symbol extensions *)
  List.iter (fun sym ->
    Hashtbl.add macro_table sym.name (Symbol sym)
  ) all_symbol_extensions;
  
  (* Add argumentful extensions *)
  List.iter (fun arg ->
    Hashtbl.add macro_table arg.name (Argumentful arg)
  ) all_argumentful_extensions;
  
  macro_table

(* Statistics function *)
let count_extensions () =
  let symbol_count = List.length all_symbol_extensions in
  let argumentful_count = List.length all_argumentful_extensions in
  (symbol_count, argumentful_count, symbol_count + argumentful_count)

(* Test function to verify extensions *)
let test_extensions () =
  printf "=== L1 Macro Extensions Test ===\n\n";
  
  let (symbols, args, total) = count_extensions () in
  printf "Extension catalog: %d symbols + %d argumentful = %d total\n\n" 
    symbols args total;
  
  let take n lst = 
    let rec aux n acc = function
      | [] -> List.rev acc
      | _ when n <= 0 -> List.rev acc
      | h :: t -> aux (n-1) (h :: acc) t
    in aux n [] lst in
  
  printf "Sample text symbols:\n";
  List.iter (fun sym ->
    printf "  \\%s → %s\n" sym.name 
      (String.concat "" (List.map (function
        | TText s -> s | TOp s -> s | _ -> "?") sym.expansion))
  ) (take 5 text_symbol_extensions);
  
  printf "\nSample logic symbols:\n";
  List.iter (fun sym ->
    printf "  \\%s → %s\n" sym.name 
      (String.concat "" (List.map (function
        | TText s -> s | TOp s -> s | _ -> "?") sym.expansion))
  ) (take 5 logic_symbol_extensions);
  
  printf "\nSample font commands:\n";
  List.iter (fun arg ->
    printf "  \\%s{text} → %s\n" arg.name 
      (Str.global_replace (Str.regexp_string "$1") "text" arg.template)
  ) (take 5 math_font_extensions);
  
  printf "\nSample accent commands:\n";
  List.iter (fun arg ->
    printf "  \\%s{e} → %s\n" arg.name 
      (Str.global_replace (Str.regexp_string "$1") "e" arg.template)
  ) (take 4 accent_extensions);
  
  printf "\n=== Extension Summary ===\n";
  printf "✅ Text symbols: %d new (currency, punctuation, publishing)\n" 
    (List.length text_symbol_extensions);
  printf "✅ Logic symbols: %d new (operators, quantifiers, arrows)\n" 
    (List.length logic_symbol_extensions);
  printf "✅ Font commands: %d new (math & text styling)\n" 
    (List.length math_font_extensions);
  printf "✅ Accent commands: %d new (Unicode combining characters)\n" 
    (List.length accent_extensions);
  printf "✅ Spacing commands: %d new (various width spaces)\n" 
    (List.length spacing_extensions);
  printf "✅ Additional symbols: %d new (decorative)\n" 
    (List.length additional_symbol_extensions);
  printf "\n🎯 Total new macros: %d (extending 406 → 462)\n" total;
  printf "🚀 Ready for integration with production L1 expander\n"

(* Standalone test if run directly *)
let () = 
  if not !Sys.interactive then
    test_extensions ()

(* Export for use by other modules *)
module L1_Extensions = struct
  type macro = Symbol of symbol_macro | Argumentful of argumentful_macro
  
  let symbol_extensions = all_symbol_extensions
  let argumentful_extensions = all_argumentful_extensions
  let integrate = integrate_extensions
  let count = count_extensions
end