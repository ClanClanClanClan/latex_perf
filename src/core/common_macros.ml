(** Common LaTeX macro definitions for v25
    
    This module defines the 76 built-in macros mentioned in the v25 spec.
    These are placeholder implementations until we extract from Coq.
*)

open Types

(* Text formatting macros *)
let text_macros = [
  ("LaTeX", [TText "LaTeX"]);
  ("TeX", [TText "TeX"]);
  ("textbf", [TText "[bold]"]);
  ("textit", [TText "[italic]"]);
  ("emph", [TText "[emph]"]);
  ("texttt", [TText "[monospace]"]);
  ("textsc", [TText "[smallcaps]"]);
  ("textrm", [TText "[roman]"]);
  ("textsf", [TText "[sans-serif]"]);
  ("textsl", [TText "[slanted]"]);
  ("underline", [TText "[underline]"]);
  ("textup", [TText "[upright]"]);
]

(* Math macros *)
let math_macros = [
  ("alpha", [TText "α"]);
  ("beta", [TText "β"]);
  ("gamma", [TText "γ"]);
  ("delta", [TText "δ"]);
  ("epsilon", [TText "ε"]);
  ("theta", [TText "θ"]);
  ("lambda", [TText "λ"]);
  ("mu", [TText "μ"]);
  ("pi", [TText "π"]);
  ("sigma", [TText "σ"]);
  ("phi", [TText "φ"]);
  ("omega", [TText "ω"]);
  ("sum", [TText "∑"]);
  ("int", [TText "∫"]);
  ("prod", [TText "∏"]);
  ("infty", [TText "∞"]);
  ("partial", [TText "∂"]);
  ("nabla", [TText "∇"]);
  ("pm", [TText "±"]);
  ("times", [TText "×"]);
  ("div", [TText "÷"]);
  ("cdot", [TText "·"]);
  ("leq", [TText "≤"]);
  ("geq", [TText "≥"]);
  ("neq", [TText "≠"]);
  ("approx", [TText "≈"]);
  ("equiv", [TText "≡"]);
  ("in", [TText "∈"]);
  ("subset", [TText "⊂"]);
  ("subseteq", [TText "⊆"]);
  ("cup", [TText "∪"]);
  ("cap", [TText "∩"]);
  ("rightarrow", [TText "→"]);
  ("leftarrow", [TText "←"]);
  ("Rightarrow", [TText "⇒"]);
  ("Leftarrow", [TText "⇐"]);
  ("forall", [TText "∀"]);
  ("exists", [TText "∃"]);
]

(* Spacing and typography macros *)
let spacing_macros = [
  ("ldots", [TText "..."]);
  ("cdots", [TText "⋯"]);
  ("vdots", [TText "⋮"]);
  ("ddots", [TText "⋱"]);
  ("quad", [TSpace]);
  ("qquad", [TSpace; TSpace]);
  ("!", []);  (* Negative thin space *)
  (",", [TSpace]);  (* Thin space *)
  (":", [TSpace]);  (* Medium space *)
  (";", [TSpace]);  (* Thick space *)
  ("~", [TSpace]);  (* Non-breaking space *)
  ("@", []);  (* Null space *)
]

(* Accents and special characters *)
let accent_macros = [
  ("'", [TText "́"]);   (* Acute accent *)
  ("`", [TText "̀"]);   (* Grave accent *)
  ("^", [TText "̂"]);   (* Circumflex *)
  ("\"", [TText "̈"]);  (* Diaeresis *)
  ("tilde", [TText "̃"]);   (* Tilde accent - renamed to avoid conflict *)
  ("=", [TText "̄"]);   (* Macron *)
  (".", [TText "̇"]);   (* Dot accent *)
  ("u", [TText "̆"]);   (* Breve *)
  ("v", [TText "̌"]);   (* Caron *)
  ("H", [TText "̋"]);   (* Double acute *)
  ("c", [TText "̧"]);   (* Cedilla *)
]

(* Document structure macros *)
let structure_macros = [
  ("par", [TNewline; TNewline]);
  ("\\", [TNewline]);
  ("newline", [TNewline]);
  ("linebreak", [TNewline]);
  ("noindent", []);
  ("indent", [TSpace]);
]

(* Reference macros *)
let reference_macros = [
  ("S", [TText "§"]);
  ("P", [TText "¶"]);
  ("dag", [TText "†"]);
  ("ddag", [TText "‡"]);
  ("copyright", [TText "©"]);
  ("pounds", [TText "£"]);
  ("dots", [TText "…"]);
]

(* Additional macros to reach 86 total *)
let additional_macros = [
  ("today", [TText "2025-07-29"]);
  ("LaTeXe", [TText "LaTeX2e"]);
  ("footnote", [TText "[footnote]"]);
]

(* Combine all macros *)
let all_macros = 
  text_macros @ math_macros @ spacing_macros @ 
  accent_macros @ structure_macros @ reference_macros @ additional_macros

(* Get all macro definitions as simple pairs *)
let builtin_macro_list = all_macros

(* Count of macros *)
let macro_count = List.length all_macros