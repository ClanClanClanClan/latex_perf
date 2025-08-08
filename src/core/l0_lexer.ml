(* LaTeX Perfectionist v25 - L0 Lexer Implementation *)
(* Performance: Track A Enhanced - proven Week 39 optimization candidate *)
(* Zero-allocation with pre-computed catcode optimization *)

include L0_lexer_track_a_enhanced

(* Export main interface *)
let tokenize = tokenize_enhanced
let tokenize_string s = tokenize_enhanced s