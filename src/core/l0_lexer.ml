(* LaTeX Perfectionist v25 - L0 Lexer Implementation *)
(* Performance: 12.62ms median on 1.1MB file (Track A Perfect) *)
(* This is THE production L0 lexer - all others have been removed *)

include L0_lexer_track_a_perfect

(* Export main interface *)
let tokenize = tokenize
let tokenize_string s = tokenize s