(** L0 Lexer Interface - LaTeX Perfectionist v25
    
    Performance Requirements:
    - p95 latency: 80μs
    - Hard cutoff: 160μs
    - Chunk size: ≤4 KiB
    
    From Technical Resolution: Question 1
*)

open Types

(** Main lexing function - pure, never raises 
    
    @param prev Optional previous lexer state for incremental processing
    @param bytes UTF-8 encoded chunk (≤4 KiB logical)
    @return Token array and new lexer state
*)
val lex_chunk : ?prev:lexer_state -> bytes -> token array * lexer_state

(** Initialize a fresh lexer state *)
val initial_state : unit -> lexer_state

(** Compute cache key for memoization (Question 5) *)
val compute_cache_key : bytes -> lexer_state -> l0_cache_key

and l0_cache_key = {
  chunk_id : int;
  hash : int64;  (* xxh3 64-bit hash *)
}

(** SIMD-optimized lexing paths (Question 16) *)
module Simd : sig
  type path = Scalar | Avx2 | Avx512 | Neon
  
  (** Detect best SIMD path for current CPU *)
  val detect_features : unit -> path
  
  (** Get current selected path *)
  val selected_path : unit -> path
end

(** Error types for L0 layer (Question 2) *)
type lexer_error = 
  | InvalidUtf8 of { offset : int; bytes : bytes }
  | ChunkTooLarge of { size : int; limit : int }
  | CatcodeTableCorrupted

(** Result type following error propagation protocol *)
type 'a result = ('a, [`fatal] layer_err) Stdlib.result

and _ layer_err =
  | L0_Fatal : lexer_error -> [`fatal] layer_err