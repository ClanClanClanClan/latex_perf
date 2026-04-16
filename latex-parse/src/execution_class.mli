(** Execution class taxonomy (v26 spec section 6).

    Classifies rules by when they execute:
    - A: keystroke-critical, strict latency budget
    - B: debounce background, short idle delay
    - C: build-coupled, requires compile logs
    - D: optional heuristic, advisory *)

type t = A | B | C | D

val classify : string -> t
(** Classify a rule ID to its execution class. *)

val is_keystroke_safe : t -> bool
(** [true] for Class A and B. *)

val to_string : t -> string
