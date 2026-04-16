(** Execution policy: controls which execution classes are active in a run. *)

type t = { enable_a : bool; enable_b : bool; enable_c : bool; enable_d : bool }

val default : t
(** A+B only. Keystroke-safe path. *)

val with_build : t
(** A+B+C. For save/build triggers with compile log available. *)

val full : t
(** A+B+C+D. All classes enabled. *)

val allows : t -> Execution_class.t -> bool
(** [true] if the policy enables the given class. *)
