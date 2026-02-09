(** Robust socket I/O helpers.

    All functions retry on {!Unix.EINTR} and return [Error] on EOF or
    short-write instead of raising exceptions. *)

(** I/O error conditions. *)
type error = Eof | Short_write

val error_to_string : error -> string

(** {2 Result-returning API} *)

val read_exact : Unix.file_descr -> bytes -> int -> int -> (unit, error) result
val write_all : Unix.file_descr -> bytes -> int -> int -> (unit, error) result

(** {2 Exception-raising convenience wrappers}

    Use these when callers already have a top-level [try ... with] that converts
    exceptions to connection-close / error-result behaviour. *)

val read_exact_exn : Unix.file_descr -> bytes -> int -> int -> unit
val write_all_exn : Unix.file_descr -> bytes -> int -> int -> unit
