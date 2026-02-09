(** Safe conversion between {!Unix.file_descr} and [int] via C stubs.

    Avoids [Obj.magic] by performing the identity conversion in C. *)

val fd_to_int : Unix.file_descr -> int
val int_to_fd : int -> Unix.file_descr
