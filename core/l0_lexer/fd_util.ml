(** Safe conversion between [Unix.file_descr] and [int].

    On Unix systems, file descriptors are small non-negative integers.
    OCaml's [Unix.file_descr] is internally represented as an unboxed int,
    but accessing this via [Obj.magic] is fragile. These externals use
    C stubs that perform the identity conversion in a type-safe manner. *)

external fd_to_int : Unix.file_descr -> int = "fd_to_int" [@@noalloc]
external int_to_fd : int -> Unix.file_descr = "int_to_fd" [@@noalloc]
