#include <caml/mlvalues.h>

/*
 * Safe conversion between Unix.file_descr and int.
 *
 * On Unix, OCaml's Unix.file_descr is represented as an unboxed int
 * (the raw OS file descriptor). These stubs provide a type-safe bridge
 * without resorting to Obj.magic.
 */

CAMLprim value fd_to_int(value fd) { return fd; }
CAMLprim value int_to_fd(value n)  { return n; }
