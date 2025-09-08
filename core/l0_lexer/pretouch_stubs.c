// Memory locking for performance isolation
#include <caml/mlvalues.h>
#include <sys/mman.h>
#include <errno.h>

CAMLprim value ocaml_mlock_all(value unit) {
  // Lock all current and future pages
  if (mlockall(MCL_CURRENT | MCL_FUTURE) == 0) {
    return Val_unit;
  }
  // Silently fail if permission denied
  return Val_unit;
}
