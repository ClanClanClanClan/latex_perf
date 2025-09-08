// Stub for external tokenizer
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>

CAMLprim value core_tokenize_stub(value input_str) {
  CAMLparam1(input_str);
  // For now, just fail and let the fallback handle it
  caml_failwith("External tokenizer not available");
  CAMLreturn(Val_unit); // Never reached
}
