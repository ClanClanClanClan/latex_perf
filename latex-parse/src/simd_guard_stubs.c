#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <string.h>

#if defined(__aarch64__)
static int simd_ok(void){ return 1; } /* NEON is mandatory on arm64 */
#elif defined(__x86_64__)
static int simd_ok(void){
  /* CPUID check for AVX2 */
  unsigned int eax, ebx, ecx, edx;
  eax = 7; ecx = 0;
  __asm__ __volatile__("cpuid"
    : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
    : "a"(eax), "c"(ecx));
  return (ebx & (1u<<5)) != 0; /* AVX2 bit */
}
#else
static int simd_ok(void){ return 0; }
#endif

CAMLprim value ocaml_simd_available(value unit) {
  return Val_int(simd_ok());
}

CAMLprim value ocaml_require_simd(value unit){
  const char* allow = getenv("L0_ALLOW_SCALAR");
  if (!simd_ok() && !(allow && strcmp(allow, "1")==0)) {
    caml_failwith("SIMD not available and L0_ALLOW_SCALAR!=1");
  }
  return Val_unit;
}