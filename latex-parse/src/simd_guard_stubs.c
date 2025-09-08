#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <stdint.h>

/* Weak reference to the SIMD entrypoint symbol provided by your static lib.
   If the linker dead-strips it, this pointer stays NULL unless we force-load. */
__attribute__((weak)) void tokenize_bytes_into_soa_simd(void);

#if defined(__APPLE__) && (defined(__aarch64__) || defined(__arm64__))
  #include <sys/sysctl.h>
  static int cpu_has_simd(void){
    int neon = 0; size_t sz = sizeof(neon);
    if (sysctlbyname("hw.optional.neon", &neon, &sz, NULL, 0) != 0) return 0;
    return neon ? 1 : 0;
  }
#elif defined(__aarch64__)
  #include <sys/auxv.h>
  #include <asm/hwcap.h>
  static int cpu_has_simd(void){
    unsigned long caps = getauxval(AT_HWCAP);
    return (caps & HWCAP_ASIMD) ? 1 : 0;
  }
#elif defined(__x86_64__) || defined(__i386__)
  #include <cpuid.h>
  static int cpu_has_simd(void){
    unsigned eax, ebx, ecx, edx;
    if (!__get_cpuid(7, &eax, &ebx, &ecx, &edx)) return 0;
    return (ebx & (1u<<5)) ? 1 : 0; /* AVX2 bit */
  }
#else
  static int cpu_has_simd(void){ return 0; }
#endif

CAMLprim value ocaml_simd_cpu_supported(value unit){
  return Val_bool(cpu_has_simd());
}

CAMLprim value ocaml_simd_symbol_linked(value unit){
  return Val_bool(tokenize_bytes_into_soa_simd != 0);
}