#include <caml/mlvalues.h>
#include <sys/mman.h>
#include <sys/resource.h>
CAMLprim value ocaml_mlockall(value unit){
#ifdef __APPLE__
  mlockall(MCL_CURRENT|MCL_FUTURE); // best-effort; may be capped
#else
  struct rlimit r={RLIM_INFINITY,RLIM_INFINITY}; setrlimit(RLIMIT_MEMLOCK,&r);
  mlockall(MCL_CURRENT|MCL_FUTURE);
#endif
  return Val_unit;
}
