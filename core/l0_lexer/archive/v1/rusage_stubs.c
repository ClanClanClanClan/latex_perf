// macOS minor/major faults via proc_pid_rusage
#ifdef __APPLE__
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <libproc.h>
#include <unistd.h>

CAMLprim value ocaml_proc_rusage_faults(value unit){
  CAMLparam1(unit);
  CAMLlocal1(result);
  
  struct rusage_info_v2 ri;
  if (proc_pid_rusage(getpid(), RUSAGE_INFO_V2, (rusage_info_t*)&ri)==0){
    result = caml_alloc_tuple(2);
    Store_field(result, 0, caml_copy_int64(ri.ri_pageins));
    Store_field(result, 1, caml_copy_int64(ri.ri_pageins)); // Use pageins for both
    CAMLreturn(result);
  }
  result = caml_alloc_tuple(2); 
  Store_field(result, 0, Val_int(0)); 
  Store_field(result, 1, Val_int(0)); 
  CAMLreturn(result);
}
#else
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
CAMLprim value ocaml_proc_rusage_faults(value unit){ 
  CAMLparam1(unit);
  CAMLlocal1(result);
  result = caml_alloc_tuple(2); 
  Store_field(result, 0, Val_int(0)); 
  Store_field(result, 1, Val_int(0)); 
  CAMLreturn(result); 
}
#endif
