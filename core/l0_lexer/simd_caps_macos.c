// NEON and Rosetta detection for macOS
#include <caml/mlvalues.h>
#include <caml/mlvalues.h>
#include <sys/sysctl.h>

static int sysctl_int(const char* name, int* out){
  size_t sz=sizeof(int); return sysctlbyname(name, out, &sz, NULL, 0);
}
CAMLprim value ocaml_is_rosetta(value unit){
  int v=0; size_t sz=sizeof(v);
  if (sysctlbyname("sysctl.proc_translated",&v,&sz,NULL,0)!=0) v=0;
  return Val_bool(v!=0);
}
CAMLprim value ocaml_has_neon(value unit){
  int neon=0; if (sysctl_int("hw.optional.neon",&neon)!=0) neon=1;
  return Val_bool(neon!=0);
}
