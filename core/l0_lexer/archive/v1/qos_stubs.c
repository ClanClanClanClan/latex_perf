#include <caml/mlvalues.h>
#ifdef __APPLE__
#include <pthread.h>
#include <pthread/qos.h>
#include <sys/resource.h>
CAMLprim value ocaml_set_interactive_qos(value unit){
  pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
  setpriority(PRIO_PROCESS,0,-5);
  return Val_unit;
}
CAMLprim value ocaml_set_affinity(value vcore){ (void)vcore; return Val_unit; } // no-op on macOS
#else
#define _GNU_SOURCE
#include <sched.h>
#include <sys/resource.h>
CAMLprim value ocaml_set_interactive_qos(value unit){ setpriority(PRIO_PROCESS,0,-5); return Val_unit; }
CAMLprim value ocaml_set_affinity(value vcore){
  int core=Int_val(vcore); cpu_set_t set; CPU_ZERO(&set); CPU_SET(core,&set);
  sched_setaffinity(0,sizeof(set),&set); return Val_unit;
}
#endif
