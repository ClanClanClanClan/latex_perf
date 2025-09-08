#define _GNU_SOURCE
#include <time.h>
#include <stdint.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

static int64_t now_ns_mono(void){
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}
CAMLprim value ocaml_clock_monotonic_ns(value unit){
  return caml_copy_int64(now_ns_mono());
}