// Monotonic clock for macOS/Linux
#define _GNU_SOURCE
#include <time.h>
#include <stdint.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

static int64_t now_ns_mono() {
#ifdef __APPLE__
  // CLOCK_MONOTONIC is fine on macOS 10.12+
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
#else
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
#endif
}

CAMLprim value ocaml_clock_monotonic_ns(value unit) {
  return caml_copy_int64(now_ns_mono());
}
