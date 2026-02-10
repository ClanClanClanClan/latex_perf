#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#ifdef __APPLE__
#include <mach/mach.h>
#elif defined(__linux__)
#include <stdio.h>
#include <unistd.h>
#endif

CAMLprim value ocaml_task_meminfo(value unit){
#ifdef __APPLE__
  struct task_basic_info_64 info;
  mach_msg_type_number_t count = TASK_BASIC_INFO_64_COUNT;
  kern_return_t kr = task_info(mach_task_self(), TASK_BASIC_INFO_64,
                               (task_info_t)&info, &count);
  if (kr != KERN_SUCCESS){
    value t = caml_alloc_tuple(2);
    Store_field(t,0, caml_copy_int64(0));
    Store_field(t,1, caml_copy_int64(0));
    return t;
  }
  value t = caml_alloc_tuple(2);
  Store_field(t,0, caml_copy_int64((int64_t)info.resident_size));
  Store_field(t,1, caml_copy_int64((int64_t)info.virtual_size));
  return t;
#elif defined(__linux__)
  /* Read RSS from /proc/self/statm (field 1, in pages) */
  int64_t rss_bytes = 0;
  FILE *f = fopen("/proc/self/statm", "r");
  if (f) {
    long pages = 0, rss_pages = 0;
    if (fscanf(f, "%ld %ld", &pages, &rss_pages) == 2)
      rss_bytes = (int64_t)rss_pages * sysconf(_SC_PAGESIZE);
    fclose(f);
  }
  value t = caml_alloc_tuple(2);
  Store_field(t,0, caml_copy_int64(rss_bytes));
  Store_field(t,1, caml_copy_int64(0));
  return t;
#else
  value t = caml_alloc_tuple(2);
  Store_field(t,0, caml_copy_int64(0));
  Store_field(t,1, caml_copy_int64(0));
  return t;
#endif
}