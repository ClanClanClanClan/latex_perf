/**
 * Ultra Fast LaTeX Validator - C Implementation
 * SIMD-optimized pattern matching and file operations
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/fail.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <immintrin.h>  /* For AVX2/SSE instructions */

/* Memory map a file */
value caml_mmap_file(value filename) {
  CAMLparam1(filename);
  CAMLlocal1(bigarray);
  
  const char* path = String_val(filename);
  int fd = open(path, O_RDONLY);
  if (fd < 0) {
    caml_failwith("Cannot open file");
  }
  
  struct stat st;
  if (fstat(fd, &st) < 0) {
    close(fd);
    caml_failwith("Cannot stat file");
  }
  
  if (st.st_size == 0) {
    close(fd);
    /* Return empty bigarray for empty files */
    intnat dims[1] = {0};
    bigarray = caml_ba_alloc(CAML_BA_UINT8 | CAML_BA_C_LAYOUT, 1, NULL, dims);
    CAMLreturn(bigarray);
  }
  
  void* addr = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  
  if (addr == MAP_FAILED) {
    caml_failwith("Cannot mmap file");
  }
  
  /* Create bigarray pointing to mmap'd memory */
  intnat dims[1] = {st.st_size};
  bigarray = caml_ba_alloc(CAML_BA_UINT8 | CAML_BA_C_LAYOUT, 1, addr, dims);
  
  CAMLreturn(bigarray);
}

/* Unmap a file */
value caml_munmap_file(value bigarray) {
  CAMLparam1(bigarray);
  
  void* data = Caml_ba_data_val(bigarray);
  size_t size = Caml_ba_array_val(bigarray)->dim[0];
  
  if (size > 0) {
    munmap(data, size);
  }
  
  CAMLreturn(Val_unit);
}

/* SIMD-optimized string search using AVX2 */
static inline int find_char_avx2(const char* haystack, size_t len, char needle) {
  if (len < 32) {
    /* Fallback for small strings */
    for (size_t i = 0; i < len; i++) {
      if (haystack[i] == needle) return i;
    }
    return -1;
  }
  
  __m256i needle_vec = _mm256_set1_epi8(needle);
  size_t i;
  
  /* Process 32 bytes at a time */
  for (i = 0; i <= len - 32; i += 32) {
    __m256i chunk = _mm256_loadu_si256((__m256i*)(haystack + i));
    __m256i cmp = _mm256_cmpeq_epi8(chunk, needle_vec);
    int mask = _mm256_movemask_epi8(cmp);
    
    if (mask != 0) {
      /* Found a match - find first bit set */
      return i + __builtin_ctz(mask);
    }
  }
  
  /* Handle remaining bytes */
  for (; i < len; i++) {
    if (haystack[i] == needle) return i;
  }
  
  return -1;
}

/* Find pattern using SIMD */
value caml_find_pattern_simd(value bigarray, value start_off, value search_len, value pattern) {
  CAMLparam4(bigarray, start_off, search_len, pattern);
  
  const char* data = (const char*)Caml_ba_data_val(bigarray);
  size_t offset = Int_val(start_off);
  size_t len = Int_val(search_len);
  const char* pat = String_val(pattern);
  
  if (strlen(pat) == 1) {
    /* Single character - use SIMD */
    int pos = find_char_avx2(data + offset, len, pat[0]);
    CAMLreturn(Val_int(pos));
  }
  
  /* Multi-character pattern - use optimized strstr */
  const char* found = memmem(data + offset, len, pat, strlen(pat));
  if (found) {
    CAMLreturn(Val_int(found - (data + offset)));
  } else {
    CAMLreturn(Val_int(-1));
  }
}

/* Count newlines using SIMD */
value caml_count_newlines_simd(value bigarray, value start_off, value search_len) {
  CAMLparam3(bigarray, start_off, search_len);
  
  const char* data = (const char*)Caml_ba_data_val(bigarray);
  size_t offset = Int_val(start_off);
  size_t len = Int_val(search_len);
  
  int count = 0;
  
  if (len >= 32) {
    __m256i newline_vec = _mm256_set1_epi8('\n');
    size_t i;
    
    /* Process 32 bytes at a time */
    for (i = 0; i <= len - 32; i += 32) {
      __m256i chunk = _mm256_loadu_si256((__m256i*)(data + offset + i));
      __m256i cmp = _mm256_cmpeq_epi8(chunk, newline_vec);
      int mask = _mm256_movemask_epi8(cmp);
      count += __builtin_popcount(mask);
    }
    
    /* Handle remaining bytes */
    for (; i < len; i++) {
      if (data[offset + i] == '\n') count++;
    }
  } else {
    /* Small buffer - no SIMD */
    for (size_t i = 0; i < len; i++) {
      if (data[offset + i] == '\n') count++;
    }
  }
  
  CAMLreturn(Val_int(count));
}

/* Fast quote validation - specialized for the slow rule */
value caml_validate_quotes_ultra_fast(value bigarray, value start_off, value search_len) {
  CAMLparam3(bigarray, start_off, search_len);
  CAMLlocal1(result_array);
  
  const char* data = (const char*)Caml_ba_data_val(bigarray);
  size_t offset = Int_val(start_off);
  size_t len = Int_val(search_len);
  
  /* Find all straight quotes and their line numbers */
  int* quote_positions = malloc(len * sizeof(int));  /* Worst case: every char is a quote */
  int* line_numbers = malloc(len * sizeof(int));
  int quote_count = 0;
  int current_line = 1;
  
  size_t pos = 0;
  while (pos < len) {
    char c = data[offset + pos];
    
    if (c == '\n') {
      current_line++;
    } else if (c == '"') {
      quote_positions[quote_count] = offset + pos;
      line_numbers[quote_count] = current_line;
      quote_count++;
    }
    
    pos++;
  }
  
  /* Create OCaml array result */
  result_array = caml_alloc(quote_count * 2, 0);
  for (int i = 0; i < quote_count; i++) {
    Store_field(result_array, i * 2, Val_int(quote_positions[i]));
    Store_field(result_array, i * 2 + 1, Val_int(line_numbers[i]));
  }
  
  free(quote_positions);
  free(line_numbers);
  
  CAMLreturn(result_array);
}