/*
 * Phase C - SIMD FFI Stubs
 * OCaml C interface stubs for SIMD microkernel
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/fail.h>

#include "simd_tokenizer.h"

// Helper function to extract bigarray data pointer
static inline void* bigarray_data_ptr(value v_array) {
    return Caml_ba_data_val(v_array);
}

// Helper function to get bigarray dimension
static inline long bigarray_dim(value v_array) {
    return Caml_ba_array_val(v_array)->dim[0];
}

/*
 * SIMD tokenize stub
 * OCaml signature: input_ba -> input_len -> kinds -> codes -> start_pos -> end_pos -> lines -> cols -> capacity -> int
 */
value simd_tokenize_stub(value v_input, value v_input_len, 
                         value v_kinds, value v_codes, value v_start_pos, value v_end_pos,
                         value v_lines, value v_cols, value v_capacity) {
    CAMLparam5(v_input, v_input_len, v_kinds, v_codes, v_start_pos);
    CAMLxparam4(v_end_pos, v_lines, v_cols, v_capacity);
    CAMLlocal1(result);
    
    // Extract input data
    const uint8_t *input = (const uint8_t*)bigarray_data_ptr(v_input);
    size_t input_len = Int_val(v_input_len);
    int32_t capacity = Int_val(v_capacity);
    
    // Create SIMD buffer structure
    simd_token_buffer_t output = {
        .kinds = (int32_t*)bigarray_data_ptr(v_kinds),
        .codes = (int32_t*)bigarray_data_ptr(v_codes),
        .start_pos = (int32_t*)bigarray_data_ptr(v_start_pos),
        .end_pos = (int32_t*)bigarray_data_ptr(v_end_pos),
        .lines = (int32_t*)bigarray_data_ptr(v_lines),
        .cols = (int32_t*)bigarray_data_ptr(v_cols),
        .count = 0,
        .capacity = capacity
    };
    
    // Call SIMD tokenizer
    int token_count = simd_tokenize(input, input_len, &output);
    
    result = Val_int(token_count);
    CAMLreturn(result);
}

/*
 * Bytecode stub for simd_tokenize (same implementation)
 */
value simd_tokenize_stub_bytecode(value *argv, int argn) {
    return simd_tokenize_stub(argv[0], argv[1], argv[2], argv[3], argv[4], 
                              argv[5], argv[6], argv[7], argv[8]);
}

/*
 * SIMD vs Scalar benchmark stub
 * Compare SIMD and scalar performance
 */
value simd_vs_scalar_benchmark_stub(value v_input, value v_input_len,
                                    value v_simd_kinds, value v_simd_codes, value v_simd_start, 
                                    value v_simd_end, value v_simd_lines, value v_simd_cols,
                                    value v_scalar_kinds, value v_scalar_codes, value v_scalar_start,
                                    value v_scalar_end, value v_scalar_lines, value v_scalar_cols,
                                    value v_capacity) {
    CAMLparam5(v_input, v_input_len, v_simd_kinds, v_simd_codes, v_simd_start);
    CAMLxparam5(v_simd_end, v_simd_lines, v_simd_cols, v_scalar_kinds, v_scalar_codes);
    CAMLxparam5(v_scalar_start, v_scalar_end, v_scalar_lines, v_scalar_cols, v_capacity);
    CAMLlocal1(result);
    
    // Extract input data
    const uint8_t *input = (const uint8_t*)bigarray_data_ptr(v_input);
    size_t input_len = Int_val(v_input_len);
    int32_t capacity = Int_val(v_capacity);
    
    // Create SIMD buffer
    simd_token_buffer_t simd_output = {
        .kinds = (int32_t*)bigarray_data_ptr(v_simd_kinds),
        .codes = (int32_t*)bigarray_data_ptr(v_simd_codes),
        .start_pos = (int32_t*)bigarray_data_ptr(v_simd_start),
        .end_pos = (int32_t*)bigarray_data_ptr(v_simd_end),
        .lines = (int32_t*)bigarray_data_ptr(v_simd_lines),
        .cols = (int32_t*)bigarray_data_ptr(v_simd_cols),
        .count = 0,
        .capacity = capacity
    };
    
    // Create scalar buffer
    simd_token_buffer_t scalar_output = {
        .kinds = (int32_t*)bigarray_data_ptr(v_scalar_kinds),
        .codes = (int32_t*)bigarray_data_ptr(v_scalar_codes),
        .start_pos = (int32_t*)bigarray_data_ptr(v_scalar_start),
        .end_pos = (int32_t*)bigarray_data_ptr(v_scalar_end),
        .lines = (int32_t*)bigarray_data_ptr(v_scalar_lines),
        .cols = (int32_t*)bigarray_data_ptr(v_scalar_cols),
        .count = 0,
        .capacity = capacity
    };
    
    // Run benchmark
    int diff = simd_vs_scalar_benchmark(input, input_len, &simd_output, &scalar_output);
    
    result = Val_int(diff);
    CAMLreturn(result);
}

/*
 * Bytecode stub for benchmark
 */
value simd_vs_scalar_benchmark_stub_bytecode(value *argv, int argn) {
    return simd_vs_scalar_benchmark_stub(argv[0], argv[1], argv[2], argv[3], argv[4],
                                         argv[5], argv[6], argv[7], argv[8], argv[9],
                                         argv[10], argv[11], argv[12], argv[13], argv[14]);
}

/*
 * Get SIMD architecture information
 */
value simd_get_architecture_stub(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(result);
    
    const char* arch_name;
    
#ifdef USE_AVX2
    arch_name = "AVX2";
#elif defined(USE_NEON)
    arch_name = "NEON";
#else
    arch_name = "Scalar";
#endif
    
    result = caml_copy_string(arch_name);
    CAMLreturn(result);
}

/*
 * Get SIMD width information
 */
value simd_get_width_stub(value unit) {
    CAMLparam1(unit);
    
    int width;
    
#ifdef USE_AVX2
    width = 32;
#elif defined(USE_NEON)
    width = 16;
#else
    width = 1;
#endif
    
    CAMLreturn(Val_int(width));
}