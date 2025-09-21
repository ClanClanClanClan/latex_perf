/*
 * Phase C - Production OCaml/C Interface Stubs
 * Connects SIMD tokenizer to OCaml production system
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/fail.h>

// External SIMD tokenizer function
extern int tokenize_bytes_into_soa_simd(
    const uint8_t *input,
    size_t input_len,
    int32_t *kinds,
    int32_t *codes,
    int32_t *start_pos,
    int32_t *end_pos,
    int32_t *lines,
    int32_t *cols,
    int max_tokens
);

/*
 * OCaml stub for SIMD tokenization
 * Signature: bytes -> int -> int32 array1 -> ... -> int -> int
 */
value tokenize_bytes_into_soa_simd_stub(
    value v_input,
    value v_input_len,
    value v_kinds,
    value v_codes,
    value v_start_pos,
    value v_end_pos,
    value v_lines,
    value v_cols,
    value v_max_tokens
) {
    CAMLparam5(v_input, v_input_len, v_kinds, v_codes, v_start_pos);
    CAMLxparam4(v_end_pos, v_lines, v_cols, v_max_tokens);
    CAMLlocal1(result);
    
    // Extract input bytes
    const uint8_t *input = (const uint8_t*)Bytes_val(v_input);
    size_t input_len = Int_val(v_input_len);
    int max_tokens = Int_val(v_max_tokens);
    
    // Extract bigarray pointers
    int32_t *kinds = (int32_t*)Caml_ba_data_val(v_kinds);
    int32_t *codes = (int32_t*)Caml_ba_data_val(v_codes);
    int32_t *start_pos = (int32_t*)Caml_ba_data_val(v_start_pos);
    int32_t *end_pos = (int32_t*)Caml_ba_data_val(v_end_pos);
    int32_t *lines = (int32_t*)Caml_ba_data_val(v_lines);
    int32_t *cols = (int32_t*)Caml_ba_data_val(v_cols);
    
    // Call SIMD tokenizer
    int token_count = tokenize_bytes_into_soa_simd(
        input, input_len,
        kinds, codes, start_pos, end_pos, lines, cols,
        max_tokens
    );
    
    result = Val_int(token_count);
    CAMLreturn(result);
}

/*
 * Bytecode version of the stub (for compatibility)
 */
value tokenize_bytes_into_soa_simd_stub_bytecode(value *argv, int argn) {
    return tokenize_bytes_into_soa_simd_stub(
        argv[0], argv[1], argv[2], argv[3], argv[4],
        argv[5], argv[6], argv[7], argv[8]
    );
}