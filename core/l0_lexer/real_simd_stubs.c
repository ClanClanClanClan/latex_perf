/*
 * Real SIMD tokenizer stub - connects to actual SIMD implementation
 * This properly links to the tokenize_bytes_into_soa_simd function
 */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/bigarray.h>
#include <stdint.h>
#include <string.h>

// External SIMD tokenizer from simd_tokenizer_fixed.c
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
 * OCaml stub that properly calls the real SIMD tokenizer
 * Signature: bytes -> int -> (int * int * int) array
 */
CAMLprim value real_simd_tokenize_stub(value v_input, value v_max_tokens) {
    CAMLparam2(v_input, v_max_tokens);
    CAMLlocal2(result, tuple);
    
    const uint8_t* input = (const uint8_t*)Bytes_val(v_input);
    int input_len = caml_string_length(v_input);
    int max_tokens = Int_val(v_max_tokens);
    
    // Allocate arrays for SIMD tokenizer output
    int32_t* kinds = (int32_t*)malloc(max_tokens * sizeof(int32_t));
    int32_t* codes = (int32_t*)malloc(max_tokens * sizeof(int32_t));
    int32_t* start_pos = (int32_t*)malloc(max_tokens * sizeof(int32_t));
    int32_t* end_pos = (int32_t*)malloc(max_tokens * sizeof(int32_t));
    int32_t* lines = (int32_t*)malloc(max_tokens * sizeof(int32_t));
    int32_t* cols = (int32_t*)malloc(max_tokens * sizeof(int32_t));
    
    if (!kinds || !codes || !start_pos || !end_pos || !lines || !cols) {
        if (kinds) free(kinds);
        if (codes) free(codes);
        if (start_pos) free(start_pos);
        if (end_pos) free(end_pos);
        if (lines) free(lines);
        if (cols) free(cols);
        caml_failwith("Memory allocation failed");
    }
    
    // Call the REAL SIMD tokenizer
    int token_count = tokenize_bytes_into_soa_simd(
        input, input_len,
        kinds, codes, start_pos, end_pos, lines, cols,
        max_tokens
    );
    
    if (token_count < 0) {
        free(kinds); free(codes); free(start_pos);
        free(end_pos); free(lines); free(cols);
        caml_failwith("SIMD tokenization failed");
    }
    
    // Create OCaml array of tuples (kind, start_pos, end_pos)
    result = caml_alloc(token_count, 0);
    for (int i = 0; i < token_count; i++) {
        tuple = caml_alloc(3, 0);
        Store_field(tuple, 0, Val_int(kinds[i]));
        Store_field(tuple, 1, Val_int(start_pos[i]));
        Store_field(tuple, 2, Val_int(end_pos[i] - 1)); // Convert to inclusive end
        Store_field(result, i, tuple);
    }
    
    free(kinds); free(codes); free(start_pos);
    free(end_pos); free(lines); free(cols);
    
    CAMLreturn(result);
}