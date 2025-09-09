/*
 * Scalar fallback implementation when SIMD is not available
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>

// Simple scalar tokenizer fallback
int tokenize_bytes_into_soa_simd(
    const uint8_t *input,
    size_t input_len,
    int32_t *kinds,
    int32_t *codes,
    int32_t *start_pos,
    int32_t *end_pos,
    int32_t *lines,
    int32_t *cols,
    int max_tokens
) {
    // Basic whitespace tokenizer
    int token_count = 0;
    size_t i = 0;
    int line = 1, col = 1;
    
    while (i < input_len && token_count < max_tokens) {
        // Skip whitespace
        while (i < input_len && (input[i] == ' ' || input[i] == '\t' || 
                                input[i] == '\n' || input[i] == '\r')) {
            if (input[i] == '\n') { line++; col = 1; } else { col++; }
            i++;
        }
        
        if (i >= input_len) break;
        
        // Record token
        start_pos[token_count] = i;
        lines[token_count] = line;
        cols[token_count] = col;
        
        // Find token end
        while (i < input_len && !(input[i] == ' ' || input[i] == '\t' || 
                                 input[i] == '\n' || input[i] == '\r')) {
            col++; i++;
        }
        
        end_pos[token_count] = i;
        kinds[token_count] = 12; // TEXT token
        codes[token_count] = input[start_pos[token_count]]; // First char
        token_count++;
    }
    
    return token_count;
}

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/bigarray.h>

// Forward declaration
value tokenize_bytes_into_soa_simd_stub(
    value v_input, value v_input_len,
    value v_kinds, value v_codes, value v_start_pos, value v_end_pos,
    value v_lines, value v_cols, value v_max_tokens);

// OCaml stub bytecode entry
value tokenize_bytes_into_soa_simd_stub_bytecode(value* argv, int argn) {
    return tokenize_bytes_into_soa_simd_stub(argv[0], argv[1], argv[2], argv[3], 
                                           argv[4], argv[5], argv[6], argv[7], argv[8]);
}

// OCaml stub main implementation
value tokenize_bytes_into_soa_simd_stub(
    value v_input, value v_input_len,
    value v_kinds, value v_codes, value v_start_pos, value v_end_pos,
    value v_lines, value v_cols, value v_max_tokens)
{
    CAMLparam5(v_input, v_input_len, v_kinds, v_codes, v_start_pos);
    CAMLxparam4(v_end_pos, v_lines, v_cols, v_max_tokens);
    
    const uint8_t *input = (const uint8_t*)Caml_ba_data_val(v_input);
    size_t input_len = Int_val(v_input_len);
    int32_t *kinds = (int32_t*)Caml_ba_data_val(v_kinds);
    int32_t *codes = (int32_t*)Caml_ba_data_val(v_codes);  
    int32_t *start_pos = (int32_t*)Caml_ba_data_val(v_start_pos);
    int32_t *end_pos = (int32_t*)Caml_ba_data_val(v_end_pos);
    int32_t *lines = (int32_t*)Caml_ba_data_val(v_lines);
    int32_t *cols = (int32_t*)Caml_ba_data_val(v_cols);
    int max_tokens = Int_val(v_max_tokens);
    
    int result = tokenize_bytes_into_soa_simd(input, input_len, kinds, codes,
                                             start_pos, end_pos, lines, cols, max_tokens);
    
    CAMLreturn(Val_int(result));
}