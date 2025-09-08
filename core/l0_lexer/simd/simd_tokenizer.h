/*
 * Phase C - SIMD Microkernel Header
 * High-performance vectorized tokenization for LaTeX Perfectionist
 */

#ifndef SIMD_TOKENIZER_H
#define SIMD_TOKENIZER_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// Token types (matching OCaml catcodes)
#define TOK_ESCAPE     0   // \ 
#define TOK_BEGIN_GRP  1   // {
#define TOK_END_GRP    2   // }
#define TOK_MATH       3   // $
#define TOK_NEWLINE    5   // \n
#define TOK_SPACE      10  // space
#define TOK_LETTER     11  // a-z, A-Z
#define TOK_OTHER      12  // default
#define TOK_COMMENT    14  // %

// Output Structure of Arrays (matches OCaml)
typedef struct {
    int32_t *kinds;      // Token types
    int32_t *codes;      // Character codes  
    int32_t *start_pos;  // Start positions
    int32_t *end_pos;    // End positions
    int32_t *lines;      // Line numbers
    int32_t *cols;       // Column numbers
    int32_t count;       // Number of tokens
    int32_t capacity;    // Buffer capacity
} simd_token_buffer_t;

/**
 * Main SIMD tokenization function
 * 
 * @param input     Input byte stream (e.g., mmap'd file)
 * @param input_len Length of input in bytes
 * @param output    Pre-allocated output buffer
 * @return          Number of tokens generated, or -1 on error
 */
int simd_tokenize(const uint8_t *input, size_t input_len, simd_token_buffer_t *output);

/**
 * Performance comparison: SIMD vs Scalar
 * 
 * @param input     Input byte stream
 * @param input_len Length of input
 * @param output1   Buffer for SIMD results
 * @param output2   Buffer for scalar results
 * @return          Difference in token counts (should be 0)
 */
int simd_vs_scalar_benchmark(const uint8_t *input, size_t input_len, 
                             simd_token_buffer_t *output1, 
                             simd_token_buffer_t *output2);

/**
 * OCaml FFI helpers
 */
simd_token_buffer_t* simd_create_buffer(int32_t capacity);
void simd_free_buffer(simd_token_buffer_t *buf);

#ifdef __cplusplus
}
#endif

#endif // SIMD_TOKENIZER_H