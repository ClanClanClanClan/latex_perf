/*
 * Phase C - FIXED SIMD Tokenizer for LaTeX Perfectionist
 * Corrected implementation that produces identical results to scalar
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdatomic.h>

#ifdef __aarch64__
#include <arm_neon.h>
#define USE_NEON
#endif

// Token types (matching OCaml catcodes)
#define TOK_ESCAPE     0   // backslash
#define TOK_BEGIN_GRP  1   // {
#define TOK_END_GRP    2   // }
#define TOK_MATH       3   // $
#define TOK_NEWLINE    5   // \n
#define TOK_SPACE      10  // space
#define TOK_LETTER     11  // a-z, A-Z
#define TOK_OTHER      12  // default
#define TOK_COMMENT    14  // %

// SIMD Attestation: Atomic counters for audit verification
static _Atomic uint64_t simd_neon_scans_performed = 0;
static _Atomic uint64_t scalar_bytes_processed = 0;
static _Atomic uint64_t total_tokenize_calls = 0;

// Forward declaration for NEON scanning function
#ifdef USE_NEON
static size_t find_next_special_neon(const uint8_t *input, size_t start, size_t len);
#endif

// Direct tokenization into OCaml bigarrays
// This matches the exact signature needed for production
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
    // SIMD Attestation: Record total tokenization calls
    atomic_fetch_add(&total_tokenize_calls, 1);
    
    // Initialize catcode lookup table
    static uint8_t catcode_table[256];
    static bool table_initialized = false;
    
    if (!table_initialized) {
        memset(catcode_table, TOK_OTHER, 256);
        catcode_table['\\'] = TOK_ESCAPE;
        catcode_table['{'] = TOK_BEGIN_GRP;
        catcode_table['}'] = TOK_END_GRP;
        catcode_table['$'] = TOK_MATH;
        catcode_table['\n'] = TOK_NEWLINE;
        catcode_table[' '] = TOK_SPACE;
        catcode_table['\t'] = TOK_SPACE;
        catcode_table['%'] = TOK_COMMENT;
        
        for (int i = 'a'; i <= 'z'; i++) catcode_table[i] = TOK_LETTER;
        for (int i = 'A'; i <= 'Z'; i++) catcode_table[i] = TOK_LETTER;
        
        table_initialized = true;
    }
    
    int token_count = 0;
    size_t pos = 0;
    int32_t line_num = 1;
    int32_t col_num = 1;
    
#ifdef USE_NEON
    // NEON-accelerated processing: use vectorized scanning to find special characters
    while (pos < input_len && token_count < max_tokens) {
        // Find next special character using NEON
        size_t next_special = find_next_special_neon(input, pos, input_len);

        // SIMD Attestation: Record NEON scan performed
        atomic_fetch_add(&simd_neon_scans_performed, 1);

        // Process regular characters between current position and next special character
        while (pos < next_special && token_count < max_tokens) {
            uint8_t byte = input[pos];
            if (byte == 0) break;

            int catcode = catcode_table[byte];

            // Handle regular non-special characters more efficiently
            if (catcode != TOK_ESCAPE && catcode != TOK_BEGIN_GRP && catcode != TOK_END_GRP &&
                catcode != TOK_MATH && catcode != TOK_COMMENT && catcode != TOK_NEWLINE) {

                // Regular token (letter, space, other)
                if (token_count < max_tokens) {
                    kinds[token_count] = catcode;
                    codes[token_count] = byte;
                    start_pos[token_count] = pos;
                    end_pos[token_count] = pos + 1;
                    lines[token_count] = line_num;
                    cols[token_count] = col_num;
                    token_count++;
                }
                pos++;
                col_num++;
                continue;
            }

            // If we hit a special character before reaching next_special, break to handle it
            break;
        }

        // Handle the special character found by NEON scanning
        if (pos < input_len && token_count < max_tokens) {
            uint8_t byte = input[pos];
            if (byte == 0) break;

            int catcode = catcode_table[byte];
#else
    // Fallback scalar processing for non-NEON platforms
    // SIMD Attestation: Record scalar processing
    atomic_fetch_add(&scalar_bytes_processed, input_len);

    while (pos < input_len && token_count < max_tokens) {
        uint8_t byte = input[pos];
        if (byte == 0) break;
        
        int catcode = catcode_table[byte];
#endif
        
        switch (catcode) {
        case TOK_ESCAPE: {
            // Handle escape sequence
            size_t start = pos;
            int32_t start_col = col_num;
            pos++;
            col_num++;
            
            // Consume following letters
            while (pos < input_len) {
                uint8_t c = input[pos];
                if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
                    pos++;
                    col_num++;
                } else {
                    break;
                }
            }
            
            // Store escape token
            if (token_count < max_tokens) {
                kinds[token_count] = TOK_ESCAPE;
                codes[token_count] = 0; // Control sequence marker
                start_pos[token_count] = start;
                end_pos[token_count] = pos;
                lines[token_count] = line_num;
                cols[token_count] = start_col;
                token_count++;
            }
            break;
        }
        
        case TOK_COMMENT: {
            // Skip comment to end of line
            pos++;
            col_num++;
            while (pos < input_len && input[pos] != '\n') {
                pos++;
                col_num++;
            }
            break;
        }
        
        case TOK_NEWLINE: {
            // Store newline token
            if (token_count < max_tokens) {
                kinds[token_count] = catcode;
                codes[token_count] = byte;
                start_pos[token_count] = pos;
                end_pos[token_count] = pos + 1;
                lines[token_count] = line_num;
                cols[token_count] = col_num;
                token_count++;
            }
            pos++;
            line_num++;
            col_num = 1;
            break;
        }
        
        default: {
            // Regular token
            if (token_count < max_tokens) {
                kinds[token_count] = catcode;
                codes[token_count] = byte;
                start_pos[token_count] = pos;
                end_pos[token_count] = pos + 1;
                lines[token_count] = line_num;
                cols[token_count] = col_num;
                token_count++;
            }
            pos++;
            col_num++;
            break;
        }
        }
#ifdef USE_NEON
        }
#endif
    }

    return token_count;
}

#ifdef USE_NEON
// NEON-accelerated scanning for specific characters
// This can be used to quickly find the next interesting character
static size_t find_next_special_neon(const uint8_t *input, size_t start, size_t len) {
    if (start >= len) return len;
    
    // Characters we're looking for
    uint8x16_t backslash = vdupq_n_u8('\\');
    uint8x16_t brace_open = vdupq_n_u8('{');
    uint8x16_t brace_close = vdupq_n_u8('}');
    uint8x16_t dollar = vdupq_n_u8('$');
    uint8x16_t newline = vdupq_n_u8('\n');
    uint8x16_t percent = vdupq_n_u8('%');
    
    size_t pos = start;
    
    // Process 16-byte blocks
    while (pos + 16 <= len) {
        uint8x16_t data = vld1q_u8(input + pos);
        
        // Check for any special characters
        uint8x16_t matches = vceqq_u8(data, backslash);
        matches = vorrq_u8(matches, vceqq_u8(data, brace_open));
        matches = vorrq_u8(matches, vceqq_u8(data, brace_close));
        matches = vorrq_u8(matches, vceqq_u8(data, dollar));
        matches = vorrq_u8(matches, vceqq_u8(data, newline));
        matches = vorrq_u8(matches, vceqq_u8(data, percent));
        
        // Check if any matches found
        uint64_t mask = vgetq_lane_u64(vreinterpretq_u64_u8(matches), 0) |
                        vgetq_lane_u64(vreinterpretq_u64_u8(matches), 1);
        
        if (mask != 0) {
            // Found a special character, scan byte by byte to find exact position
            for (int i = 0; i < 16; i++) {
                uint8_t c = input[pos + i];
                if (c == '\\' || c == '{' || c == '}' || 
                    c == '$' || c == '\n' || c == '%') {
                    return pos + i;
                }
            }
        }
        
        pos += 16;
    }
    
    // Scan remaining bytes
    while (pos < len) {
        uint8_t c = input[pos];
        if (c == '\\' || c == '{' || c == '}' || 
            c == '$' || c == '\n' || c == '%') {
            return pos;
        }
        pos++;
    }
    
    return len;
}

// Optimized SIMD tokenizer using NEON for scanning
int tokenize_bytes_into_soa_simd_optimized(
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
    // For now, use the scalar version for correctness
    // Once we verify accuracy, we can optimize with NEON scanning
    return tokenize_bytes_into_soa_simd(
        input, input_len, kinds, codes, 
        start_pos, end_pos, lines, cols, max_tokens
    );
}

// SIMD Attestation: OCaml-callable counter access functions
uint64_t simd_get_avx2_blocks_processed(void) {
    return 0;  // Not used in this ARM64/NEON implementation
}

uint64_t simd_get_neon_blocks_processed(void) {
    return atomic_load(&simd_neon_scans_performed);
}

uint64_t simd_get_scalar_bytes_processed(void) {
    return atomic_load(&scalar_bytes_processed);
}

uint64_t simd_get_total_tokenize_calls(void) {
    return atomic_load(&total_tokenize_calls);
}

// SIMD Attestation: Reset counters for fresh testing
void simd_reset_attestation_counters(void) {
    atomic_store(&simd_neon_scans_performed, 0);
    atomic_store(&scalar_bytes_processed, 0);
    atomic_store(&total_tokenize_calls, 0);
}
#endif
