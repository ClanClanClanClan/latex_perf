/*
 * Tokenizer implementation - simple scalar version for testing
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>

// Simple scalar tokenizer that just splits on whitespace
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
    int token_count = 0;
    size_t i = 0;
    int line = 1;
    int col = 1;
    
    while (i < input_len && token_count < max_tokens) {
        // Skip whitespace
        while (i < input_len && (input[i] == ' ' || input[i] == '\t' || input[i] == '\n' || input[i] == '\r')) {
            if (input[i] == '\n') {
                line++;
                col = 1;
            } else {
                col++;
            }
            i++;
        }
        
        if (i >= input_len) break;
        
        // Start of token
        size_t start = i;
        int start_col = col;
        
        // Find end of token (next whitespace or special char)
        while (i < input_len && input[i] != ' ' && input[i] != '\t' && input[i] != '\n' && input[i] != '\r' && 
               input[i] != '{' && input[i] != '}' && input[i] != '\\' && input[i] != '$' && input[i] != '%') {
            col++;
            i++;
        }
        
        // Handle special single chars
        if (i == start && i < input_len) {
            col++;
            i++;
        }
        
        // Store token
        if (i > start) {
            kinds[token_count] = 1; // Generic token kind
            codes[token_count] = (int32_t)(input[start] | (input[start] << 8)); // Simple hash
            start_pos[token_count] = (int32_t)start;
            end_pos[token_count] = (int32_t)i;
            lines[token_count] = line;
            cols[token_count] = start_col;
            token_count++;
        }
    }
    
    return token_count;
}