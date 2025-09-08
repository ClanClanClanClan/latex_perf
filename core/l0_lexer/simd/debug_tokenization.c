#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simd_tokenizer.h"

void print_tokens(simd_token_buffer_t *buf, const char* label) {
    printf("\n=== %s TOKENS (%d total) ===\n", label, buf->count);
    for (int i = 0; i < buf->count && i < 20; i++) {
        const char* token_type;
        switch (buf->kinds[i]) {
            case 0: token_type = "ESCAPE"; break;
            case 1: token_type = "BEGIN_GRP"; break;
            case 2: token_type = "END_GRP"; break;
            case 3: token_type = "MATH"; break;
            case 5: token_type = "NEWLINE"; break;
            case 10: token_type = "SPACE"; break;
            case 11: token_type = "LETTER"; break;
            case 14: token_type = "COMMENT"; break;
            default: token_type = "OTHER"; break;
        }
        
        printf("Token %2d: %-10s code=%3d pos=%d-%d line=%d col=%d\n", 
               i, token_type, buf->codes[i], buf->start_pos[i], buf->end_pos[i],
               buf->lines[i], buf->cols[i]);
    }
}

int main() {
    const char *test_input = "\\alpha + \\beta = {x^2 + y^2}";
    size_t input_len = strlen(test_input);
    
    printf("Analyzing tokenization: '%s'\n", test_input);
    printf("Input length: %zu bytes\n", input_len);
    
    // Create buffers
    simd_token_buffer_t *simd_buf = simd_create_buffer(1000);
    simd_token_buffer_t *scalar_buf = simd_create_buffer(1000);
    
    // Run SIMD tokenization
    int simd_tokens = simd_tokenize((const uint8_t*)test_input, input_len, simd_buf);
    
    // Run scalar-only tokenization
    scalar_buf->count = 0;
    int32_t line_num = 1;
    int32_t col_num = 1;
    for (size_t i = 0; i < input_len && scalar_buf->count < scalar_buf->capacity; i++) {
        uint8_t byte = test_input[i];
        if (byte == 0) break;
        
        // Simple scalar tokenization for comparison
        int catcode;
        if (byte == '\\') catcode = 0; // ESCAPE
        else if (byte == '{') catcode = 1; // BEGIN_GRP
        else if (byte == '}') catcode = 2; // END_GRP
        else if (byte == '$') catcode = 3; // MATH
        else if (byte == '\n') catcode = 5; // NEWLINE
        else if (byte == ' ' || byte == '\t') catcode = 10; // SPACE
        else if (byte == '%') catcode = 14; // COMMENT
        else if ((byte >= 'a' && byte <= 'z') || (byte >= 'A' && byte <= 'Z')) catcode = 11; // LETTER
        else catcode = 12; // OTHER
        
        // Handle escape sequences specially
        if (catcode == 0) { // ESCAPE
            int start_pos = i;
            int start_col = col_num;
            
            size_t seq_len = 1;
            while (i + seq_len < input_len) {
                uint8_t next_byte = test_input[i + seq_len];
                if ((next_byte >= 'a' && next_byte <= 'z') || (next_byte >= 'A' && next_byte <= 'Z')) {
                    seq_len++;
                } else {
                    break;
                }
            }
            
            scalar_buf->kinds[scalar_buf->count] = 0; // ESCAPE
            scalar_buf->codes[scalar_buf->count] = 0;
            scalar_buf->start_pos[scalar_buf->count] = start_pos;
            scalar_buf->end_pos[scalar_buf->count] = start_pos + seq_len;
            scalar_buf->lines[scalar_buf->count] = line_num;
            scalar_buf->cols[scalar_buf->count] = start_col;
            scalar_buf->count++;
            
            i += seq_len - 1; // -1 because loop will increment
            col_num += seq_len;
            continue;
        }
        
        // Regular token
        scalar_buf->kinds[scalar_buf->count] = catcode;
        scalar_buf->codes[scalar_buf->count] = byte;
        scalar_buf->start_pos[scalar_buf->count] = i;
        scalar_buf->end_pos[scalar_buf->count] = i + 1;
        scalar_buf->lines[scalar_buf->count] = line_num;
        scalar_buf->cols[scalar_buf->count] = col_num;
        scalar_buf->count++;
        
        if (byte == '\n') {
            line_num++;
            col_num = 1;
        } else {
            col_num++;
        }
    }
    
    printf("\nComparison: SIMD=%d tokens, Scalar=%d tokens\n", simd_tokens, scalar_buf->count);
    
    print_tokens(simd_buf, "SIMD");
    print_tokens(scalar_buf, "SCALAR");
    
    simd_free_buffer(simd_buf);
    simd_free_buffer(scalar_buf);
    return 0;
}