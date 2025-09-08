#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simd_tokenizer.h"

int main() {
    const char *test_input = "\\alpha + \\beta = {x + y}";
    size_t input_len = strlen(test_input);
    
    simd_token_buffer_t *buf = simd_create_buffer(1000);
    if (!buf) { printf("Failed to create buffer\n"); return 1; }
    
    int tokens = simd_tokenize((const uint8_t*)test_input, input_len, buf);
    printf("SIMD Tokenizer Test:\n");
    printf("Architecture: NEON\n");
    printf("Input: %s\n", test_input);
    printf("Tokens generated: %d\n", tokens);
    
    for (int i = 0; i < tokens && i < 10; i++) {
        printf("Token %d: kind=%d, code=%d, pos=%d-%d\n", 
               i, buf->kinds[i], buf->codes[i], 
               buf->start_pos[i], buf->end_pos[i]);
    }
    
    simd_free_buffer(buf);
    return 0;
}
