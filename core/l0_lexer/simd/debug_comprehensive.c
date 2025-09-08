#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simd_tokenizer.h"

int main() {
    // Same input as comprehensive test
    const char *test_input = "\\documentclass{article}\n"
                             "\\begin{document}\n" 
                             "Hello \\alpha + \\beta = {x^2 + y^2}\n"
                             "\\end{document}";
    
    size_t input_len = strlen(test_input);
    printf("Full test input (%zu bytes):\n'%s'\n\n", input_len, test_input);
    
    // Create buffers for comparison  
    simd_token_buffer_t *simd_buf = simd_create_buffer(1000);
    simd_token_buffer_t *scalar_buf = simd_create_buffer(1000);
    
    // Run SIMD vs Scalar benchmark (this calls the internal comparison)
    int diff = simd_vs_scalar_benchmark((const uint8_t*)test_input, input_len, simd_buf, scalar_buf);
    
    printf("Results:\n");
    printf("SIMD tokens: %d\n", simd_buf->count);
    printf("Scalar tokens: %d\n", scalar_buf->count);
    printf("Difference: %d\n", diff);
    
    if (diff != 0) {
        printf("\n=== DETAILED TOKEN COMPARISON ===\n");
        int max_tokens = simd_buf->count > scalar_buf->count ? simd_buf->count : scalar_buf->count;
        
        for (int i = 0; i < max_tokens; i++) {
            printf("Token %2d: ", i);
            
            if (i < simd_buf->count) {
                printf("SIMD(kind=%d,code=%3d,pos=%d-%d) ", 
                       simd_buf->kinds[i], simd_buf->codes[i],
                       simd_buf->start_pos[i], simd_buf->end_pos[i]);
            } else {
                printf("SIMD(---) ");
            }
            
            if (i < scalar_buf->count) {
                printf("SCALAR(kind=%d,code=%3d,pos=%d-%d)", 
                       scalar_buf->kinds[i], scalar_buf->codes[i],
                       scalar_buf->start_pos[i], scalar_buf->end_pos[i]);
            } else {
                printf("SCALAR(---)");
            }
            
            // Mark differences
            if (i < simd_buf->count && i < scalar_buf->count) {
                if (simd_buf->kinds[i] != scalar_buf->kinds[i] || 
                    simd_buf->codes[i] != scalar_buf->codes[i] ||
                    simd_buf->start_pos[i] != scalar_buf->start_pos[i] ||
                    simd_buf->end_pos[i] != scalar_buf->end_pos[i]) {
                    printf(" *** DIFFER ***");
                }
            }
            printf("\n");
        }
    }
    
    simd_free_buffer(simd_buf);
    simd_free_buffer(scalar_buf);
    return 0;
}