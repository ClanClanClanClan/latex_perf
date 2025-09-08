#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "simd_tokenizer.h"

int main() {
    printf("=== PHASE C SIMD MICROKERNEL TEST ===\n");
    
    // Test input (LaTeX document fragment)
    const char *test_input = "\\documentclass{article}\n"
                             "\\begin{document}\n" 
                             "Hello \\alpha + \\beta = {x^2 + y^2}\n"
                             "\\end{document}";
    
    size_t input_len = strlen(test_input);
    printf("Input length: %zu bytes\n", input_len);
    printf("Input: %s\n\n", test_input);
    
    // Create buffer for tokenization
    simd_token_buffer_t *buf = simd_create_buffer(1000);
    if (!buf) {
        printf("Failed to create buffer\n");
        return 1;
    }
    
    // Time the tokenization
    clock_t start = clock();
    int tokens = simd_tokenize((const uint8_t*)test_input, input_len, buf);
    clock_t end = clock();
    
    double time_ms = ((double)(end - start)) / CLOCKS_PER_SEC * 1000.0;
    
    printf("=== SIMD TOKENIZATION RESULTS ===\n");
#ifdef USE_NEON
    printf("SIMD Architecture: NEON (ARM64)\n");
#elif defined(USE_AVX2)
    printf("SIMD Architecture: AVX2 (x86_64)\n");
#else
    printf("SIMD Architecture: Scalar fallback\n");
#endif
    printf("Tokens generated: %d\n", tokens);
    printf("Time taken: %.6f ms\n", time_ms);
    printf("\nFirst 10 tokens:\n");
    
    for (int i = 0; i < tokens && i < 10; i++) {
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
    
    // Performance benchmark
    printf("\n=== PERFORMANCE BENCHMARK ===\n");
    int iterations = 10000;
    printf("Running %d iterations...\n", iterations);
    
    start = clock();
    for (int i = 0; i < iterations; i++) {
        buf->count = 0;
        simd_tokenize((const uint8_t*)test_input, input_len, buf);
    }
    end = clock();
    
    double total_time = ((double)(end - start)) / CLOCKS_PER_SEC * 1000.0;
    double avg_time = total_time / iterations;
    
    printf("Total time: %.3f ms\n", total_time);
    printf("Average time: %.6f ms per tokenization\n", avg_time);
    printf("Throughput: %.1f tokenizations/second\n", 1000.0 / avg_time);
    
    // Test SIMD vs Scalar comparison if available
    simd_token_buffer_t *scalar_buf = simd_create_buffer(1000);
    if (scalar_buf) {
        printf("\n=== SIMD VS SCALAR COMPARISON ===\n");
        
        int diff = simd_vs_scalar_benchmark((const uint8_t*)test_input, input_len, buf, scalar_buf);
        printf("Token count difference: %d (should be 0)\n", diff);
        printf("SIMD tokens: %d\n", buf->count);
        printf("Scalar tokens: %d\n", scalar_buf->count);
        
        if (diff == 0) {
            printf("✅ SIMD and scalar results match!\n");
        } else {
            printf("❌ SIMD and scalar results differ!\n");
        }
        
        simd_free_buffer(scalar_buf);
    }
    
    printf("\n=== PHASE C SIMD TEST COMPLETE ===\n");
    
    simd_free_buffer(buf);
    return 0;
}