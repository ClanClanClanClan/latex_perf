/* LaTeX Perfectionist v25 - Track B Main Lexer Entry Point
 * High-level API with automatic SIMD dispatch
 */

#include "lexer_types.h"
#include "feature_detect.h"
#include "scalar/lexer_scalar.h"
#include "arena/arena.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* === DISPATCH TABLE === */

static simd_dispatch_t g_dispatch_table[] = {
    /* Will be populated at runtime based on CPU features */
    {NULL, NULL, "uninitialized", false}
};

static bool g_dispatch_initialized = false;

/* === DISPATCH INITIALIZATION === */

/* Forward declarations for SIMD implementations */
#ifdef HAVE_AVX2
#include "simd/lexer_avx2.h"
#endif

#ifdef HAVE_NEON
#include "simd/lexer_neon.h"
#endif

/* Stub implementations for SIMD variants */
static size_t classify_stub(const char* input, size_t len, catcode_t* output) {
    return classify_batch_scalar(input, len, output);
}

static size_t tokenize_stub(lexer_ctx_t* ctx) {
    return lexer_tokenize_scalar(ctx);
}

static void init_dispatch_table(void) {
    if (g_dispatch_initialized) return;
    
    /* Initialize CPU feature detection */
    cpu_features_init();
    
    /* Initialize catcode lookup table */
    catcode_init();
    
    /* Select best implementation based on CPU features */
    simd_dispatch_t* dispatch = &g_dispatch_table[0];
    
#ifdef HAVE_AVX512
    if (has_avx512()) {
        dispatch->classify = (classify_fn_t)classify_stub; /* TODO: implement classify_avx512 */
        dispatch->tokenize = (tokenize_fn_t)tokenize_stub; /* TODO: implement tokenize_avx512 */
        dispatch->name = "AVX-512";
        dispatch->available = true;
        goto dispatch_selected;
    }
#endif

#ifdef HAVE_AVX2
    if (has_avx2()) {
        init_avx2_tables();
        dispatch->classify = (classify_fn_t)classify_chars_avx2;
        dispatch->tokenize = (tokenize_fn_t)tokenize_avx2;
        dispatch->name = "AVX2";
        dispatch->available = true;
        goto dispatch_selected;
    }
#endif

#ifdef HAVE_NEON
    if (has_neon()) {
        init_neon_tables();
        dispatch->classify = (classify_fn_t)classify_chars_neon;
        dispatch->tokenize = (tokenize_fn_t)tokenize_neon;
        dispatch->name = "NEON";
        dispatch->available = true;
        goto dispatch_selected;
    }
#endif

    /* Fallback to scalar implementation */
    dispatch->classify = (classify_fn_t)classify_batch_scalar;
    dispatch->tokenize = (tokenize_fn_t)lexer_tokenize_scalar;
    dispatch->name = "Scalar";
    dispatch->available = true;

dispatch_selected:
    g_dispatch_initialized = true;
    
    /* Print selected implementation */
    if (getenv("LEXER_VERBOSE")) {
        printf("LaTeX Perfectionist Track B: Using %s implementation\n", dispatch->name);
        printf("CPU: %s %s\n", g_cpu_features.cpu_vendor, g_cpu_features.cpu_brand);
        printf("SIMD Width: %d bytes\n", get_simd_width());
        printf("Chunk Size: %zu bytes\n", get_optimal_chunk_size());
    }
}

/* === HIGH-LEVEL API === */

/* Primary lexer entry point - matches OCaml interface */
size_t lexer_tokenize_optimized(const char* input, size_t input_len, 
                               token_t** tokens, size_t* token_count) {
    if (!input || input_len == 0 || !tokens || !token_count) {
        return 0;
    }
    
    /* Initialize dispatch table if needed */
    if (!g_dispatch_initialized) {
        init_dispatch_table();
    }
    
    /* Estimate token count (heuristic: ~1 token per 8 characters) */
    size_t estimated_tokens = input_len / 8 + 100;
    
    /* Create lexer context */
    lexer_ctx_t* ctx = lexer_create(input, input_len, estimated_tokens);
    if (!ctx) {
        return 0;
    }
    
    /* Dispatch to optimal implementation */
    simd_dispatch_t* dispatch = &g_dispatch_table[0];
    size_t result = dispatch->tokenize(ctx);
    
    /* Return results */
    *tokens = ctx->tokens;
    *token_count = ctx->token_count;
    
    /* Note: caller is responsible for calling lexer_cleanup when done */
    return result;
}

/* Cleanup function for lexer resources */
void lexer_cleanup(lexer_ctx_t* ctx) {
    if (ctx) {
        lexer_destroy(ctx);
    }
}

/* === BATCH PROCESSING API === */

/* Process multiple documents efficiently */
typedef struct {
    const char* input;
    size_t input_len;
    token_t* tokens;
    size_t token_count;
    size_t processing_time_ns;
} batch_result_t;

size_t lexer_process_batch(const char** inputs, size_t* input_lens, 
                          size_t batch_size, batch_result_t* results) {
    if (!inputs || !input_lens || !results || batch_size == 0) {
        return 0;
    }
    
    /* Initialize dispatch if needed */
    if (!g_dispatch_initialized) {
        init_dispatch_table();
    }
    
    size_t successful = 0;
    simd_dispatch_t* dispatch = &g_dispatch_table[0];
    
    for (size_t i = 0; i < batch_size; i++) {
        if (!inputs[i] || input_lens[i] == 0) {
            continue;
        }
        
        /* Time the processing */
        struct timespec start, end;
        clock_gettime(CLOCK_MONOTONIC, &start);
        
        /* Process document */
        size_t estimated_tokens = input_lens[i] / 8 + 100;
        lexer_ctx_t* ctx = lexer_create(inputs[i], input_lens[i], estimated_tokens);
        
        if (ctx) {
            size_t token_count = dispatch->tokenize(ctx);
            
            clock_gettime(CLOCK_MONOTONIC, &end);
            
            /* Store results */
            results[i].input = inputs[i];
            results[i].input_len = input_lens[i];
            results[i].tokens = ctx->tokens;
            results[i].token_count = token_count;
            results[i].processing_time_ns = 
                (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                (end.tv_nsec - start.tv_nsec);
            
            successful++;
            
            /* Note: Not destroying context here - caller must call batch cleanup */
        }
    }
    
    return successful;
}

/* === PERFORMANCE ANALYSIS === */

/* Performance measurement for benchmarking */
perf_stats_t lexer_measure_performance(const char* input, size_t input_len, 
                                      size_t iterations) {
    perf_stats_t stats = {0};
    
    if (!input || input_len == 0 || iterations == 0) {
        return stats;
    }
    
    /* Initialize dispatch if needed */
    if (!g_dispatch_initialized) {
        init_dispatch_table();
    }
    
    simd_dispatch_t* dispatch = &g_dispatch_table[0];
    
    /* Detect SIMD availability */
    stats.simd_enabled = strcmp(dispatch->name, "Scalar") != 0;
    
    /* Run benchmark iterations */
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    for (size_t i = 0; i < iterations; i++) {
        size_t estimated_tokens = input_len / 8 + 100;
        lexer_ctx_t* ctx = lexer_create(input, input_len, estimated_tokens);
        
        if (ctx) {
            size_t tokens = dispatch->tokenize(ctx);
            stats.tokens_generated += tokens;
            lexer_destroy(ctx);
        }
    }
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    stats.time_ns = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                    (end.tv_nsec - start.tv_nsec);
    stats.bytes_processed = input_len * iterations;
    
    return stats;
}

/* === DEBUGGING/TESTING === */

/* Get current dispatch info */
const char* lexer_get_implementation_name(void) {
    if (!g_dispatch_initialized) {
        init_dispatch_table();
    }
    return g_dispatch_table[0].name;
}

/* Force a specific implementation (for testing) */
#ifdef LEXER_TESTING
void lexer_force_implementation(const char* impl_name) {
    if (!g_dispatch_initialized) {
        init_dispatch_table();
    }
    
    simd_dispatch_t* dispatch = &g_dispatch_table[0];
    
    if (strcmp(impl_name, "scalar") == 0) {
        dispatch->classify = (classify_fn_t)classify_batch_scalar;
        dispatch->tokenize = (tokenize_fn_t)lexer_tokenize_scalar;
        dispatch->name = "Scalar (forced)";
    }
    /* Add other implementations as they're developed */
}

/* Validate lexer output correctness */
bool lexer_validate_output(const char* input, size_t input_len) {
    if (!input || input_len == 0) return false;
    
    token_t* tokens = NULL;
    size_t token_count = 0;
    
    size_t result = lexer_tokenize_optimized(input, input_len, &tokens, &token_count);
    
    if (result == 0 || !tokens) {
        return false;
    }
    
    /* Basic validation - last token should be EOF */
    if (token_count == 0) {
        return false;
    }
    
    token_t* last_token = &tokens[token_count - 1];
    bool valid = (last_token->type == TOKEN_EOF);
    
    /* Additional validation could go here */
    
    return valid;
}
#endif

/* === INITIALIZATION === */

/* Library initialization - call once at startup */
void lexer_track_b_init(void) {
    init_dispatch_table();
}

/* Library cleanup - call at shutdown */
void lexer_track_b_cleanup(void) {
    /* Currently nothing to clean up */
    /* In future: might clean up SIMD contexts, etc. */
}

/* === SIMPLE C API FOR TESTING === */

/* Simple test function that can be called from command line */
int lexer_test_simple(const char* filename) {
    FILE* f = fopen(filename, "r");
    if (!f) {
        fprintf(stderr, "Error: Cannot open file '%s'\n", filename);
        return 1;
    }
    
    /* Read entire file */
    fseek(f, 0, SEEK_END);
    long file_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    
    char* input = malloc((size_t)file_size + 1);
    if (!input) {
        fclose(f);
        fprintf(stderr, "Error: Out of memory\n");
        return 1;
    }
    
    size_t read_size = fread(input, 1, (size_t)file_size, f);
    input[read_size] = '\0';
    fclose(f);
    
    /* Initialize lexer */
    lexer_track_b_init();
    
    /* Process file */
    printf("Processing file: %s (%zu bytes)\n", filename, read_size);
    printf("Implementation: %s\n", lexer_get_implementation_name());
    
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    
    token_t* tokens = NULL;
    size_t token_count = 0;
    
    size_t result = lexer_tokenize_optimized(input, read_size, &tokens, &token_count);
    
    clock_gettime(CLOCK_MONOTONIC, &end);
    
    uint64_t time_ns = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                       (end.tv_nsec - start.tv_nsec);
    double time_ms = (double)time_ns / 1000000.0;
    
    printf("Results:\n");
    printf("  Tokens generated: %zu\n", token_count);
    printf("  Processing time: %.3f ms\n", time_ms);
    printf("  Throughput: %.1f MB/s\n", (double)read_size / time_ms / 1000.0);
    
    /* Show first few tokens */
    printf("  First 10 tokens:\n");
    for (size_t i = 0; i < token_count && i < 10; i++) {
        token_t* tok = &tokens[i];
        printf("    [%zu] Type=%d Offset=%u Line=%u Col=%u\n", 
               i, tok->type, tok->offset, tok->line, tok->col);
    }
    
    free(input);
    lexer_track_b_cleanup();
    
    return 0;
}