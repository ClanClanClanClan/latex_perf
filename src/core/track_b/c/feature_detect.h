/* LaTeX Perfectionist v25 - Track B Feature Detection
 * Runtime detection of CPU features for optimal SIMD dispatch
 */

#ifndef FEATURE_DETECT_H
#define FEATURE_DETECT_H

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/* === CPU FEATURE FLAGS === */

typedef struct {
    /* x86/x64 features */
    bool sse2;
    bool sse4_1;
    bool avx;
    bool avx2;
    bool avx512f;      /* AVX-512 Foundation */
    bool avx512bw;     /* AVX-512 Byte and Word Instructions */
    bool avx512vl;     /* AVX-512 Vector Length Extensions */
    
    /* ARM features */
    bool neon;
    bool sve;          /* Scalable Vector Extension */
    bool sve2;
    
    /* Other features */
    bool bmi1;         /* Bit Manipulation Instructions 1 */
    bool bmi2;         /* Bit Manipulation Instructions 2 */
    bool popcnt;       /* Population Count */
    bool lzcnt;        /* Leading Zero Count */
    
    /* CPU info */
    int cache_line_size;
    int l1_cache_size;
    int l2_cache_size;
    int num_cores;
    
    /* Vendor info */
    char cpu_vendor[16];
    char cpu_brand[64];
} cpu_features_t;

/* === GLOBAL CPU FEATURES === */

/* Global features struct - initialized once at startup */
extern cpu_features_t g_cpu_features;

/* Initialize CPU feature detection */
void cpu_features_init(void);

/* === FEATURE QUERIES === */

/* Check if specific features are available */
static inline bool has_avx2(void) {
    return g_cpu_features.avx2;
}

static inline bool has_avx512(void) {
    return g_cpu_features.avx512f && g_cpu_features.avx512bw;
}

static inline bool has_neon(void) {
    return g_cpu_features.neon;
}

/* Check for optimal SIMD width */
static inline int get_simd_width(void) {
    if (g_cpu_features.avx512f) return 64; /* 512 bits = 64 bytes */
    if (g_cpu_features.avx2) return 32;    /* 256 bits = 32 bytes */
    if (g_cpu_features.sse2) return 16;    /* 128 bits = 16 bytes */
    if (g_cpu_features.neon) return 16;    /* 128 bits = 16 bytes */
    return 8; /* Scalar fallback */
}

/* === ARCHITECTURE DETECTION === */

/* Detect CPU architecture */
typedef enum {
    ARCH_X86,
    ARCH_X86_64,
    ARCH_ARM32,
    ARCH_ARM64,
    ARCH_UNKNOWN
} cpu_arch_t;

cpu_arch_t get_cpu_architecture(void);

/* === PERFORMANCE HINTS === */

/* Get optimal chunk size for lexer processing */
static inline size_t get_optimal_chunk_size(void) {
    /* Base on L1 cache size and SIMD width */
    size_t base = g_cpu_features.l1_cache_size > 0 ? 
                  (size_t)g_cpu_features.l1_cache_size / 4 : 8192;
    
    /* Align to SIMD width */
    int simd_width = get_simd_width();
    return (base / simd_width) * simd_width;
}

/* Check if we should use parallel processing */
static inline bool should_use_parallel(size_t input_size) {
    /* Only use parallel for large inputs with multiple cores */
    return g_cpu_features.num_cores > 1 && input_size > 64 * 1024;
}

/* === RUNTIME DISPATCH HELPERS === */

/* Function pointer types for SIMD dispatch */
typedef void* (*classify_fn_ptr)(const void*, size_t, void*);
typedef void* (*tokenize_fn_ptr)(void*);

/* Get optimal classification function */
classify_fn_ptr get_optimal_classify_fn(void);

/* Get optimal tokenization function */
tokenize_fn_ptr get_optimal_tokenize_fn(void);

/* === DEBUG/TESTING === */

/* Print detected features */
void print_cpu_features(void);

/* Validate feature detection */
bool validate_cpu_features(void);

/* Force enable/disable features for testing */
#ifdef FEATURE_TESTING
void force_enable_feature(const char* feature_name);
void force_disable_feature(const char* feature_name);
void reset_forced_features(void);
#endif

#endif /* FEATURE_DETECT_H */