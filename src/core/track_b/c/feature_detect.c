/* LaTeX Perfectionist v25 - Track B Feature Detection Implementation
 * Runtime detection of CPU features for optimal SIMD dispatch
 */

#include "feature_detect.h"
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __x86_64__
#include <cpuid.h>
#endif

#ifdef __linux__
#include <unistd.h>
#include <sys/auxv.h>
#endif

#ifdef __APPLE__
#include <sys/sysctl.h>
#endif

/* === GLOBAL STATE === */

cpu_features_t g_cpu_features = {0};
static bool g_features_initialized = false;

/* === x86/x64 FEATURE DETECTION === */

#ifdef __x86_64__
static void detect_x86_features(void) {
    unsigned int eax, ebx, ecx, edx;
    
    /* Basic CPUID info */
    if (__get_cpuid(0, &eax, &ebx, &ecx, &edx)) {
        /* Vendor string */
        memcpy(g_cpu_features.cpu_vendor, &ebx, 4);
        memcpy(g_cpu_features.cpu_vendor + 4, &edx, 4);
        memcpy(g_cpu_features.cpu_vendor + 8, &ecx, 4);
        g_cpu_features.cpu_vendor[12] = '\0';
    }
    
    /* Feature flags in CPUID leaf 1 */
    if (__get_cpuid(1, &eax, &ebx, &ecx, &edx)) {
        g_cpu_features.sse2 = (edx & bit_SSE2) != 0;
        g_cpu_features.sse4_1 = (ecx & bit_SSE4_1) != 0;
        g_cpu_features.avx = (ecx & bit_AVX) != 0;
        g_cpu_features.popcnt = (ecx & bit_POPCNT) != 0;
    }
    
    /* Extended features in CPUID leaf 7 */
    if (__get_cpuid_count(7, 0, &eax, &ebx, &ecx, &edx)) {
        g_cpu_features.avx2 = (ebx & bit_AVX2) != 0;
        g_cpu_features.bmi1 = (ebx & bit_BMI1) != 0;
        g_cpu_features.bmi2 = (ebx & bit_BMI2) != 0;
        g_cpu_features.avx512f = (ebx & bit_AVX512F) != 0;
        g_cpu_features.avx512bw = (ebx & bit_AVX512BW) != 0;
        g_cpu_features.avx512vl = (ebx & bit_AVX512VL) != 0;
    }
    
    /* Brand string */
    if (__get_cpuid(0x80000000, &eax, &ebx, &ecx, &edx) && eax >= 0x80000004) {
        char* brand = g_cpu_features.cpu_brand;
        __get_cpuid(0x80000002, (unsigned*)brand, (unsigned*)(brand+4), 
                   (unsigned*)(brand+8), (unsigned*)(brand+12));
        __get_cpuid(0x80000003, (unsigned*)(brand+16), (unsigned*)(brand+20), 
                   (unsigned*)(brand+24), (unsigned*)(brand+28));
        __get_cpuid(0x80000004, (unsigned*)(brand+32), (unsigned*)(brand+36), 
                   (unsigned*)(brand+40), (unsigned*)(brand+44));
        brand[47] = '\0';
    }
}
#endif

/* === ARM FEATURE DETECTION === */

#ifdef __aarch64__
static void detect_arm_features(void) {
    strcpy(g_cpu_features.cpu_vendor, "ARM");
    
    /* Use getauxval on Linux */
#ifdef __linux__
    unsigned long hwcap = getauxval(AT_HWCAP);
    g_cpu_features.neon = (hwcap & HWCAP_ASIMD) != 0;
    
    unsigned long hwcap2 = getauxval(AT_HWCAP2);
    g_cpu_features.sve = (hwcap2 & HWCAP2_SVE) != 0;
    g_cpu_features.sve2 = (hwcap2 & HWCAP2_SVE2) != 0;
#endif

    /* Use sysctl on macOS */
#ifdef __APPLE__
    size_t size = sizeof(int);
    int has_neon = 0;
    if (sysctlbyname("hw.optional.neon", &has_neon, &size, NULL, 0) == 0) {
        g_cpu_features.neon = has_neon;
    }
#endif
}
#endif

/* === CACHE INFO DETECTION === */

static void detect_cache_info(void) {
#ifdef __linux__
    /* Try to read cache info from sysfs */
    FILE* f = fopen("/sys/devices/system/cpu/cpu0/cache/index0/coherency_line_size", "r");
    if (f) {
        fscanf(f, "%d", &g_cpu_features.cache_line_size);
        fclose(f);
    }
    
    f = fopen("/sys/devices/system/cpu/cpu0/cache/index0/size", "r");
    if (f) {
        char size_str[32];
        if (fgets(size_str, sizeof(size_str), f)) {
            g_cpu_features.l1_cache_size = atoi(size_str) * 1024; /* Assume KB */
        }
        fclose(f);
    }
    
    /* Count CPU cores */
    g_cpu_features.num_cores = (int)sysconf(_SC_NPROCESSORS_ONLN);
#endif

#ifdef __APPLE__
    size_t size = sizeof(int);
    sysctlbyname("hw.cachelinesize", &g_cpu_features.cache_line_size, &size, NULL, 0);
    sysctlbyname("hw.l1icachesize", &g_cpu_features.l1_cache_size, &size, NULL, 0);
    sysctlbyname("hw.l2cachesize", &g_cpu_features.l2_cache_size, &size, NULL, 0);
    sysctlbyname("hw.ncpu", &g_cpu_features.num_cores, &size, NULL, 0);
#endif

    /* Fallback defaults */
    if (g_cpu_features.cache_line_size == 0) g_cpu_features.cache_line_size = 64;
    if (g_cpu_features.l1_cache_size == 0) g_cpu_features.l1_cache_size = 32 * 1024;
    if (g_cpu_features.l2_cache_size == 0) g_cpu_features.l2_cache_size = 256 * 1024;
    if (g_cpu_features.num_cores == 0) g_cpu_features.num_cores = 1;
}

/* === MAIN INITIALIZATION === */

void cpu_features_init(void) {
    if (g_features_initialized) return;
    
    memset(&g_cpu_features, 0, sizeof(g_cpu_features));
    
#ifdef __x86_64__
    detect_x86_features();
#endif

#ifdef __aarch64__
    detect_arm_features();
#endif

    detect_cache_info();
    
    g_features_initialized = true;
}

/* === ARCHITECTURE DETECTION === */

cpu_arch_t get_cpu_architecture(void) {
#ifdef __x86_64__
    return ARCH_X86_64;
#elif defined(__i386__)
    return ARCH_X86;
#elif defined(__aarch64__)
    return ARCH_ARM64;
#elif defined(__arm__)
    return ARCH_ARM32;
#else
    return ARCH_UNKNOWN;
#endif
}

/* === RUNTIME DISPATCH === */

/* Forward declarations for SIMD implementations */
extern void* classify_scalar(const void* input, size_t len, void* output);
extern void* tokenize_scalar(void* ctx);

#ifdef HAVE_AVX2
extern void* classify_avx2(const void* input, size_t len, void* output);
extern void* tokenize_avx2(void* ctx);
#endif

#ifdef HAVE_AVX512
extern void* classify_avx512(const void* input, size_t len, void* output);
extern void* tokenize_avx512(void* ctx);
#endif

#ifdef HAVE_NEON
extern void* classify_neon(const void* input, size_t len, void* output);
extern void* tokenize_neon(void* ctx);
#endif

classify_fn_ptr get_optimal_classify_fn(void) {
#ifdef HAVE_AVX512
    if (has_avx512()) return classify_avx512;
#endif
#ifdef HAVE_AVX2
    if (has_avx2()) return classify_avx2;
#endif
#ifdef HAVE_NEON
    if (has_neon()) return classify_neon;
#endif
    return classify_scalar;
}

tokenize_fn_ptr get_optimal_tokenize_fn(void) {
#ifdef HAVE_AVX512
    if (has_avx512()) return tokenize_avx512;
#endif
#ifdef HAVE_AVX2
    if (has_avx2()) return tokenize_avx2;
#endif
#ifdef HAVE_NEON
    if (has_neon()) return tokenize_neon;
#endif
    return tokenize_scalar;
}

/* === DEBUG OUTPUT === */

void print_cpu_features(void) {
    if (!g_features_initialized) cpu_features_init();
    
    printf("CPU Features:\n");
    printf("  Vendor: %s\n", g_cpu_features.cpu_vendor);
    printf("  Brand: %s\n", g_cpu_features.cpu_brand);
    printf("  Architecture: ");
    
    switch (get_cpu_architecture()) {
        case ARCH_X86: printf("x86\n"); break;
        case ARCH_X86_64: printf("x86-64\n"); break;
        case ARCH_ARM32: printf("ARM32\n"); break;
        case ARCH_ARM64: printf("ARM64\n"); break;
        case ARCH_UNKNOWN: printf("Unknown\n"); break;
    }
    
    printf("  Cores: %d\n", g_cpu_features.num_cores);
    printf("  Cache Line: %d bytes\n", g_cpu_features.cache_line_size);
    printf("  L1 Cache: %d KB\n", g_cpu_features.l1_cache_size / 1024);
    printf("  L2 Cache: %d KB\n", g_cpu_features.l2_cache_size / 1024);
    
    printf("  SIMD Features:\n");
    if (g_cpu_features.sse2) printf("    SSE2\n");
    if (g_cpu_features.sse4_1) printf("    SSE4.1\n");
    if (g_cpu_features.avx) printf("    AVX\n");
    if (g_cpu_features.avx2) printf("    AVX2\n");
    if (g_cpu_features.avx512f) printf("    AVX-512F\n");
    if (g_cpu_features.avx512bw) printf("    AVX-512BW\n");
    if (g_cpu_features.neon) printf("    NEON\n");
    if (g_cpu_features.sve) printf("    SVE\n");
    
    printf("  Other Features:\n");
    if (g_cpu_features.bmi1) printf("    BMI1\n");
    if (g_cpu_features.bmi2) printf("    BMI2\n");
    if (g_cpu_features.popcnt) printf("    POPCNT\n");
    
    printf("  Optimal SIMD Width: %d bytes\n", get_simd_width());
    printf("  Optimal Chunk Size: %zu bytes\n", get_optimal_chunk_size());
}

bool validate_cpu_features(void) {
    if (!g_features_initialized) cpu_features_init();
    
    /* Basic sanity checks */
    if (g_cpu_features.num_cores <= 0 || g_cpu_features.num_cores > 256) {
        return false;
    }
    
    if (g_cpu_features.cache_line_size <= 0 || g_cpu_features.cache_line_size > 1024) {
        return false;
    }
    
    /* Architecture-specific checks */
    cpu_arch_t arch = get_cpu_architecture();
    if (arch == ARCH_UNKNOWN) {
        return false;
    }
    
#ifdef __x86_64__
    /* x86-64 should always have SSE2 */
    if (!g_cpu_features.sse2) {
        return false;
    }
#endif
    
    return true;
}

/* === TESTING SUPPORT === */

#ifdef FEATURE_TESTING
static bool g_forced_features = false;
static cpu_features_t g_original_features;

void force_enable_feature(const char* feature_name) {
    if (!g_forced_features) {
        g_original_features = g_cpu_features;
        g_forced_features = true;
    }
    
    if (strcmp(feature_name, "avx2") == 0) {
        g_cpu_features.avx2 = true;
        g_cpu_features.avx = true; /* AVX2 implies AVX */
        g_cpu_features.sse2 = true; /* AVX implies SSE2 */
    } else if (strcmp(feature_name, "avx512") == 0) {
        g_cpu_features.avx512f = true;
        g_cpu_features.avx512bw = true;
        g_cpu_features.avx2 = true;
        g_cpu_features.avx = true;
        g_cpu_features.sse2 = true;
    } else if (strcmp(feature_name, "neon") == 0) {
        g_cpu_features.neon = true;
    }
}

void force_disable_feature(const char* feature_name) {
    if (!g_forced_features) {
        g_original_features = g_cpu_features;
        g_forced_features = true;
    }
    
    if (strcmp(feature_name, "avx2") == 0) {
        g_cpu_features.avx2 = false;
    } else if (strcmp(feature_name, "avx512") == 0) {
        g_cpu_features.avx512f = false;
        g_cpu_features.avx512bw = false;
    } else if (strcmp(feature_name, "neon") == 0) {
        g_cpu_features.neon = false;
    }
}

void reset_forced_features(void) {
    if (g_forced_features) {
        g_cpu_features = g_original_features;
        g_forced_features = false;
    }
}
#endif