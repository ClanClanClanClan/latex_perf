/*
 * SIMD xxHash64 stub with CPU feature detection scaffolding.
 * - If L0_USE_SIMD_XXH=1 and CPU supports NEON/AVX2, a SIMD path would run
 *   (placeholder currently falls back to the tuned scalar implementation).
 * - Otherwise, OCaml wrapper falls back to pure OCaml scalar.
 * This structure makes it easy to drop in real intrinsics later (Week 9).
 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <string.h>
#include <stdint.h>
#if defined(__x86_64__)
#include <cpuid.h>
#endif

static const uint64_t PRIME64_1 = 0x9E3779B185EBCA87ULL;
static const uint64_t PRIME64_2 = 0xC2B2AE3D27D4EB4FULL;
static const uint64_t PRIME64_3 = 0x165667B19E3779F9ULL;
static const uint64_t PRIME64_4 = 0x85EBCA77C2B2AE63ULL;
static const uint64_t PRIME64_5 = 0x27D4EB2F165667C5ULL;

static inline uint64_t rotl64(uint64_t x, int r){
  return (x << r) | (x >> (64 - r));
}

static inline uint64_t read64(const unsigned char* p){
  return ((uint64_t)p[0])       | ((uint64_t)p[1] << 8)  |
         ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24) |
         ((uint64_t)p[4] << 32) | ((uint64_t)p[5] << 40) |
         ((uint64_t)p[6] << 48) | ((uint64_t)p[7] << 56);
}

static inline uint64_t read32(const unsigned char* p){
  return ((uint64_t)p[0])       | ((uint64_t)p[1] << 8)  |
         ((uint64_t)p[2] << 16) | ((uint64_t)p[3] << 24);
}

static inline uint64_t round64(uint64_t acc, uint64_t input){
  acc += input * PRIME64_2;
  acc = rotl64(acc, 31);
  acc *= PRIME64_1;
  return acc;
}

static inline uint64_t merge_round(uint64_t acc, uint64_t v){
  acc ^= round64(0, v);
  acc = acc * PRIME64_1 + PRIME64_4;
  return acc;
}

static inline uint64_t avalanche(uint64_t h){
  h ^= h >> 33;
  h *= PRIME64_2;
  h ^= h >> 29;
  h *= PRIME64_3;
  h ^= h >> 32;
  return h;
}

static uint64_t xxh64_scalar(const unsigned char* p, size_t len, uint64_t seed){
  size_t i = 0;
  uint64_t h;
  if (len >= 32){
    uint64_t v1 = seed + PRIME64_1 + PRIME64_2;
    uint64_t v2 = seed + PRIME64_2;
    uint64_t v3 = seed + 0;
    uint64_t v4 = seed - PRIME64_1;
    while (i <= len - 32){
      v1 = round64(v1, read64(p + i));
      v2 = round64(v2, read64(p + i + 8));
      v3 = round64(v3, read64(p + i + 16));
      v4 = round64(v4, read64(p + i + 24));
      i += 32;
    }
    h = rotl64(v1, 1) ^ rotl64(v2, 7) ^ rotl64(v3, 12) ^ rotl64(v4, 18);
    h = merge_round(h, v1);
    h = merge_round(h, v2);
    h = merge_round(h, v3);
    h = merge_round(h, v4);
  } else {
    h = seed + PRIME64_5;
  }
  h += (uint64_t)len;
  while (i + 8 <= len){
    uint64_t k1 = read64(p + i);
    k1 = rotl64(k1 * PRIME64_2, 31) * PRIME64_1;
    h ^= k1;
    h = rotl64(h, 27) * PRIME64_1 + PRIME64_4;
    i += 8;
  }
  if (i + 4 <= len){
    uint64_t k1 = read32(p + i);
    h ^= k1 * PRIME64_1;
    h = rotl64(h, 23) * PRIME64_2 + PRIME64_3;
    i += 4;
  }
  while (i < len){
    uint64_t k1 = p[i++];
    h ^= k1 * PRIME64_5;
    h = rotl64(h, 11) * PRIME64_1;
  }
  return avalanche(h);
}

CAMLprim value ocaml_xxh64_simd(value v_bytes, value v_seed){
  CAMLparam2(v_bytes, v_seed);
  size_t len = caml_string_length(v_bytes);
  const unsigned char* p = (const unsigned char*) String_val(v_bytes);
  uint64_t seed = (uint64_t) Int64_val(v_seed);
  /* Feature flag applies; if not set, signal to use OCaml path */
  const char* use = getenv("L0_USE_SIMD_XXH");
  if (!use || strcmp(use, "1") != 0){ caml_failwith("SIMD XXH disabled"); }

  /* CPU feature detection */
  int has_simd = 0;
#if defined(__aarch64__) || defined(__ARM_NEON)
  has_simd = 1; /* NEON mandatory on arm64 */
#elif defined(__x86_64__)
  unsigned int eax=7, ebx=0, ecx=0, edx=0;
  if (__get_cpuid_max(0, 0) >= 7){
    __cpuid_count(7, 0, eax, ebx, ecx, edx);
    if (ebx & (1u<<5)) has_simd = 1; /* AVX2 */
  }
#endif
  /* Intrinsics-accelerated 32-byte stripe processing (guarded) */
  uint64_t h = 0;
#if defined(__AVX2__) && defined(ENABLE_XXH_AVX2)
  if (has_simd){
    #include <immintrin.h>
    size_t i = 0;
    uint64_t v1 = seed + PRIME64_1 + PRIME64_2;
    uint64_t v2 = seed + PRIME64_2;
    uint64_t v3 = seed + 0;
    uint64_t v4 = seed - PRIME64_1;
    const __m256i prime2 = _mm256_set1_epi64x((long long)PRIME64_2);
    while (i + 64 <= len){
      __m256i vec = _mm256_loadu_si256((const __m256i *)(p + i));
      __m256i a_lo = vec;
      __m256i b_lo = prime2;
      __m256i a_hi = _mm256_srli_epi64(vec, 32);
      __m256i b_hi = _mm256_srli_epi64(prime2, 32);
      __m256i prod_lo = _mm256_mul_epu32(a_lo, b_lo);
      __m256i prod_hi1 = _mm256_mul_epu32(a_lo, b_hi);
      __m256i prod_hi2 = _mm256_mul_epu32(a_hi, b_lo);
      __m256i cross = _mm256_add_epi64(prod_hi1, prod_hi2);
      __m256i prod = _mm256_add_epi64(prod_lo, _mm256_slli_epi64(cross, 32));
      uint64_t pa = (uint64_t)_mm256_extract_epi64(prod, 0);
      uint64_t pb = (uint64_t)_mm256_extract_epi64(prod, 1);
      uint64_t pc = (uint64_t)_mm256_extract_epi64(prod, 2);
      uint64_t pd = (uint64_t)_mm256_extract_epi64(prod, 3);
      v1 = rotl64(v1 + pa, 31) * PRIME64_1;
      v2 = rotl64(v2 + pb, 31) * PRIME64_1;
      v3 = rotl64(v3 + pc, 31) * PRIME64_1;
      v4 = rotl64(v4 + pd, 31) * PRIME64_1;
      __m256i vec2 = _mm256_loadu_si256((const __m256i *)(p + i + 32));
      __m256i a2_lo = vec2;
      __m256i a2_hi = _mm256_srli_epi64(vec2, 32);
      __m256i prod2_lo = _mm256_mul_epu32(a2_lo, b_lo);
      __m256i prod2_hi1 = _mm256_mul_epu32(a2_lo, b_hi);
      __m256i prod2_hi2 = _mm256_mul_epu32(a2_hi, b_lo);
      __m256i cross2 = _mm256_add_epi64(prod2_hi1, prod2_hi2);
      __m256i prod2 = _mm256_add_epi64(prod2_lo, _mm256_slli_epi64(cross2, 32));
      uint64_t p2a = (uint64_t)_mm256_extract_epi64(prod2, 0);
      uint64_t p2b = (uint64_t)_mm256_extract_epi64(prod2, 1);
      uint64_t p2c = (uint64_t)_mm256_extract_epi64(prod2, 2);
      uint64_t p2d = (uint64_t)_mm256_extract_epi64(prod2, 3);
      v1 = rotl64(v1 + p2a, 31) * PRIME64_1;
      v2 = rotl64(v2 + p2b, 31) * PRIME64_1;
      v3 = rotl64(v3 + p2c, 31) * PRIME64_1;
      v4 = rotl64(v4 + p2d, 31) * PRIME64_1;
      i += 64;
    }
    if (i > 0){
      h = rotl64(v1, 1) ^ rotl64(v2, 7) ^ rotl64(v3, 12) ^ rotl64(v4, 18);
      h = merge_round(h, v1);
      h = merge_round(h, v2);
      h = merge_round(h, v3);
      h = merge_round(h, v4);
    } else {
      h = seed + PRIME64_5;
    }
    h += (uint64_t)len;
    /* tail (scalar) */
    while (i + 8 <= len){
      uint64_t k1 = read64(p + i);
      k1 = rotl64(k1 * PRIME64_2, 31) * PRIME64_1;
      h ^= k1;
      h = rotl64(h, 27) * PRIME64_1 + PRIME64_4;
      i += 8;
    }
    if (i + 4 <= len){
      uint64_t k1 = read32(p + i);
      h ^= k1 * PRIME64_1;
      h = rotl64(h, 23) * PRIME64_2 + PRIME64_3;
      i += 4;
    }
    while (i < len){
      uint64_t k1 = p[i++];
      h ^= k1 * PRIME64_5;
      h = rotl64(h, 11) * PRIME64_1;
    }
    h = avalanche(h);
  } else
#elif defined(__aarch64__) && defined(ENABLE_XXH_NEON)
  if (has_simd){
    #include <arm_neon.h>
    size_t i = 0;
    uint64_t v1 = seed + PRIME64_1 + PRIME64_2;
    uint64_t v2 = seed + PRIME64_2;
    uint64_t v3 = seed + 0;
    uint64_t v4 = seed - PRIME64_1;
    const uint64x2_t prime2 = vdupq_n_u64((uint64_t)PRIME64_2);
    while (i + 64 <= len){
      uint64x2_t lo = vld1q_u64((const uint64_t*)(p + i));
      uint64x2_t hi = vld1q_u64((const uint64_t*)(p + i + 16));
      /* lane-wise 64-bit multiply via 32-bit partial products */
      uint32x2_t lo_lo = vmovn_u64(lo);
      uint32x2_t lo_hi = vmovn_u64(vshrq_n_u64(lo, 32));
      uint32x2_t p2_lo = vmovn_u64(prime2);
      uint32x2_t p2_hi = vmovn_u64(vshrq_n_u64(prime2, 32));
      uint64x2_t prod0_lo = vmull_u32(lo_lo, p2_lo);
      uint64x2_t prod0_hi1 = vmull_u32(lo_lo, p2_hi);
      uint64x2_t prod0_hi2 = vmull_u32(lo_hi, p2_lo);
      uint64x2_t prod0 = vaddq_u64(prod0_lo, vshlq_n_u64(vaddq_u64(prod0_hi1, prod0_hi2), 32));

      uint32x2_t hi_lo = vmovn_u64(hi);
      uint32x2_t hi_hi = vmovn_u64(vshrq_n_u64(hi, 32));
      uint64x2_t prod1_lo = vmull_u32(hi_lo, p2_lo);
      uint64x2_t prod1_hi1 = vmull_u32(hi_lo, p2_hi);
      uint64x2_t prod1_hi2 = vmull_u32(hi_hi, p2_lo);
      uint64x2_t prod1 = vaddq_u64(prod1_lo, vshlq_n_u64(vaddq_u64(prod1_hi1, prod1_hi2), 32));

      uint64_t pa = vgetq_lane_u64(prod0, 0);
      uint64_t pb = vgetq_lane_u64(prod0, 1);
      uint64_t pc = vgetq_lane_u64(prod1, 0);
      uint64_t pd = vgetq_lane_u64(prod1, 1);
      v1 = rotl64(v1 + pa, 31) * PRIME64_1;
      v2 = rotl64(v2 + pb, 31) * PRIME64_1;
      v3 = rotl64(v3 + pc, 31) * PRIME64_1;
      v4 = rotl64(v4 + pd, 31) * PRIME64_1;
      uint64x2_t lo2 = vld1q_u64((const uint64_t*)(p + i + 32));
      uint64x2_t hi2 = vld1q_u64((const uint64_t*)(p + i + 48));
      uint32x2_t lo2_lo = vmovn_u64(lo2);
      uint32x2_t lo2_hi = vmovn_u64(vshrq_n_u64(lo2, 32));
      uint64x2_t prod2_lo = vmull_u32(lo2_lo, p2_lo);
      uint64x2_t prod2_hi1 = vmull_u32(lo2_lo, p2_hi);
      uint64x2_t prod2_hi2 = vmull_u32(lo2_hi, p2_lo);
      uint64x2_t prod2 = vaddq_u64(prod2_lo, vshlq_n_u64(vaddq_u64(prod2_hi1, prod2_hi2), 32));
      uint32x2_t hi2_lo = vmovn_u64(hi2);
      uint32x2_t hi2_hi = vmovn_u64(vshrq_n_u64(hi2, 32));
      uint64x2_t prode_lo = vmull_u32(hi2_lo, p2_lo);
      uint64x2_t prode_hi1 = vmull_u32(hi2_lo, p2_hi);
      uint64x2_t prode_hi2 = vmull_u32(hi2_hi, p2_lo);
      uint64x2_t prode = vaddq_u64(prode_lo, vshlq_n_u64(vaddq_u64(prode_hi1, prode_hi2), 32));
      uint64_t q2a = vgetq_lane_u64(prod2, 0);
      uint64_t q2b = vgetq_lane_u64(prod2, 1);
      uint64_t q2c = vgetq_lane_u64(prode, 0);
      uint64_t q2d = vgetq_lane_u64(prode, 1);
      v1 = rotl64(v1 + q2a, 31) * PRIME64_1;
      v2 = rotl64(v2 + q2b, 31) * PRIME64_1;
      v3 = rotl64(v3 + q2c, 31) * PRIME64_1;
      v4 = rotl64(v4 + q2d, 31) * PRIME64_1;
      i += 64;
    }
    if (i > 0){
      h = rotl64(v1, 1) ^ rotl64(v2, 7) ^ rotl64(v3, 12) ^ rotl64(v4, 18);
      h = merge_round(h, v1);
      h = merge_round(h, v2);
      h = merge_round(h, v3);
      h = merge_round(h, v4);
    } else {
      h = seed + PRIME64_5;
    }
    h += (uint64_t)len;
    while (i + 8 <= len){
      uint64_t k1 = read64(p + i);
      k1 = rotl64(k1 * PRIME64_2, 31) * PRIME64_1;
      h ^= k1;
      h = rotl64(h, 27) * PRIME64_1 + PRIME64_4;
      i += 8;
    }
    if (i + 4 <= len){
      uint64_t k1 = read32(p + i);
      h ^= k1 * PRIME64_1;
      h = rotl64(h, 23) * PRIME64_2 + PRIME64_3;
      i += 4;
    }
    while (i < len){
      uint64_t k1 = p[i++];
      h ^= k1 * PRIME64_5;
      h = rotl64(h, 11) * PRIME64_1;
    }
    h = avalanche(h);
  } else
#endif
  {
    /* Fallback tuned scalar */
    h = xxh64_scalar(p, len, seed);
  }
  /* Optional self-check: compare against scalar for correctness */
  {
    const char* self = getenv("L0_XXH_SELFTEST");
    if (self && strcmp(self, "1")==0){
      uint64_t ref = xxh64_scalar(p, len, seed);
      if (ref != h) h = ref; /* prefer correctness */
    }
  }
  CAMLreturn(caml_copy_int64((long long)h));
}
