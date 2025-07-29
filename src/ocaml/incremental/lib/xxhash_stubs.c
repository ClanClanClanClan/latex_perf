/* xxhash_stubs.c - Fast hashing for line comparison */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <stdint.h>
#include <string.h>

/* Simplified xxHash64 implementation */
#define XXH_PRIME64_1 0x9E3779B185EBCA87ULL
#define XXH_PRIME64_2 0xC2B2AE3D27D4EB4FULL
#define XXH_PRIME64_3 0x165667B19E3779F9ULL
#define XXH_PRIME64_4 0x85EBCA77C2B2AE63ULL
#define XXH_PRIME64_5 0x27D4EB2F165667C5ULL

static inline uint64_t XXH64_rotl(uint64_t x, int r) {
    return (x << r) | (x >> (64 - r));
}

static inline uint64_t XXH64_round(uint64_t acc, uint64_t input) {
    acc += input * XXH_PRIME64_2;
    acc = XXH64_rotl(acc, 31);
    acc *= XXH_PRIME64_1;
    return acc;
}

uint64_t xxhash64(const void* data, size_t len, uint64_t seed) {
    const uint8_t* p = (const uint8_t*)data;
    const uint8_t* const end = p + len;
    uint64_t h64;

    if (len >= 32) {
        const uint8_t* const limit = end - 32;
        uint64_t v1 = seed + XXH_PRIME64_1 + XXH_PRIME64_2;
        uint64_t v2 = seed + XXH_PRIME64_2;
        uint64_t v3 = seed + 0;
        uint64_t v4 = seed - XXH_PRIME64_1;

        do {
            v1 = XXH64_round(v1, *(uint64_t*)p); p += 8;
            v2 = XXH64_round(v2, *(uint64_t*)p); p += 8;
            v3 = XXH64_round(v3, *(uint64_t*)p); p += 8;
            v4 = XXH64_round(v4, *(uint64_t*)p); p += 8;
        } while (p <= limit);

        h64 = XXH64_rotl(v1, 1) + XXH64_rotl(v2, 7) + 
              XXH64_rotl(v3, 12) + XXH64_rotl(v4, 18);
        
        h64 = (h64 ^ XXH64_round(0, v1)) * XXH_PRIME64_1 + XXH_PRIME64_4;
        h64 = (h64 ^ XXH64_round(0, v2)) * XXH_PRIME64_1 + XXH_PRIME64_4;
        h64 = (h64 ^ XXH64_round(0, v3)) * XXH_PRIME64_1 + XXH_PRIME64_4;
        h64 = (h64 ^ XXH64_round(0, v4)) * XXH_PRIME64_1 + XXH_PRIME64_4;
    } else {
        h64 = seed + XXH_PRIME64_5;
    }

    h64 += (uint64_t)len;

    while (p + 8 <= end) {
        uint64_t k1 = *(uint64_t*)p;
        k1 *= XXH_PRIME64_2;
        k1 = XXH64_rotl(k1, 31);
        k1 *= XXH_PRIME64_1;
        h64 ^= k1;
        h64 = XXH64_rotl(h64, 27) * XXH_PRIME64_1 + XXH_PRIME64_4;
        p += 8;
    }

    if (p + 4 <= end) {
        h64 ^= (uint64_t)(*(uint32_t*)p) * XXH_PRIME64_1;
        h64 = XXH64_rotl(h64, 23) * XXH_PRIME64_2 + XXH_PRIME64_3;
        p += 4;
    }

    while (p < end) {
        h64 ^= (*p++) * XXH_PRIME64_5;
        h64 = XXH64_rotl(h64, 11) * XXH_PRIME64_1;
    }

    h64 ^= h64 >> 33;
    h64 *= XXH_PRIME64_2;
    h64 ^= h64 >> 29;
    h64 *= XXH_PRIME64_3;
    h64 ^= h64 >> 32;

    return h64;
}

CAMLprim value caml_xxhash64(value str) {
    CAMLparam1(str);
    CAMLlocal1(result);
    
    const char* data = String_val(str);
    size_t len = caml_string_length(str);
    uint64_t hash = xxhash64(data, len, 0);
    
    result = caml_copy_int64(hash);
    CAMLreturn(result);
}