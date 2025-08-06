/* LaTeX Perfectionist v25 - Track B Arena Allocator Implementation */

#include "arena.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>

/* === INTERNAL HELPERS === */

/* Align size to boundary */
static inline size_t align_size(size_t size, size_t alignment) {
    return (size + alignment - 1) & ~(alignment - 1);
}

/* Calculate recommended arena size based on input */
static size_t calculate_arena_size(size_t estimated_tokens) {
    /* Estimate memory needs:
     * - Tokens: estimated_tokens * sizeof(token_t)
     * - Strings: estimated string data (15% overhead)
     * - Alignment padding
     */
    size_t token_bytes = estimated_tokens * sizeof(token_t);
    size_t string_bytes = (size_t)(token_bytes * ARENA_STRING_OVERHEAD);
    size_t total = token_bytes + string_bytes;
    
    /* Apply growth factor for safety */
    total = (size_t)(total * ARENA_GROWTH_FACTOR);
    
    /* Clamp to reasonable bounds */
    if (total < ARENA_MIN_SIZE) total = ARENA_MIN_SIZE;
    if (total > ARENA_MAX_SIZE) total = ARENA_MAX_SIZE;
    
    /* Align to SIMD boundary */
    return align_size(total, ARENA_ALIGNMENT);
}

/* === PUBLIC API === */

arena_t* arena_create(size_t estimated_tokens) {
    arena_t* arena = malloc(sizeof(arena_t));
    if (!arena) return NULL;
    
    size_t size = calculate_arena_size(estimated_tokens);
    
    /* Allocate aligned memory for SIMD operations */
    void* base = aligned_alloc(ARENA_ALIGNMENT, size);
    if (!base) {
        free(arena);
        return NULL;
    }
    
    arena->base = (char*)base;
    arena->size = size;
    arena->offset = 0;
    arena->tokens_count = 0;
    arena->strings_size = 0;
    
    return arena;
}

void arena_destroy(arena_t* arena) {
    if (!arena) return;
    
    if (arena->base) {
        free(arena->base);
    }
    free(arena);
}

void arena_reset(arena_t* arena) {
    if (!arena) return;
    
    arena->offset = 0;
    arena->tokens_count = 0;
    arena->strings_size = 0;
}

token_t* arena_alloc_tokens(arena_t* arena, size_t count) {
    if (!arena || count == 0) return NULL;
    
    size_t needed = count * sizeof(token_t);
    size_t aligned_needed = align_size(needed, sizeof(token_t));
    
    /* Check if we have enough space */
    if (arena->offset + aligned_needed > arena->size) {
        return NULL; /* Out of memory */
    }
    
    token_t* result = (token_t*)(arena->base + arena->offset);
    arena->offset += aligned_needed;
    arena->tokens_count += count;
    
    /* Zero-initialize tokens */
    memset(result, 0, needed);
    
    return result;
}

size_t arena_token_count(const arena_t* arena) {
    return arena ? arena->tokens_count : 0;
}

uint32_t arena_alloc_string(arena_t* arena, const char* str, size_t len) {
    if (!arena || !str || len == 0) return 0;
    
    size_t aligned_len = align_size(len + 1, 8); /* +1 for null terminator */
    
    /* Check if we have enough space */
    if (arena->offset + aligned_len > arena->size) {
        return 0; /* Out of memory */
    }
    
    uint32_t offset = (uint32_t)arena->offset;
    char* dest = arena->base + arena->offset;
    
    /* Copy string data */
    memcpy(dest, str, len);
    dest[len] = '\0'; /* Null terminate */
    
    arena->offset += aligned_len;
    arena->strings_size += aligned_len;
    
    return offset;
}

const char* arena_get_string(const arena_t* arena, uint32_t offset, size_t len) {
    if (!arena || offset == 0 || offset >= arena->size) return NULL;
    
    const char* str = arena->base + offset;
    
    /* Bounds check */
    if (offset + len > arena->size) return NULL;
    
    return str;
}

arena_stats_t arena_get_stats(const arena_t* arena) {
    arena_stats_t stats = {0};
    
    if (!arena) return stats;
    
    stats.total_size = arena->size;
    stats.tokens_used = arena->tokens_count * sizeof(token_t);
    stats.strings_used = arena->strings_size;
    size_t total_used = arena->offset;
    stats.bytes_free = arena->size - total_used;
    stats.utilization = (double)total_used / arena->size * 100.0;
    
    return stats;
}

/* === TESTING SUPPORT === */

#ifdef ARENA_TESTING
/* Test arena functionality */
bool arena_test_basic(void) {
    arena_t* arena = arena_create(1000);
    if (!arena) return false;
    
    /* Test token allocation */
    token_t* tokens = arena_alloc_tokens(arena, 10);
    if (!tokens) {
        arena_destroy(arena);
        return false;
    }
    
    /* Test string allocation */
    const char* test_str = "\\documentclass";
    uint32_t offset = arena_alloc_string(arena, test_str, strlen(test_str));
    if (offset == 0) {
        arena_destroy(arena);
        return false;
    }
    
    /* Test string retrieval */
    const char* retrieved = arena_get_string(arena, offset, strlen(test_str));
    if (!retrieved || strcmp(retrieved, test_str) != 0) {
        arena_destroy(arena);
        return false;
    }
    
    /* Test stats */
    arena_stats_t stats = arena_get_stats(arena);
    if (stats.total_size == 0 || stats.utilization == 0) {
        arena_destroy(arena);
        return false;
    }
    
    arena_destroy(arena);
    return true;
}
#endif