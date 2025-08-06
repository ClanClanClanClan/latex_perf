/* LaTeX Perfectionist v25 - Track B Arena Allocator
 * Zero-GC-pressure memory management for high-performance lexing
 */

#ifndef ARENA_H
#define ARENA_H

#include "../lexer_types.h"

/* === ARENA MANAGEMENT === */

/* Create arena with estimated capacity
 * estimated_tokens: rough guess of token count (for pre-sizing)
 * Returns: allocated arena or NULL on failure */
arena_t* arena_create(size_t estimated_tokens);

/* Destroy arena and free all memory */
void arena_destroy(arena_t* arena);

/* Reset arena to initial state (keep memory allocated) */
void arena_reset(arena_t* arena);

/* === TOKEN ALLOCATION === */

/* Allocate array of tokens from arena
 * Returns: pointer to token array or NULL if insufficient space */
token_t* arena_alloc_tokens(arena_t* arena, size_t count);

/* Get current token count in arena */
size_t arena_token_count(const arena_t* arena);

/* === STRING ALLOCATION === */

/* Allocate string space from arena and copy data
 * Returns: offset into string arena (0 = allocation failed) */
uint32_t arena_alloc_string(arena_t* arena, const char* str, size_t len);

/* Get string pointer from offset */
const char* arena_get_string(const arena_t* arena, uint32_t offset, size_t len);

/* === MEMORY STATISTICS === */

typedef struct {
    size_t total_size;       /* Total arena size */
    size_t tokens_used;      /* Bytes used for tokens */
    size_t strings_used;     /* Bytes used for strings */
    size_t bytes_free;       /* Remaining free bytes */
    double utilization;      /* Usage percentage */
} arena_stats_t;

/* Get arena memory usage statistics */
arena_stats_t arena_get_stats(const arena_t* arena);

/* === OPTIMIZATION CONSTANTS === */

/* Default arena sizing - optimized for 1.1MB LaTeX files */
#define ARENA_MIN_SIZE          (64 * 1024)        /* 64KB minimum */
#define ARENA_TOKENS_PER_KB     150                /* ~150 tokens per KB of input */
#define ARENA_STRING_OVERHEAD   0.15               /* 15% overhead for strings */
#define ARENA_GROWTH_FACTOR     1.5                /* Growth factor when expanding */
#define ARENA_MAX_SIZE          (128 * 1024 * 1024) /* 128MB maximum */

/* Memory alignment for SIMD operations */
#define ARENA_ALIGNMENT         32                 /* 32-byte alignment for AVX2 */

#endif /* ARENA_H */