/* LaTeX Perfectionist v25 - Track B C Kernel Types
 * High-performance SIMD-enabled lexer with arena allocation
 */

#ifndef LEXER_TYPES_H
#define LEXER_TYPES_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/* === TOKEN DEFINITIONS === */

/* Token types matching OCaml Lexer_v25.token */
typedef enum {
    TOKEN_CHAR = 0,
    TOKEN_MACRO = 1,
    TOKEN_PARAM = 2,
    TOKEN_GROUP_OPEN = 3,
    TOKEN_GROUP_CLOSE = 4,
    TOKEN_EOF = 5
} token_type_t;

/* Catcode types matching OCaml Catcode.t */
typedef enum {
    CATCODE_ESCAPE = 0,      /* \ */
    CATCODE_BEGIN_GROUP = 1, /* { */
    CATCODE_END_GROUP = 2,   /* } */
    CATCODE_MATH_SHIFT = 3,  /* $ */
    CATCODE_ALIGNMENT = 4,   /* & */
    CATCODE_EOL = 5,         /* \n \r */
    CATCODE_PARAMETER = 6,   /* # */
    CATCODE_SUPERSCRIPT = 7, /* ^ */
    CATCODE_SUBSCRIPT = 8,   /* _ */
    CATCODE_IGNORED = 9,     /* \0 */
    CATCODE_SPACE = 10,      /* space, tab */
    CATCODE_LETTER = 11,     /* a-z A-Z */
    CATCODE_OTHER = 12,      /* everything else */
    CATCODE_ACTIVE = 13,     /* active chars */
    CATCODE_COMMENT = 14,    /* % */
    CATCODE_INVALID = 15     /* DEL etc */
} catcode_t;

/* Compact token representation - 16 bytes total */
typedef struct {
    token_type_t type;       /* 4 bytes */
    uint32_t offset;         /* 4 bytes - byte offset in source */
    uint16_t line;           /* 2 bytes - line number */
    uint16_t col;            /* 2 bytes - column number */
    union {                  /* 4 bytes - type-specific data */
        struct {
            uint32_t codepoint;  /* Unicode codepoint */
            catcode_t catcode;   /* Catcode classification */
        } char_data;
        struct {
            uint32_t name_offset; /* Offset into string arena */
            uint32_t name_len;    /* Length of macro name */
        } macro_data;
        int32_t param_num;       /* Parameter number */
    } data;
} token_t;

/* === ARENA ALLOCATOR === */

typedef struct arena {
    char* base;              /* Start of allocated memory */
    size_t size;             /* Total arena size */
    size_t offset;           /* Current allocation offset */
    size_t tokens_count;     /* Number of tokens allocated */
    size_t strings_size;     /* Size of string data */
} arena_t;

/* === LEXER STATE === */

typedef enum {
    STATE_NORMAL = 0,        /* Regular text processing */
    STATE_COMMAND = 1,       /* Inside command name */
    STATE_COMMENT = 2        /* Inside comment (until EOL) */
} lexer_state_t;

/* Lexer context for incremental processing */
typedef struct {
    const char* input;       /* Input buffer */
    size_t input_len;        /* Input length */
    size_t position;         /* Current position */
    lexer_state_t state;     /* Current lexer state */
    uint16_t line;           /* Current line number */
    uint16_t col;            /* Current column */
    arena_t* arena;          /* Memory arena */
    token_t* tokens;         /* Token output buffer */
    size_t max_tokens;       /* Maximum tokens capacity */
    size_t token_count;      /* Current token count */
} lexer_ctx_t;

/* === PERFORMANCE STATISTICS === */

typedef struct {
    uint64_t bytes_processed;
    uint64_t tokens_generated;
    uint64_t time_ns;
    uint32_t simd_operations;
    uint32_t scalar_fallbacks;
    bool simd_enabled;
} perf_stats_t;

/* === FUNCTION POINTERS FOR SIMD DISPATCH === */

typedef size_t (*classify_fn_t)(const char* input, size_t len, catcode_t* output);
typedef size_t (*tokenize_fn_t)(lexer_ctx_t* ctx);

typedef struct {
    classify_fn_t classify;
    tokenize_fn_t tokenize;
    const char* name;
    bool available;
} simd_dispatch_t;

#endif /* LEXER_TYPES_H */