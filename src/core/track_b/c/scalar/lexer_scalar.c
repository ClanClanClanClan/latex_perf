/* LaTeX Perfectionist v25 - Track B Scalar Lexer Implementation
 * High-performance C implementation matching Track A logic
 */

#include "lexer_scalar.h"
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#ifdef LEXER_PROFILE
#include <time.h>
static inline uint64_t get_cycles(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}
#endif

/* === CATCODE LOOKUP TABLE === */

/* Pre-computed catcode table for all 256 ASCII characters */
const catcode_t catcode_table[256] = {
    /* 0x00-0x0F */
    CATCODE_IGNORED, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_SPACE, CATCODE_EOL, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_EOL, CATCODE_OTHER, CATCODE_OTHER,
    
    /* 0x10-0x1F */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    
    /* 0x20-0x2F */
    CATCODE_SPACE, CATCODE_OTHER, CATCODE_OTHER, CATCODE_PARAMETER, /* !"# */
    CATCODE_MATH_SHIFT, CATCODE_COMMENT, CATCODE_ALIGNMENT, CATCODE_OTHER, /* $%&' */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, /* ()*+ */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, /* ,-./ */
    
    /* 0x30-0x3F: Digits 0-9, other symbols */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, /* 0123 */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, /* 4567 */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, /* 89:; */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, /* <=>? */
    
    /* 0x40-0x4F: @, A-O */
    CATCODE_OTHER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* @ABC */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* DEFG */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* HIJK */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* LMNO */
    
    /* 0x50-0x5F: P-Z, symbols */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* PQRS */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* TUVW */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_OTHER, /* XYZ[ */
    CATCODE_ESCAPE, CATCODE_OTHER, CATCODE_SUPERSCRIPT, CATCODE_SUBSCRIPT, /* \]^_ */
    
    /* 0x60-0x6F: `, a-o */
    CATCODE_OTHER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* `abc */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* defg */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* hijk */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* lmno */
    
    /* 0x70-0x7F: p-z, symbols */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* pqrs */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, /* tuvw */
    CATCODE_LETTER, CATCODE_LETTER, CATCODE_LETTER, CATCODE_BEGIN_GROUP, /* xyz{ */
    CATCODE_OTHER, CATCODE_END_GROUP, CATCODE_OTHER, CATCODE_INVALID, /* |}~DEL */
    
    /* 0x80-0xFF: Extended ASCII - treated as OTHER or INVALID */
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER,
    CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER, CATCODE_OTHER
};

/* === CATCODE INITIALIZATION === */

void catcode_init(void) {
    /* Table is statically initialized - nothing to do */
    /* Future: could add validation or runtime customization */
}

/* === LEXER CONTEXT MANAGEMENT === */

lexer_ctx_t* lexer_create(const char* input, size_t input_len, size_t estimated_tokens) {
    if (!input || input_len == 0) return NULL;
    
    lexer_ctx_t* ctx = malloc(sizeof(lexer_ctx_t));
    if (!ctx) return NULL;
    
    /* Create arena for memory management */
    arena_t* arena = arena_create(estimated_tokens);
    if (!arena) {
        free(ctx);
        return NULL;
    }
    
    /* Allocate token buffer */
    token_t* tokens = arena_alloc_tokens(arena, estimated_tokens);
    if (!tokens) {
        arena_destroy(arena);
        free(ctx);
        return NULL;
    }
    
    /* Initialize context */
    ctx->input = input;
    ctx->input_len = input_len;
    ctx->position = 0;
    ctx->state = STATE_NORMAL;
    ctx->line = 1;
    ctx->col = 1;
    ctx->arena = arena;
    ctx->tokens = tokens;
    ctx->max_tokens = estimated_tokens;
    ctx->token_count = 0;
    
    return ctx;
}

void lexer_destroy(lexer_ctx_t* ctx) {
    if (!ctx) return;
    
    if (ctx->arena) {
        arena_destroy(ctx->arena);
    }
    free(ctx);
}

/* === UTF-8 DECODING === */

uint32_t utf8_decode(const char* str, size_t* consumed) {
    if (!str || !consumed) return 0;
    
    unsigned char c = (unsigned char)*str;
    *consumed = 1;
    
    /* ASCII fast path */
    if (c < 0x80) {
        return c;
    }
    
    /* Multi-byte UTF-8 - simplified for performance */
    /* In production, would use full UTF-8 decoder */
    return c; /* Fallback to byte value */
}

/* === TOKEN CREATION HELPERS === */

void make_macro_token(token_t* token, uint32_t offset, uint16_t line, uint16_t col,
                      const char* name, size_t name_len, arena_t* arena) {
    token->type = TOKEN_MACRO;
    token->offset = offset;
    token->line = line;
    token->col = col;
    
    /* Store macro name in arena */
    uint32_t name_offset = arena_alloc_string(arena, name, name_len);
    token->data.macro_data.name_offset = name_offset;
    token->data.macro_data.name_len = (uint32_t)name_len;
}

/* === BATCH CLASSIFICATION === */

size_t classify_batch_scalar(const char* input, size_t len, catcode_t* output) {
    if (!input || !output || len == 0) return 0;
    
    for (size_t i = 0; i < len; i++) {
        output[i] = catcode_lookup((unsigned char)input[i]);
    }
    
    return len;
}

/* === STATE MACHINE IMPLEMENTATION === */

size_t process_normal_state(lexer_ctx_t* ctx) {
    size_t tokens_created = 0;
    
    while (ctx->position < ctx->input_len && ctx->token_count < ctx->max_tokens) {
        char c = ctx->input[ctx->position];
        catcode_t catcode = catcode_lookup((unsigned char)c);
        
        token_t* token = &ctx->tokens[ctx->token_count];
        
        switch (catcode) {
            case CATCODE_ESCAPE: {
                /* Start of command - switch to command state */
                ctx->state = STATE_COMMAND;
                ctx->position++;
                ctx->col++;
                return tokens_created; /* Let command state handle it */
            }
            
            case CATCODE_BEGIN_GROUP: {
                make_simple_token(token, TOKEN_GROUP_OPEN, 
                                (uint32_t)ctx->position, ctx->line, ctx->col);
                break;
            }
            
            case CATCODE_END_GROUP: {
                make_simple_token(token, TOKEN_GROUP_CLOSE, 
                                (uint32_t)ctx->position, ctx->line, ctx->col);
                break;
            }
            
            case CATCODE_COMMENT: {
                /* Start comment state */
                ctx->state = STATE_COMMENT;
                ctx->position++;
                ctx->col++;
                return tokens_created; /* Let comment state handle it */
            }
            
            default: {
                /* Regular character token */
                make_char_token(token, (uint32_t)ctx->position, ctx->line, ctx->col,
                              (uint32_t)c, catcode);
                break;
            }
        }
        
        /* Advance position */
        ctx->position++;
        if (c == '\n') {
            ctx->line++;
            ctx->col = 1;
        } else {
            ctx->col++;
        }
        
        ctx->token_count++;
        tokens_created++;
    }
    
    return tokens_created;
}

size_t process_command_state(lexer_ctx_t* ctx) {
    if (ctx->position >= ctx->input_len) return 0;
    
    size_t start_pos = ctx->position;
    size_t name_start = ctx->position;
    
    /* Collect command name (letters only) */
    while (ctx->position < ctx->input_len) {
        char c = ctx->input[ctx->position];
        catcode_t catcode = catcode_lookup((unsigned char)c);
        
        if (catcode != CATCODE_LETTER) {
            break;
        }
        
        ctx->position++;
        ctx->col++;
    }
    
    size_t name_len = ctx->position - name_start;
    
    if (name_len > 0 && ctx->token_count < ctx->max_tokens) {
        /* Create macro token */
        token_t* token = &ctx->tokens[ctx->token_count];
        make_macro_token(token, (uint32_t)start_pos, ctx->line, ctx->col,
                        ctx->input + name_start, name_len, ctx->arena);
        ctx->token_count++;
    }
    
    /* Return to normal state */
    ctx->state = STATE_NORMAL;
    
    return name_len > 0 ? 1 : 0;
}

size_t process_comment_state(lexer_ctx_t* ctx) {
    /* Skip until end of line */
    while (ctx->position < ctx->input_len) {
        char c = ctx->input[ctx->position];
        ctx->position++;
        
        if (c == '\n' || c == '\r') {
            ctx->line++;
            ctx->col = 1;
            ctx->state = STATE_NORMAL;
            break;
        } else {
            ctx->col++;
        }
    }
    
    return 0; /* Comments don't generate tokens */
}

/* === MAIN TOKENIZATION FUNCTION === */

size_t lexer_tokenize_scalar(lexer_ctx_t* ctx) {
    if (!ctx) return 0;
    
#ifdef LEXER_PROFILE
    profile_data_t profile;
    profile_start(&profile);
#endif
    
    size_t initial_count = ctx->token_count;
    
    /* Main tokenization loop */
    while (ctx->position < ctx->input_len && ctx->token_count < ctx->max_tokens) {
        size_t tokens_before = ctx->token_count;
        
        switch (ctx->state) {
            case STATE_NORMAL:
                process_normal_state(ctx);
                break;
            case STATE_COMMAND:
                process_command_state(ctx);
                break;
            case STATE_COMMENT:
                process_comment_state(ctx);
                break;
        }
        
        /* Prevent infinite loops */
        if (ctx->token_count == tokens_before && ctx->position < ctx->input_len) {
            /* Force advance if no progress made */
            ctx->position++;
            ctx->col++;
        }
    }
    
    /* Add EOF token */
    if (ctx->token_count < ctx->max_tokens) {
        token_t* eof_token = &ctx->tokens[ctx->token_count];
        make_simple_token(eof_token, TOKEN_EOF, 
                         (uint32_t)ctx->position, ctx->line, ctx->col);
        ctx->token_count++;
    }
    
    size_t tokens_generated = ctx->token_count - initial_count;
    
#ifdef LEXER_PROFILE
    profile_end(&profile, ctx->input_len, tokens_generated);
    profile_print(&profile);
#endif
    
    return tokens_generated;
}

/* === ERROR HANDLING === */

lexer_error_t lexer_get_error(const lexer_ctx_t* ctx) {
    if (!ctx) return LEXER_ERROR_NULL_CONTEXT;
    return LEXER_OK; /* Simplified - would track errors in real implementation */
}

const char* lexer_error_string(lexer_error_t error) {
    switch (error) {
        case LEXER_OK: return "No error";
        case LEXER_ERROR_NULL_CONTEXT: return "Null lexer context";
        case LEXER_ERROR_OUT_OF_MEMORY: return "Out of memory";
        case LEXER_ERROR_INVALID_UTF8: return "Invalid UTF-8 sequence";
        case LEXER_ERROR_TOKEN_OVERFLOW: return "Too many tokens";
        case LEXER_ERROR_INPUT_TOO_LARGE: return "Input too large";
        default: return "Unknown error";
    }
}

/* === PROFILING SUPPORT === */

#ifdef LEXER_PROFILE
void profile_start(profile_data_t* profile) {
    if (!profile) return;
    memset(profile, 0, sizeof(profile_data_t));
    profile->total_cycles = get_cycles();
}

void profile_end(profile_data_t* profile, size_t bytes, size_t tokens) {
    if (!profile) return;
    profile->total_cycles = get_cycles() - profile->total_cycles;
    profile->bytes_processed = bytes;
    profile->tokens_generated = tokens;
}

void profile_print(const profile_data_t* profile) {
    if (!profile) return;
    
    double ms = (double)profile->total_cycles / 1000000.0;
    double throughput_mbps = (double)profile->bytes_processed / ms / 1000.0;
    
    printf("LEXER PROFILE:\n");
    printf("  Time: %.3f ms\n", ms);
    printf("  Bytes: %zu\n", profile->bytes_processed);
    printf("  Tokens: %zu\n", profile->tokens_generated);
    printf("  Throughput: %.1f MB/s\n", throughput_mbps);
}
#endif