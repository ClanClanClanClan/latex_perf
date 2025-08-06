/* LaTeX Perfectionist v25 - Track B Scalar Lexer
 * High-performance C implementation matching Track A logic
 */

#ifndef LEXER_SCALAR_H
#define LEXER_SCALAR_H

#include "../lexer_types.h"
#include "../arena/arena.h"

/* === CATCODE CLASSIFICATION === */

/* Fast catcode lookup table - precomputed for all 256 bytes */
extern const catcode_t catcode_table[256];

/* Initialize catcode lookup table */
void catcode_init(void);

/* Fast inline catcode lookup */
static inline catcode_t catcode_lookup(unsigned char c) {
    return catcode_table[c];
}

/* === SCALAR LEXER API === */

/* Initialize lexer context */
lexer_ctx_t* lexer_create(const char* input, size_t input_len, size_t estimated_tokens);

/* Destroy lexer context and free resources */
void lexer_destroy(lexer_ctx_t* ctx);

/* Main scalar tokenization function
 * Returns: number of tokens generated, or 0 on error */
size_t lexer_tokenize_scalar(lexer_ctx_t* ctx);

/* === TOKEN CREATION HELPERS === */

/* Create character token */
static inline void make_char_token(token_t* token, uint32_t offset, uint16_t line, 
                                   uint16_t col, uint32_t codepoint, catcode_t catcode) {
    token->type = TOKEN_CHAR;
    token->offset = offset;
    token->line = line;
    token->col = col;
    token->data.char_data.codepoint = codepoint;
    token->data.char_data.catcode = catcode;
}

/* Create macro token */
void make_macro_token(token_t* token, uint32_t offset, uint16_t line, uint16_t col,
                      const char* name, size_t name_len, arena_t* arena);

/* Create simple tokens (group open/close, EOF) */
static inline void make_simple_token(token_t* token, token_type_t type, 
                                      uint32_t offset, uint16_t line, uint16_t col) {
    token->type = type;
    token->offset = offset;
    token->line = line;
    token->col = col;
    /* data union left zeroed for simple tokens */
}

/* === PERFORMANCE OPTIMIZATIONS === */

/* Batch character classification - process multiple bytes */
size_t classify_batch_scalar(const char* input, size_t len, catcode_t* output);

/* Fast UTF-8 decoder for Unicode support */
uint32_t utf8_decode(const char* str, size_t* consumed);

/* Position tracking with optimized line/column updates */
typedef struct {
    uint16_t line;
    uint16_t col;
} position_t;

static inline void advance_position(position_t* pos, char c) {
    if (c == '\n') {
        pos->line++;
        pos->col = 1;
    } else {
        pos->col++;
    }
}

/* === LEXER STATE MACHINE === */

/* Process normal text state */
size_t process_normal_state(lexer_ctx_t* ctx);

/* Process command state */
size_t process_command_state(lexer_ctx_t* ctx);

/* Process comment state */
size_t process_comment_state(lexer_ctx_t* ctx);

/* === ERROR HANDLING === */

typedef enum {
    LEXER_OK = 0,
    LEXER_ERROR_NULL_CONTEXT = 1,
    LEXER_ERROR_OUT_OF_MEMORY = 2,
    LEXER_ERROR_INVALID_UTF8 = 3,
    LEXER_ERROR_TOKEN_OVERFLOW = 4,
    LEXER_ERROR_INPUT_TOO_LARGE = 5
} lexer_error_t;

/* Get last error */
lexer_error_t lexer_get_error(const lexer_ctx_t* ctx);

/* Error message strings */
const char* lexer_error_string(lexer_error_t error);

/* === PERFORMANCE PROFILING === */

#ifdef LEXER_PROFILE
typedef struct {
    uint64_t total_cycles;
    uint64_t classification_cycles;
    uint64_t tokenization_cycles;
    uint64_t allocation_cycles;
    size_t bytes_processed;
    size_t tokens_generated;
} profile_data_t;

/* Start profiling */
void profile_start(profile_data_t* profile);

/* End profiling and record results */
void profile_end(profile_data_t* profile, size_t bytes, size_t tokens);

/* Print profiling results */
void profile_print(const profile_data_t* profile);
#endif

#endif /* LEXER_SCALAR_H */