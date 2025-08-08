/* LaTeX Perfectionist v25 - Track B ARM NEON SIMD Implementation
 * High-performance catcode classification using 128-bit SIMD
 */

#ifndef LEXER_NEON_H
#define LEXER_NEON_H

#include <arm_neon.h>
#include <stdint.h>
#include <stddef.h>
#include "../lexer_types.h"

/* === NEON CONSTANTS === */

/* Special character constants for fast detection */
#define CHAR_BACKSLASH  0x5C  /* \ */
#define CHAR_LBRACE     0x7B  /* { */
#define CHAR_RBRACE     0x7D  /* } */
#define CHAR_DOLLAR     0x24  /* $ */
#define CHAR_AMPERSAND  0x26  /* & */
#define CHAR_HASH       0x23  /* # */
#define CHAR_CARET      0x5E  /* ^ */
#define CHAR_UNDERSCORE 0x5F  /* _ */
#define CHAR_PERCENT    0x25  /* % */
#define CHAR_SPACE      0x20  /* space */
#define CHAR_TAB        0x09  /* tab */
#define CHAR_NEWLINE    0x0A  /* \n */
#define CHAR_RETURN     0x0D  /* \r */

/* === NEON SIMD FUNCTIONS === */

/* Initialize NEON lookup tables */
void init_neon_tables(void);

/* Classify 16 bytes at once using NEON 
 * Returns: number of bytes processed (always 16 unless at end) */
size_t classify_chars_neon(const uint8_t* input, size_t len, catcode_t* output);

/* Find special characters in 16-byte chunk
 * Returns: bitmask of special character positions */
uint16_t find_special_chars_neon(const uint8_t* input);

/* Optimized tokenization using NEON */
size_t tokenize_neon(lexer_ctx_t* ctx);

/* === SIMD CATCODE LOOKUP === */

/* Pre-computed NEON lookup tables for catcode classification */
extern uint8x16_t g_catcode_table_00; /* For bytes 0x00-0x0F */
extern uint8x16_t g_catcode_table_10; /* For bytes 0x10-0x1F */
extern uint8x16_t g_catcode_table_20; /* For bytes 0x20-0x2F */
extern uint8x16_t g_catcode_table_30; /* For bytes 0x30-0x3F */
extern uint8x16_t g_catcode_table_40; /* For bytes 0x40-0x4F */
extern uint8x16_t g_catcode_table_50; /* For bytes 0x50-0x5F */
extern uint8x16_t g_catcode_table_60; /* For bytes 0x60-0x6F */
extern uint8x16_t g_catcode_table_70; /* For bytes 0x70-0x7F */

/* Fast catcode lookup using NEON table lookups */
static inline uint8x16_t lookup_catcodes_neon(uint8x16_t chars) {
    /* Create vectors for special character comparisons */
    uint8x16_t v_backslash = vdupq_n_u8(CHAR_BACKSLASH);
    uint8x16_t v_lbrace = vdupq_n_u8(CHAR_LBRACE);
    uint8x16_t v_rbrace = vdupq_n_u8(CHAR_RBRACE);
    uint8x16_t v_dollar = vdupq_n_u8(CHAR_DOLLAR);
    uint8x16_t v_ampersand = vdupq_n_u8(CHAR_AMPERSAND);
    uint8x16_t v_hash = vdupq_n_u8(CHAR_HASH);
    uint8x16_t v_caret = vdupq_n_u8(CHAR_CARET);
    uint8x16_t v_underscore = vdupq_n_u8(CHAR_UNDERSCORE);
    uint8x16_t v_percent = vdupq_n_u8(CHAR_PERCENT);
    uint8x16_t v_space = vdupq_n_u8(CHAR_SPACE);
    uint8x16_t v_tab = vdupq_n_u8(CHAR_TAB);
    uint8x16_t v_newline = vdupq_n_u8(CHAR_NEWLINE);
    uint8x16_t v_return = vdupq_n_u8(CHAR_RETURN);
    
    /* Initialize with default catcode 12 (Other) */
    uint8x16_t catcodes = vdupq_n_u8(12);
    
    /* Check for letters (A-Z: 0x41-0x5A, a-z: 0x61-0x7A) */
    uint8x16_t is_upper_start = vcgeq_u8(chars, vdupq_n_u8(0x41));
    uint8x16_t is_upper_end = vcleq_u8(chars, vdupq_n_u8(0x5A));
    uint8x16_t is_upper = vandq_u8(is_upper_start, is_upper_end);
    
    uint8x16_t is_lower_start = vcgeq_u8(chars, vdupq_n_u8(0x61));
    uint8x16_t is_lower_end = vcleq_u8(chars, vdupq_n_u8(0x7A));
    uint8x16_t is_lower = vandq_u8(is_lower_start, is_lower_end);
    
    uint8x16_t is_letter = vorrq_u8(is_upper, is_lower);
    catcodes = vbslq_u8(is_letter, vdupq_n_u8(11), catcodes); /* Letter = 11 */
    
    /* Check for special characters and assign their catcodes */
    uint8x16_t is_backslash = vceqq_u8(chars, v_backslash);
    catcodes = vbslq_u8(is_backslash, vdupq_n_u8(0), catcodes); /* Escape = 0 */
    
    uint8x16_t is_lbrace = vceqq_u8(chars, v_lbrace);
    catcodes = vbslq_u8(is_lbrace, vdupq_n_u8(1), catcodes); /* BeginGroup = 1 */
    
    uint8x16_t is_rbrace = vceqq_u8(chars, v_rbrace);
    catcodes = vbslq_u8(is_rbrace, vdupq_n_u8(2), catcodes); /* EndGroup = 2 */
    
    uint8x16_t is_dollar = vceqq_u8(chars, v_dollar);
    catcodes = vbslq_u8(is_dollar, vdupq_n_u8(3), catcodes); /* MathShift = 3 */
    
    uint8x16_t is_ampersand = vceqq_u8(chars, v_ampersand);
    catcodes = vbslq_u8(is_ampersand, vdupq_n_u8(4), catcodes); /* AlignTab = 4 */
    
    uint8x16_t is_hash = vceqq_u8(chars, v_hash);
    catcodes = vbslq_u8(is_hash, vdupq_n_u8(6), catcodes); /* Param = 6 */
    
    uint8x16_t is_caret = vceqq_u8(chars, v_caret);
    catcodes = vbslq_u8(is_caret, vdupq_n_u8(7), catcodes); /* Superscript = 7 */
    
    uint8x16_t is_underscore = vceqq_u8(chars, v_underscore);
    catcodes = vbslq_u8(is_underscore, vdupq_n_u8(8), catcodes); /* Subscript = 8 */
    
    uint8x16_t is_percent = vceqq_u8(chars, v_percent);
    catcodes = vbslq_u8(is_percent, vdupq_n_u8(14), catcodes); /* Comment = 14 */
    
    /* Check for space characters */
    uint8x16_t is_space_char = vorrq_u8(vceqq_u8(chars, v_space), vceqq_u8(chars, v_tab));
    catcodes = vbslq_u8(is_space_char, vdupq_n_u8(10), catcodes); /* Space = 10 */
    
    /* Check for EOL characters */
    uint8x16_t is_eol = vorrq_u8(vceqq_u8(chars, v_newline), vceqq_u8(chars, v_return));
    catcodes = vbslq_u8(is_eol, vdupq_n_u8(5), catcodes); /* EndLine = 5 */
    
    return catcodes;
}

/* === CHUNK PROCESSING === */

/* Process a 16-byte chunk and emit tokens */
static inline size_t process_chunk_neon(
    const uint8_t* input,
    size_t offset,
    uint8x16_t catcodes,
    token_t* tokens,
    size_t max_tokens,
    size_t* token_count,
    uint16_t* line,
    uint16_t* col
) {
    /* Store catcodes to temporary buffer for scalar processing */
    uint8_t catcode_buf[16];
    vst1q_u8(catcode_buf, catcodes);
    
    size_t tokens_emitted = 0;
    
    for (size_t i = 0; i < 16 && *token_count < max_tokens; i++) {
        uint8_t ch = input[i];
        catcode_t cat = (catcode_t)catcode_buf[i];
        
        /* Update position tracking */
        if (ch == '\n') {
            (*line)++;
            *col = 1;
        } else {
            (*col)++;
        }
        
        /* Special handling for escape sequences, comments, etc. */
        switch (cat) {
            case CATCODE_ESCAPE:
                /* Start of command - would trigger state change */
                break;
                
            case CATCODE_COMMENT:
                /* Skip to end of line */
                break;
                
            default:
                /* Emit character token */
                if (*token_count < max_tokens) {
                    token_t* tok = &tokens[*token_count];
                    tok->type = TOKEN_CHAR;
                    tok->offset = (uint32_t)(offset + i);
                    tok->line = *line;
                    tok->col = *col;
                    tok->data.char_data.codepoint = ch;
                    tok->data.char_data.catcode = cat;
                    (*token_count)++;
                    tokens_emitted++;
                }
                break;
        }
    }
    
    return tokens_emitted;
}

/* === PERFORMANCE UTILITIES === */

/* Prefetch next chunk for better cache utilization */
static inline void prefetch_next_chunk_neon(const void* addr) {
    __builtin_prefetch(addr, 0, 3);
}

/* Find positions of special characters using NEON */
static inline uint16_t find_specials_neon(uint8x16_t chars) {
    /* Check for backslash (escape character) */
    uint8x16_t is_escape = vceqq_u8(chars, vdupq_n_u8(CHAR_BACKSLASH));
    
    /* Check for group delimiters */
    uint8x16_t is_lbrace = vceqq_u8(chars, vdupq_n_u8(CHAR_LBRACE));
    uint8x16_t is_rbrace = vceqq_u8(chars, vdupq_n_u8(CHAR_RBRACE));
    
    /* Check for other special chars */
    uint8x16_t is_dollar = vceqq_u8(chars, vdupq_n_u8(CHAR_DOLLAR));
    uint8x16_t is_percent = vceqq_u8(chars, vdupq_n_u8(CHAR_PERCENT));
    
    /* Combine all special character masks */
    uint8x16_t specials = vorrq_u8(is_escape, is_lbrace);
    specials = vorrq_u8(specials, is_rbrace);
    specials = vorrq_u8(specials, is_dollar);
    specials = vorrq_u8(specials, is_percent);
    
    /* Convert to bitmask using pairwise operations */
    /* This is the NEON equivalent of movemask */
    uint8x8_t paired = vpadd_u8(vget_low_u8(specials), vget_high_u8(specials));
    uint16x4_t paired16 = vpaddl_u8(paired);
    uint32x2_t paired32 = vpaddl_u16(paired16);
    uint64x1_t result = vpaddl_u32(paired32);
    
    return (uint16_t)vget_lane_u64(result, 0);
}

/* Check if NEON is available (always true on ARM64) */
static inline int has_neon_support(void) {
    #ifdef __aarch64__
        return 1;  /* NEON is mandatory on ARM64 */
    #else
        /* For 32-bit ARM, would need runtime detection */
        return 0;
    #endif
}

#endif /* LEXER_NEON_H */