/* LaTeX Perfectionist v25 - Track B AVX2 SIMD Implementation
 * High-performance catcode classification using 256-bit SIMD
 */

#ifndef LEXER_AVX2_H
#define LEXER_AVX2_H

#include <immintrin.h>
#include <stdint.h>
#include <stddef.h>
#include "../lexer_types.h"

/* === AVX2 CONSTANTS === */

/* Special character masks for fast detection */
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

/* === AVX2 SIMD FUNCTIONS === */

/* Initialize AVX2 lookup tables */
void init_avx2_tables(void);

/* Classify 32 bytes at once using AVX2 
 * Returns: number of bytes processed (always 32 unless at end) */
size_t classify_chars_avx2(const uint8_t* input, size_t len, catcode_t* output);

/* Find special characters in 32-byte chunk
 * Returns: bitmask of special character positions */
uint32_t find_special_chars_avx2(const uint8_t* input);

/* Optimized tokenization using AVX2 */
size_t tokenize_avx2(lexer_ctx_t* ctx);

/* === SIMD CATCODE LOOKUP === */

/* Pre-computed SIMD shuffle tables for catcode classification */
extern __m256i g_catcode_shuf_lo;  /* For bytes 0x00-0x0F */
extern __m256i g_catcode_shuf_hi;  /* For bytes 0x10-0x1F */
extern __m256i g_catcode_shuf_20;  /* For bytes 0x20-0x2F */
extern __m256i g_catcode_shuf_30;  /* For bytes 0x30-0x3F */
extern __m256i g_catcode_shuf_40;  /* For bytes 0x40-0x4F */
extern __m256i g_catcode_shuf_50;  /* For bytes 0x50-0x5F */
extern __m256i g_catcode_shuf_60;  /* For bytes 0x60-0x6F */
extern __m256i g_catcode_shuf_70;  /* For bytes 0x70-0x7F */

/* Fast catcode lookup using PSHUFB */
static inline __m256i lookup_catcodes_avx2(__m256i chars) {
    /* Split input into nibbles */
    const __m256i nibble_mask = _mm256_set1_epi8(0x0F);
    __m256i lo_nibbles = _mm256_and_si256(chars, nibble_mask);
    __m256i hi_nibbles = _mm256_and_si256(_mm256_srli_epi16(chars, 4), nibble_mask);
    
    /* Classify based on high nibble using 8-way shuffle 
     * This is a simplified version - real implementation would use
     * full 256-entry lookup table split across multiple shuffles */
    __m256i catcodes = _mm256_setzero_si256();
    
    /* For ASCII letters (0x41-0x5A, 0x61-0x7A), set catcode 11 (Letter) */
    __m256i is_upper = _mm256_and_si256(
        _mm256_cmpgt_epi8(chars, _mm256_set1_epi8(0x40)),
        _mm256_cmpgt_epi8(_mm256_set1_epi8(0x5B), chars)
    );
    __m256i is_lower = _mm256_and_si256(
        _mm256_cmpgt_epi8(chars, _mm256_set1_epi8(0x60)),
        _mm256_cmpgt_epi8(_mm256_set1_epi8(0x7B), chars)
    );
    __m256i is_letter = _mm256_or_si256(is_upper, is_lower);
    catcodes = _mm256_blendv_epi8(catcodes, _mm256_set1_epi8(11), is_letter);
    
    /* Special characters get their specific catcodes */
    __m256i is_backslash = _mm256_cmpeq_epi8(chars, _mm256_set1_epi8(CHAR_BACKSLASH));
    catcodes = _mm256_blendv_epi8(catcodes, _mm256_set1_epi8(0), is_backslash);
    
    __m256i is_lbrace = _mm256_cmpeq_epi8(chars, _mm256_set1_epi8(CHAR_LBRACE));
    catcodes = _mm256_blendv_epi8(catcodes, _mm256_set1_epi8(1), is_lbrace);
    
    __m256i is_rbrace = _mm256_cmpeq_epi8(chars, _mm256_set1_epi8(CHAR_RBRACE));
    catcodes = _mm256_blendv_epi8(catcodes, _mm256_set1_epi8(2), is_rbrace);
    
    /* Continue for other special chars... */
    /* Default to catcode 12 (Other) for unmatched */
    __m256i is_unmatched = _mm256_cmpeq_epi8(catcodes, _mm256_setzero_si256());
    catcodes = _mm256_blendv_epi8(catcodes, _mm256_set1_epi8(12), is_unmatched);
    
    return catcodes;
}

/* === CHUNK PROCESSING === */

/* Process a 32-byte chunk and emit tokens */
static inline size_t process_chunk_avx2(
    const uint8_t* input,
    size_t offset,
    __m256i catcodes,
    token_t* tokens,
    size_t max_tokens,
    size_t* token_count,
    uint16_t* line,
    uint16_t* col
) {
    /* Store catcodes to temporary buffer for scalar processing */
    uint8_t catcode_buf[32];
    _mm256_storeu_si256((__m256i*)catcode_buf, catcodes);
    
    size_t tokens_emitted = 0;
    
    for (size_t i = 0; i < 32 && *token_count < max_tokens; i++) {
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
static inline void prefetch_next_chunk(const void* addr) {
    _mm_prefetch((const char*)addr, _MM_HINT_T0);
}

/* Check if AVX2 is available at runtime */
static inline int has_avx2_support(void) {
    #ifdef _MSC_VER
        int cpu_info[4];
        __cpuid(cpu_info, 7);
        return (cpu_info[1] & (1 << 5)) != 0;
    #else
        return __builtin_cpu_supports("avx2");
    #endif
}

#endif /* LEXER_AVX2_H */