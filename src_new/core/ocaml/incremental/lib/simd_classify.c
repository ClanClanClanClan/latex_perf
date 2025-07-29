/* simd_classify.c - SIMD-accelerated character classification */

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <immintrin.h>
#include <stdint.h>

/* Character classification using AVX2 */
/* Returns bitmask of special characters found */

#define SPECIAL_BACKSLASH (1 << 0)
#define SPECIAL_DOLLAR    (1 << 1)
#define SPECIAL_PERCENT   (1 << 2)
#define SPECIAL_BRACE_L   (1 << 3)
#define SPECIAL_BRACE_R   (1 << 4)
#define SPECIAL_NEWLINE   (1 << 5)

CAMLprim value caml_classify_chars_simd(value str, value start, value len) {
    CAMLparam3(str, start, len);
    
    const char* data = String_val(str) + Int_val(start);
    int length = Int_val(len);
    uint32_t found_mask = 0;
    
#ifdef __AVX2__
    if (length >= 32) {
        __m256i backslash = _mm256_set1_epi8('\\');
        __m256i dollar = _mm256_set1_epi8('$');
        __m256i percent = _mm256_set1_epi8('%');
        __m256i brace_l = _mm256_set1_epi8('{');
        __m256i brace_r = _mm256_set1_epi8('}');
        __m256i newline = _mm256_set1_epi8('\n');
        
        int i = 0;
        for (; i + 31 < length; i += 32) {
            __m256i chars = _mm256_loadu_si256((__m256i*)(data + i));
            
            uint32_t mask_backslash = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chars, backslash));
            uint32_t mask_dollar = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chars, dollar));
            uint32_t mask_percent = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chars, percent));
            uint32_t mask_brace_l = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chars, brace_l));
            uint32_t mask_brace_r = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chars, brace_r));
            uint32_t mask_newline = _mm256_movemask_epi8(_mm256_cmpeq_epi8(chars, newline));
            
            if (mask_backslash) found_mask |= SPECIAL_BACKSLASH;
            if (mask_dollar) found_mask |= SPECIAL_DOLLAR;
            if (mask_percent) found_mask |= SPECIAL_PERCENT;
            if (mask_brace_l) found_mask |= SPECIAL_BRACE_L;
            if (mask_brace_r) found_mask |= SPECIAL_BRACE_R;
            if (mask_newline) found_mask |= SPECIAL_NEWLINE;
            
            /* Early exit if all special chars found */
            if (found_mask == 0x3F) break;
        }
        
        /* Handle remaining bytes */
        for (; i < length; i++) {
            switch (data[i]) {
                case '\\': found_mask |= SPECIAL_BACKSLASH; break;
                case '$': found_mask |= SPECIAL_DOLLAR; break;
                case '%': found_mask |= SPECIAL_PERCENT; break;
                case '{': found_mask |= SPECIAL_BRACE_L; break;
                case '}': found_mask |= SPECIAL_BRACE_R; break;
                case '\n': found_mask |= SPECIAL_NEWLINE; break;
            }
        }
    } else
#endif
    {
        /* Fallback for non-AVX2 or small strings */
        for (int i = 0; i < length; i++) {
            switch (data[i]) {
                case '\\': found_mask |= SPECIAL_BACKSLASH; break;
                case '$': found_mask |= SPECIAL_DOLLAR; break;
                case '%': found_mask |= SPECIAL_PERCENT; break;
                case '{': found_mask |= SPECIAL_BRACE_L; break;
                case '}': found_mask |= SPECIAL_BRACE_R; break;
                case '\n': found_mask |= SPECIAL_NEWLINE; break;
            }
        }
    }
    
    CAMLreturn(Val_int(found_mask));
}

/* Find first occurrence of special character */
CAMLprim value caml_find_special_char(value str, value start, value len) {
    CAMLparam3(str, start, len);
    
    const char* data = String_val(str) + Int_val(start);
    int length = Int_val(len);
    
#ifdef __AVX2__
    if (length >= 32) {
        __m256i backslash = _mm256_set1_epi8('\\');
        __m256i dollar = _mm256_set1_epi8('$');
        __m256i percent = _mm256_set1_epi8('%');
        __m256i brace_l = _mm256_set1_epi8('{');
        __m256i brace_r = _mm256_set1_epi8('}');
        __m256i newline = _mm256_set1_epi8('\n');
        
        for (int i = 0; i + 31 < length; i += 32) {
            __m256i chars = _mm256_loadu_si256((__m256i*)(data + i));
            
            __m256i special = _mm256_or_si256(
                _mm256_or_si256(
                    _mm256_cmpeq_epi8(chars, backslash),
                    _mm256_cmpeq_epi8(chars, dollar)
                ),
                _mm256_or_si256(
                    _mm256_cmpeq_epi8(chars, percent),
                    _mm256_or_si256(
                        _mm256_cmpeq_epi8(chars, brace_l),
                        _mm256_or_si256(
                            _mm256_cmpeq_epi8(chars, brace_r),
                            _mm256_cmpeq_epi8(chars, newline)
                        )
                    )
                )
            );
            
            uint32_t mask = _mm256_movemask_epi8(special);
            if (mask) {
                int offset = __builtin_ctz(mask);
                CAMLreturn(Val_int(Int_val(start) + i + offset));
            }
        }
        
        /* Check remaining bytes */
        for (int i = (length / 32) * 32; i < length; i++) {
            char c = data[i];
            if (c == '\\' || c == '$' || c == '%' || 
                c == '{' || c == '}' || c == '\n') {
                CAMLreturn(Val_int(Int_val(start) + i));
            }
        }
    } else
#endif
    {
        /* Fallback for non-AVX2 or small strings */
        for (int i = 0; i < length; i++) {
            char c = data[i];
            if (c == '\\' || c == '$' || c == '%' || 
                c == '{' || c == '}' || c == '\n') {
                CAMLreturn(Val_int(Int_val(start) + i));
            }
        }
    }
    
    CAMLreturn(Val_int(-1));  /* Not found */
}