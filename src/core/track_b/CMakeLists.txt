# LaTeX Perfectionist v25 - Track B C Kernel Build System
cmake_minimum_required(VERSION 3.16)
project(LatexPerfectionistTrackB VERSION 1.0.0 LANGUAGES C)

# === BUILD CONFIGURATION ===

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)

# Optimization flags
set(CMAKE_C_FLAGS_RELEASE "-O3 -DNDEBUG -march=native -flto")
set(CMAKE_C_FLAGS_DEBUG "-O0 -g -DDEBUG -fsanitize=address,undefined")

# Default to Release build
if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif()

# === FEATURE DETECTION ===

include(CheckCSourceCompiles)

# Check for AVX2 support
check_c_source_compiles("
#include <immintrin.h>
int main() {
    __m256i a = _mm256_setzero_si256();
    return 0;
}
" HAVE_AVX2)

# Check for AVX-512 support  
check_c_source_compiles("
#include <immintrin.h>
int main() {
    __m512i a = _mm512_setzero_si512();
    return 0;
}
" HAVE_AVX512)

# Check for NEON support (ARM)
check_c_source_compiles("
#include <arm_neon.h>
int main() {
    uint8x16_t a = vdupq_n_u8(0);
    return 0;
}
" HAVE_NEON)

# === SOURCE FILES ===

set(ARENA_SOURCES
    c/arena/arena.c
    c/arena/arena.h
)

set(SCALAR_SOURCES
    c/scalar/lexer_scalar.c
    c/scalar/lexer_scalar.h
)

set(SIMD_SOURCES)
set(SIMD_FLAGS)

# Add SIMD sources based on capabilities
if(HAVE_AVX2)
    list(APPEND SIMD_SOURCES c/simd/lexer_avx2.c c/simd/lexer_avx2.h)
    list(APPEND SIMD_FLAGS -mavx2)
    add_definitions(-DHAVE_AVX2=1)
endif()

# Disable AVX512 for now - not implemented yet
#if(HAVE_AVX512)
#    list(APPEND SIMD_SOURCES c/simd/lexer_avx512.c c/simd/lexer_avx512.h) 
#    list(APPEND SIMD_FLAGS -mavx512f -mavx512bw)
#    add_definitions(-DHAVE_AVX512=1)
#endif()

if(HAVE_NEON)
    list(APPEND SIMD_SOURCES c/simd/lexer_neon.c c/simd/lexer_neon.h)
    add_definitions(-DHAVE_NEON=1)
endif()

set(COMMON_SOURCES
    c/lexer_types.h
    c/feature_detect.c
    c/feature_detect.h
    c/lexer_main.c
)

set(ALL_SOURCES
    ${ARENA_SOURCES}
    ${SCALAR_SOURCES}
    ${SIMD_SOURCES}
    ${COMMON_SOURCES}
)

# === TARGETS ===

# Static library for OCaml linking
add_library(lexer_track_b STATIC ${ALL_SOURCES})

# Set SIMD compile flags
if(SIMD_FLAGS)
    target_compile_options(lexer_track_b PRIVATE ${SIMD_FLAGS})
endif()

# Include directories
target_include_directories(lexer_track_b PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/c
    ${CMAKE_CURRENT_SOURCE_DIR}/c/arena
    ${CMAKE_CURRENT_SOURCE_DIR}/c/scalar
    ${CMAKE_CURRENT_SOURCE_DIR}/c/simd
)

# === TESTING ===

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    enable_testing()
    
    # Arena tests
    add_executable(test_arena tests/test_arena.c ${ARENA_SOURCES})
    target_compile_definitions(test_arena PRIVATE ARENA_TESTING=1)
    target_include_directories(test_arena PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/c)
    add_test(NAME arena_tests COMMAND test_arena)
    
    # Scalar lexer tests
    add_executable(test_scalar tests/test_scalar.c ${ALL_SOURCES})
    target_compile_definitions(test_scalar PRIVATE LEXER_TESTING=1)
    target_include_directories(test_scalar PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/c)
    add_test(NAME scalar_tests COMMAND test_scalar)
    
    # SIMD correctness tests (compare against scalar)
    if(SIMD_SOURCES)
        add_executable(test_simd tests/test_simd.c ${ALL_SOURCES})
        target_compile_definitions(test_simd PRIVATE SIMD_TESTING=1)
        target_compile_options(test_simd PRIVATE ${SIMD_FLAGS})
        target_include_directories(test_simd PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/c)
        add_test(NAME simd_tests COMMAND test_simd)
    endif()
endif()

# === BENCHMARKING ===

# Benchmark executable disabled until test file is created
#add_executable(bench_track_b tests/bench_track_b.c ${ALL_SOURCES})
#target_compile_definitions(bench_track_b PRIVATE LEXER_PROFILE=1)
#if(SIMD_FLAGS)
#    target_compile_options(bench_track_b PRIVATE ${SIMD_FLAGS})
#endif()
#target_include_directories(bench_track_b PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/c)

# === INSTALLATION ===

install(TARGETS lexer_track_b
    ARCHIVE DESTINATION lib
    LIBRARY DESTINATION lib
)

install(FILES
    c/lexer_types.h
    c/arena/arena.h
    c/scalar/lexer_scalar.h
    DESTINATION include/lexer_track_b
)

# === STATUS SUMMARY ===

message(STATUS "Track B Build Configuration:")
message(STATUS "  Build Type: ${CMAKE_BUILD_TYPE}")
message(STATUS "  C Compiler: ${CMAKE_C_COMPILER_ID} ${CMAKE_C_COMPILER_VERSION}")
message(STATUS "  AVX2 Support: ${HAVE_AVX2}")
message(STATUS "  AVX-512 Support: ${HAVE_AVX512}")
message(STATUS "  NEON Support: ${HAVE_NEON}")
message(STATUS "  SIMD Sources: ${SIMD_SOURCES}")

if(NOT HAVE_AVX2 AND NOT HAVE_AVX512 AND NOT HAVE_NEON)
    message(WARNING "No SIMD support detected - only scalar implementation will be built")
endif()