# Phase C - SIMD Microkernel Makefile
# Build SIMD tokenizer with OCaml FFI bindings

# Configuration
CC = gcc
OCAMLOPT = ocamlopt
OCAMLC = ocamlc

# Architecture detection
ARCH := $(shell uname -m)

# Compiler flags
CFLAGS = -O3 -fPIC -Wall -Wextra
# SIMD flags based on architecture
ifeq ($(ARCH),x86_64)
    CFLAGS += -mavx2 -DUSE_AVX2
    ARCH_NAME = AVX2
else ifeq ($(findstring arm,$(ARCH)),arm)
    CFLAGS += -DUSE_NEON
    ARCH_NAME = NEON
else ifeq ($(findstring aarch,$(ARCH)),aarch)
    CFLAGS += -DUSE_NEON
    ARCH_NAME = NEON
else
    ARCH_NAME = Scalar
endif

# Include paths
OPAM_PREFIX = $(shell opam var prefix 2>/dev/null || echo "")
ifneq ($(OPAM_PREFIX),)
    INCLUDES = -I$(OPAM_PREFIX)/lib/ocaml
else
    INCLUDES = -I/usr/local/lib/ocaml
endif

# Source files
C_SOURCES = simd_tokenizer.c simd_stubs.c
ML_SOURCES = simd_ffi.ml
HEADERS = simd_tokenizer.h

# Object files
C_OBJECTS = $(C_SOURCES:.c=.o)
ML_OBJECTS = simd_ffi.cmx simd_ffi.cmi

# Library files
STATIC_LIB = libsimd_tokenizer.a
SHARED_LIB = libsimd_tokenizer.so

# Default target
all: $(STATIC_LIB) $(ML_OBJECTS) simd_test

# Display configuration
info:
	@echo "Building SIMD tokenizer for architecture: $(ARCH_NAME)"
	@echo "CFLAGS: $(CFLAGS)"
	@echo "CC: $(CC)"

# Compile C sources
%.o: %.c $(HEADERS)
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

# Create static library
$(STATIC_LIB): $(C_OBJECTS)
	ar rcs $@ $^

# Create shared library
$(SHARED_LIB): $(C_OBJECTS)
	$(CC) -shared $(CFLAGS) -o $@ $^

# Compile OCaml interface
simd_ffi.cmi: simd_ffi.ml
	$(OCAMLC) -I +unix -I +str -c $<

simd_ffi.cmx: simd_ffi.ml
	$(OCAMLOPT) -I +unix -I +str -c $<

# Test program
simd_test: simd_test.c $(STATIC_LIB)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $< -L. -lsimd_tokenizer

# Create test program source
simd_test.c:
	@echo '#include <stdio.h>' > $@
	@echo '#include <stdlib.h>' >> $@
	@echo '#include <string.h>' >> $@
	@echo '#include "simd_tokenizer.h"' >> $@
	@echo '' >> $@
	@echo 'int main() {' >> $@
	@echo '    const char *test_input = "\\\\alpha + \\\\beta = {x + y}";' >> $@
	@echo '    size_t input_len = strlen(test_input);' >> $@
	@echo '    ' >> $@
	@echo '    simd_token_buffer_t *buf = simd_create_buffer(1000);' >> $@
	@echo '    if (!buf) { printf("Failed to create buffer\\n"); return 1; }' >> $@
	@echo '    ' >> $@
	@echo '    int tokens = simd_tokenize((const uint8_t*)test_input, input_len, buf);' >> $@
	@echo '    printf("SIMD Tokenizer Test:\\n");' >> $@
	@echo '    printf("Architecture: $(ARCH_NAME)\\n");' >> $@
	@echo '    printf("Input: %s\\n", test_input);' >> $@
	@echo '    printf("Tokens generated: %d\\n", tokens);' >> $@
	@echo '    ' >> $@
	@echo '    for (int i = 0; i < tokens && i < 10; i++) {' >> $@
	@echo '        printf("Token %d: kind=%d, code=%d, pos=%d-%d\\n", ' >> $@
	@echo '               i, buf->kinds[i], buf->codes[i], ' >> $@
	@echo '               buf->start_pos[i], buf->end_pos[i]);' >> $@
	@echo '    }' >> $@
	@echo '    ' >> $@
	@echo '    simd_free_buffer(buf);' >> $@
	@echo '    return 0;' >> $@
	@echo '}' >> $@

# Performance benchmark
benchmark: benchmark.c $(STATIC_LIB)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $< -L. -lsimd_tokenizer

benchmark.c:
	@echo '#include <stdio.h>' > $@
	@echo '#include <stdlib.h>' >> $@
	@echo '#include <string.h>' >> $@
	@echo '#include <time.h>' >> $@
	@echo '#include "simd_tokenizer.h"' >> $@
	@echo '' >> $@
	@echo 'int main() {' >> $@
	@echo '    const char *test_input = "\\\\documentclass{article} \\\\begin{document} Hello \\\\alpha + \\\\beta = {x^2 + y^2} \\\\end{document}";' >> $@
	@echo '    size_t input_len = strlen(test_input);' >> $@
	@echo '    int iterations = 100000;' >> $@
	@echo '    ' >> $@
	@echo '    simd_token_buffer_t *simd_buf = simd_create_buffer(10000);' >> $@
	@echo '    simd_token_buffer_t *scalar_buf = simd_create_buffer(10000);' >> $@
	@echo '    ' >> $@
	@echo '    clock_t start = clock();' >> $@
	@echo '    for (int i = 0; i < iterations; i++) {' >> $@
	@echo '        simd_vs_scalar_benchmark((const uint8_t*)test_input, input_len, simd_buf, scalar_buf);' >> $@
	@echo '    }' >> $@
	@echo '    clock_t end = clock();' >> $@
	@echo '    ' >> $@
	@echo '    double time_per_iter = ((double)(end - start)) / CLOCKS_PER_SEC / iterations * 1000;' >> $@
	@echo '    printf("SIMD vs Scalar Benchmark ($(ARCH_NAME)):\\n");' >> $@
	@echo '    printf("Iterations: %d\\n", iterations);' >> $@
	@echo '    printf("Time per iteration: %.3f ms\\n", time_per_iter);' >> $@
	@echo '    printf("SIMD tokens: %d, Scalar tokens: %d\\n", simd_buf->count, scalar_buf->count);' >> $@
	@echo '    ' >> $@
	@echo '    simd_free_buffer(simd_buf);' >> $@
	@echo '    simd_free_buffer(scalar_buf);' >> $@
	@echo '    return 0;' >> $@
	@echo '}' >> $@

# Clean
clean:
	rm -f *.o *.cmi *.cmx *.cmo *.a *.so simd_test simd_test.c benchmark benchmark.c

# Install (copy to parent directory for integration)
install: $(STATIC_LIB) $(ML_OBJECTS)
	cp $(STATIC_LIB) ../
	cp simd_ffi.cmi simd_ffi.cmx ../
	cp simd_tokenizer.h ../

# Run tests
test: simd_test
	./simd_test

# Run benchmarks
bench: benchmark
	./benchmark

.PHONY: all clean install test bench info