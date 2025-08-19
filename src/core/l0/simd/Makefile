# Makefile for SIMD lexer development
# Per planner_v25_R1.yaml Section 8 - SIMD Implementation

# Find OCaml paths properly
OCAML_INCLUDE = $(shell OPAMSWITCH=l0-testing opam exec -- ocamlc -where)
OCAML_LIB = $(shell OPAMSWITCH=l0-testing opam exec -- ocamlc -where)

# Detect architecture for SIMD flags
ARCH = $(shell uname -m)
ifeq ($(ARCH),x86_64)
    SIMD_FLAGS = -mavx2 -mfma
    SIMD_DEFS = -D__AVX2__
else ifeq ($(ARCH),arm64)
    SIMD_FLAGS = -march=armv8-a+simd
    SIMD_DEFS = -D__ARM_NEON
else
    SIMD_FLAGS =
    SIMD_DEFS =
endif

# Compilation flags
CFLAGS = -O3 -fPIC -I$(OCAML_INCLUDE) $(SIMD_FLAGS) $(SIMD_DEFS)
OCAMLOPT_FLAGS = -O3 -I +unix

# Files
C_STUB = simd_stubs.c
ML_STUB = simd_lexer_stub.ml
TARGET = simd_lexer_test

.PHONY: all clean test benchmark

all: $(TARGET)

# Compile C stub to object file
simd_stubs.o: $(C_STUB)
	@echo "🔧 Compiling SIMD C stubs for $(ARCH)..."
	gcc $(CFLAGS) -c $(C_STUB) -o simd_stubs.o

# Build SIMD test binary
$(TARGET): simd_stubs.o $(ML_STUB)
	@echo "🚀 Building SIMD lexer test binary..."
	OPAMSWITCH=l0-testing opam exec -- ocamlopt $(OCAMLOPT_FLAGS) \
		-o $(TARGET) unix.cmxa simd_stubs.o $(ML_STUB)

# Test SIMD implementation
test: $(TARGET)
	@echo "🧪 Testing SIMD implementation..."
	@if [ -f "../../corpora/perf/edit_window_4kb.tex" ]; then \
		./$(TARGET) ../../corpora/perf/edit_window_4kb.tex 5; \
	else \
		echo "⚠️  Test corpus not found, using $(ML_STUB) as test input"; \
		./$(TARGET) $(ML_STUB) 5; \
	fi

# Benchmark against scalar
benchmark: $(TARGET)
	@echo "📊 Running SIMD vs Scalar benchmark..."
	@if [ -f "../../../latex_perfectionist_cli" ]; then \
		./$(TARGET) ../../../corpora/perf/perf_smoke_big.tex 20; \
	else \
		echo "❌ CLI binary not found, build it first with: make -C ../../.."; \
	fi

# Development: quick compile check
check: $(C_STUB)
	@echo "✅ Checking C stub compilation..."
	gcc $(CFLAGS) -fsyntax-only $(C_STUB)
	@echo "✅ C stub syntax OK for $(ARCH) with flags: $(SIMD_FLAGS)"

# Show compilation info
info:
	@echo "📋 SIMD Build Configuration"
	@echo "=========================="
	@echo "Architecture: $(ARCH)"
	@echo "SIMD flags:   $(SIMD_FLAGS)"
	@echo "SIMD defines: $(SIMD_DEFS)"
	@echo "OCaml include: $(OCAML_INCLUDE)"
	@echo "OCaml lib:     $(OCAML_LIB)"

clean:
	rm -f *.o *.cmi *.cmx $(TARGET)
	@echo "🧹 Cleaned SIMD build artifacts"

# Development shortcuts
dev: check $(TARGET) test

# Performance gate check per planner
gate: $(TARGET)
	@echo "🚪 SIMD Performance Gate Check (planner_v25_R1.yaml)"
	@echo "Target: Tier B ≤8ms for 1.1MB corpus with --simd flag"
	./$(TARGET) ../../../corpora/perf/perf_smoke_big.tex 10 | tail -5