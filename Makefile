# LaTeX Perfectionist v25 Build System

# Direct compilation to avoid dune Thread.wait_signal issue
build-direct:
	@echo "Building with direct compilation (dune has Thread issue)..."
	@mkdir -p _manual_build
	@cd src/data && ocamlc -c *.mli && ocamlopt -O3 -c *.ml
	@cd src/core && ocamlc -I ../data -c lexer_v25.mli && ocamlopt -O3 -I ../data -c lexer_v25.ml
	@cd src/core && ocamlc -I ../data -c stream_state.mli && ocamlopt -O3 -I ../data -c stream_state.ml
	@cd src/core && ocamlc -I ../data -c tok_ring.mli && ocamlopt -O3 -I ../data -c tok_ring.ml
	@cd src/core && ocamlopt -O3 -I ../data -c l0_lexer_track_a_perfect.ml
	@cd src/core && ocamlopt -O3 -I ../data -c l0_lexer_track_a_enhanced.ml
	@cd src/core && ocamlopt -O3 -I ../data -c l0_lexer_track_a_ultra.ml
	@cd src/core && ocamlopt -O3 -I ../data -c l0_lexer_track_a_ultra_v2.ml
	@cd src/core && ocamlopt -O3 -I ../data -c l0_lexer_track_a_arena.ml
	@cd src/core && ocamlopt -O3 -I ../data -c catcode_simd_bridge.ml
	@cd src/core && ocamlc -I ../data -c version_vector.mli && ocamlopt -O3 -I ../data -c version_vector.ml
	@cd src/core && ocamlc -I ../data -c l1_expander.mli && ocamlopt -O3 -I ../data -c l1_expander.ml
	@cd src/core && ocamlc -I ../data -c l0_lexer.mli && ocamlopt -O3 -I ../data -c l0_lexer.ml
	@cd src/core && ocamlc -I ../data -c l2_parser.mli && ocamlopt -O3 -I ../data -c l2_parser.ml
	@cd src/core && ocamlopt -O3 -I ../data -c orchestrator.ml
	@echo "Build complete!"

# Dune targets (with workaround for Thread.wait_signal issue)
COQ_TARGET=@all

# Build OCaml code with dune (Thread.wait_signal workaround)
build:
	./dune-wrapper.sh build src/core/ src/data/

# Build all targets including Coq (may have Thread issue but completes)
quick:
	./dune-wrapper.sh build $(COQ_TARGET) || opam exec -- dune build $(COQ_TARGET)

coq:
	./dune-wrapper.sh build $(COQ_TARGET) || opam exec -- dune build $(COQ_TARGET)

proofs.pdf:
	opam exec -- dune build proofs/docs/proofs.pdf

clean:
	opam exec -- dune clean
	@rm -f src/data/*.cm* src/core/*.cm*

# Performance test
test-perf: build-direct
	@ocamlopt -O3 -I src/data -I src/core -I +unix -o perf_test \
		unix.cmxa src/data/location.cmx src/data/catcode.cmx src/data/chunk.cmx \
		src/data/dlist.cmx src/data/data.cmx src/core/lexer_v25.cmx \
		src/core/l0_lexer_track_a_perfect.cmx src/core/l0_lexer.cmx perf_test.ml
	@./perf_test

# Performance gate assessment (Week 4/5 targets)
test-gates: build-direct
	@./scripts/performance_gate_harness.py

# Test L1 expander
test-l1: build-direct
	@ocamlopt -O3 -I src/data -I src/core -I +unix -o test_l1_expander \
		unix.cmxa src/data/location.cmx src/data/catcode.cmx src/data/chunk.cmx \
		src/data/dlist.cmx src/data/data.cmx src/core/lexer_v25.cmx \
		src/core/stream_state.cmx src/core/tok_ring.cmx \
		src/core/l0_lexer_track_a_arena.cmx src/core/l1_expander.cmx \
		test/test_l1_expander.ml
	@./test_l1_expander
	@rm -f test_l1_expander

# Test L0→L1 pipeline
test-pipeline: build-direct
	@ocamlopt -O3 -I src/data -I src/core -I +unix -o test_l0_l1_pipeline \
		unix.cmxa src/data/location.cmx src/data/catcode.cmx src/data/chunk.cmx \
		src/data/dlist.cmx src/data/data.cmx src/core/lexer_v25.cmx \
		src/core/stream_state.cmx src/core/tok_ring.cmx \
		src/core/l0_lexer_track_a_arena.cmx src/core/l1_expander.cmx \
		test/test_l0_l1_pipeline.ml
	@./test_l0_l1_pipeline
	@rm -f test_l0_l1_pipeline

# Test L2 parser
test-l2: build-direct
	@ocamlopt -O3 -I src/data -I src/core -I +unix -o test_l2_parser \
		unix.cmxa src/data/location.cmx src/data/catcode.cmx src/data/chunk.cmx \
		src/data/dlist.cmx src/data/data.cmx src/core/lexer_v25.cmx \
		src/core/stream_state.cmx src/core/tok_ring.cmx \
		src/core/l0_lexer_track_a_arena.cmx src/core/l1_expander.cmx \
		src/core/l2_parser.cmx test/test_l2_parser.ml
	@./test_l2_parser
	@rm -f test_l2_parser

# Debug character coalescing
debug-coalescing: build-direct
	@ocamlopt -O3 -I src/data -I src/core -I +unix -o debug_character_coalescing \
		unix.cmxa src/data/location.cmx src/data/catcode.cmx src/data/chunk.cmx \
		src/data/dlist.cmx src/data/data.cmx src/core/lexer_v25.cmx \
		src/core/stream_state.cmx src/core/tok_ring.cmx \
		src/core/l0_lexer_track_a_arena.cmx src/core/l1_expander.cmx \
		src/core/l2_parser.cmx debug_character_coalescing.ml
	@./debug_character_coalescing
	@rm -f debug_character_coalescing

# Debug math parsing  
debug-math: build-direct
	@ocamlopt -O3 -I src/data -I src/core -I +unix -o debug_math_parsing \
		unix.cmxa src/data/location.cmx src/data/catcode.cmx src/data/chunk.cmx \
		src/data/dlist.cmx src/data/data.cmx src/core/lexer_v25.cmx \
		src/core/stream_state.cmx src/core/tok_ring.cmx \
		src/core/l0_lexer_track_a_arena.cmx src/core/l1_expander.cmx \
		src/core/l2_parser.cmx debug_math_parsing.ml
	@./debug_math_parsing
	@rm -f debug_math_parsing

# Test full L0→L1→L2 pipeline
test-full-pipeline: test-pipeline test-l2

.PHONY: build build-direct quick coq clean test-perf test-gates test-l1 test-pipeline test-l2 test-full-pipeline