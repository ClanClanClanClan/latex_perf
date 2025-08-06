# LaTeX Perfectionist v25 Build System

# Direct compilation to avoid dune Thread.wait_signal issue
build-direct:
	@echo "Building with direct compilation (dune has Thread issue)..."
	@cd src/data && ocamlc -c *.mli && ocamlopt -O3 -c *.ml
	@cd src/core && ocamlc -I ../data -c lexer_v25.mli && ocamlopt -O3 -I ../data -c lexer_v25.ml
	@cd src/core && ocamlopt -O3 -I ../data -c l0_lexer_track_a_perfect.ml
	@cd src/core && ocamlc -I ../data -c l0_lexer.mli && ocamlopt -O3 -I ../data -c l0_lexer.ml
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

.PHONY: build build-direct quick coq clean test-perf