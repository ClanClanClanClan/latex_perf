# LaTeX Perfectionist v25 - Master Makefile

.PHONY: all build coq quick clean test help

# Default target
all: build coq

# OCaml build
build:
	dune build

# Coq proofs
coq:
	dune build @coq

# Quick build for development
quick:
	dune build --profile dev

# Run tests
test:
	dune test

# Clean build artifacts
clean:
	dune clean
	rm -rf .lia.cache .CoqMakefile.d .Makefile.coq.d .Makefile.d

# Help
help:
	@echo "LaTeX Perfectionist v25 Build System"
	@echo "Available targets:"
	@echo "  all     - Build OCaml + Coq (default)"
	@echo "  build   - Build OCaml only"
	@echo "  coq     - Build Coq proofs only"
	@echo "  quick   - Fast development build"
	@echo "  test    - Run test suite"
	@echo "  clean   - Clean build artifacts"