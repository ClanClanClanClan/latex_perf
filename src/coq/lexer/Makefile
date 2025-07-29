# Makefile for LaTeX Perfectionist Formal Lexer

COQC = coqc
COQDEP = coqdep
OCAMLOPT = ocamlopt
OCAMLC = ocamlc

# Source files
COQ_SOURCES = Lexer.v LexerProofs.v LexerExtraction.v
ML_EXTRACTED = latex_tokenize.ml latex_lexer_sig.mli

# Targets
.PHONY: all clean extract compile test

all: extract compile

# Compile Coq files
%.vo: %.v
	$(COQC) $<

# Dependencies
.depend: $(COQ_SOURCES)
	$(COQDEP) $(COQ_SOURCES) > .depend

-include .depend

# Extract to OCaml
extract: Lexer.vo LexerProofs.vo LexerExtraction.vo
	@echo "Extraction complete. Generated files: $(ML_EXTRACTED)"

# Compile extracted OCaml code
compile: extract
	$(OCAMLOPT) -O3 -c latex_lexer_sig.mli
	$(OCAMLOPT) -O3 -c latex_tokenize.ml
	$(OCAMLOPT) -O3 -shared -o latex_lexer.cmxs latex_tokenize.cmx
	@echo "OCaml compilation complete."

# Build integration test
test: compile
	@echo "Building lexer tests..."
	$(OCAMLOPT) -O3 -o test_lexer test_lexer.ml latex_tokenize.cmx

# Clean build artifacts
clean:
	rm -f *.vo *.vok *.vos *.glob
	rm -f $(ML_EXTRACTED)
	rm -f *.cmi *.cmx *.cmo *.o
	rm -f *.cmxs *.cma *.a
	rm -f .depend
	rm -f test_lexer

# Performance benchmark
bench: compile
	$(OCAMLOPT) -O3 -o bench_lexer bench_lexer.ml latex_tokenize.cmx
	./bench_lexer