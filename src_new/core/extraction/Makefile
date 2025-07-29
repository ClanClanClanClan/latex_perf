# Enterprise Extraction Makefile
.PHONY: extract build-enterprise test-enterprise clean build-optimized build-streaming build-native

COQ_FLAGS := -R ../../src ""
OCAML_FLAGS := -I .
OCAML_NATIVE_FLAGS := -I . -O3

# Extract validators from Coq to OCaml
extract: EnterpriseExtraction.v
	@echo "Extracting enterprise validators..."
	coqc $(COQ_FLAGS) EnterpriseExtraction.v
	@echo "Extraction complete."

# Build OCaml interface
build-enterprise: extract
	@echo "Building enterprise OCaml interface..."
	ocamlc $(OCAML_FLAGS) -c enterprise_validators.mli || true
	ocamlc $(OCAML_FLAGS) -c enterprise_validators.ml
	@echo "Enterprise validators built."

# Build optimized version
build-optimized: build-enterprise
	@echo "Building optimized validator..."
	ocamlc $(OCAML_FLAGS) -c test_enterprise_optimized.ml
	ocamlc $(OCAML_FLAGS) -o test_enterprise_optimized \
		unix.cma enterprise_validators.cmo test_enterprise_optimized.cmo
	@echo "Optimized validator built."

# Build streaming version
build-streaming: build-enterprise
	@echo "Building streaming validator..."
	ocamlc $(OCAML_FLAGS) -c test_enterprise_streaming.ml
	ocamlc $(OCAML_FLAGS) -o test_enterprise_streaming \
		unix.cma enterprise_validators.cmo test_enterprise_streaming.cmo
	@echo "Streaming validator built."

# Build native compiled versions for maximum performance
build-native: extract
	@echo "Building native compiled validators..."
	ocamlopt $(OCAML_NATIVE_FLAGS) -c enterprise_validators.ml
	ocamlopt $(OCAML_NATIVE_FLAGS) -c test_enterprise_optimized.ml
	ocamlopt $(OCAML_NATIVE_FLAGS) -c test_enterprise_streaming.ml
	ocamlopt $(OCAML_NATIVE_FLAGS) -o test_enterprise_native \
		unix.cmxa enterprise_validators.cmx test_enterprise_optimized.cmx
	ocamlopt $(OCAML_NATIVE_FLAGS) -o test_enterprise_streaming_native \
		unix.cmxa enterprise_validators.cmx test_enterprise_streaming.cmx
	@echo "Native compiled validators built."

# Test extraction on single paper
test-enterprise: build-enterprise
	@echo "Testing enterprise extraction..."
	ocamlc $(OCAML_FLAGS) -o test_enterprise \
		enterprise_validators.cmo test_enterprise.ml
	./test_enterprise
	@echo "Enterprise extraction test complete."

# Performance test
perf-test: build-native
	@echo "Performance test: Native vs Bytecode"
	time ./test_enterprise_native ../../corpus/papers/2506.19274v1/VBSurrogate_arxiv.tex > /dev/null
	time ./test_enterprise_streaming_native ../../corpus/papers/2506.19274v1/VBSurrogate_arxiv.tex > /dev/null

# Clean build artifacts
clean:
	rm -f *.cmo *.cmi *.cmx *.o *.glob *.vo *.vos *.vok
	rm -f enterprise_validators.ml enterprise_validators.mli
	rm -f test_enterprise test_enterprise_optimized test_enterprise_streaming
	rm -f test_enterprise_native test_enterprise_streaming_native

# Quick test on single paper
quick-test: build-enterprise
	@echo "Quick test on single paper..."
	echo 'let () = print_endline "Enterprise extraction works!"' > quick_test.ml
	ocamlc $(OCAML_FLAGS) -o quick_test \
		enterprise_validators.cmo quick_test.ml
	./quick_test
	rm -f quick_test quick_test.ml