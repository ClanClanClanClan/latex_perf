#!/bin/bash
# build.sh - Build script for v24-R3 incremental lexer

echo "Building LaTeX Perfectionist v24-R3 Incremental Lexer..."

# Compile modules in dependency order
ocamlc -c types.ml
ocamlc -c core_lexer.ml
ocamlc -c state_codec.ml
ocamlc -c line_processor.ml
ocamlc -c checkpoint_manager.ml
ocamlc -c ring_buffer.ml
ocamlc -c incremental_lexer.ml

# Create library
ocamlc -a -o incremental_lexer.cma \
  types.cmo \
  core_lexer.cmo \
  state_codec.cmo \
  line_processor.cmo \
  checkpoint_manager.cmo \
  ring_buffer.cmo \
  incremental_lexer.cmo

# Compile test program
ocamlc -o test_incremental unix.cma incremental_lexer.cma test_incremental.ml

# Build optimized version
echo "Building optimized version..."
ocamlopt -c types.ml
ocamlopt -c core_lexer.ml
ocamlopt -c state_codec.ml
ocamlopt -c line_processor.ml
ocamlopt -c checkpoint_manager.ml
ocamlopt -c ring_buffer.ml
ocamlopt -c incremental_lexer.ml

ocamlopt -a -o incremental_lexer.cmxa \
  types.cmx \
  core_lexer.cmx \
  state_codec.cmx \
  line_processor.cmx \
  checkpoint_manager.cmx \
  ring_buffer.cmx \
  incremental_lexer.cmx

ocamlopt -o test_incremental_opt unix.cmxa incremental_lexer.cmxa test_incremental.ml

echo "Build complete!"
echo "Run tests with: ./test_incremental_opt"