#!/bin/bash
# Clean build script for LaTeX Perfectionist v25
set -e

echo "🔧 Setting up OCaml environment..."
eval $(opam env)

echo "🧹 Cleaning previous builds..."
dune clean

echo "🏗️  Building all components..."
dune build

echo "🧪 Building tests..."
dune build test/

echo "✅ Build complete!"
