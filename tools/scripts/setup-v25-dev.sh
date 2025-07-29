#!/bin/bash
# LaTeX Perfectionist v25 - Development Environment Setup
# Week 1: Bootstrap development environment

set -euo pipefail

echo "=== LaTeX Perfectionist v25 Development Setup ==="
echo "Setting up OCaml 5.1.1, Coq 8.18, Dune 3.10 toolchain..."

# Check if opam is installed
if ! command -v opam &> /dev/null; then
    echo "Error: opam not found. Please install opam first:"
    echo "  brew install opam  # macOS"
    echo "  apt install opam   # Ubuntu/Debian"
    exit 1
fi

# Initialize opam if needed
if [ ! -d "$HOME/.opam" ]; then
    opam init --bare -a -y
fi

# Create v25 switch with exact versions
echo "Creating OCaml 5.1.1 switch for v25..."
opam switch create latex-perfectionist-v25 5.1.1 --yes || {
    echo "Switch already exists, using existing..."
    opam switch latex-perfectionist-v25
}

# Set up environment
eval $(opam env --switch=latex-perfectionist-v25)

# Install core dependencies
echo "Installing core dependencies..."
opam install -y \
    dune.3.10.0 \
    coq.8.18.0 \
    coq-core.8.18.0 \
    yojson.2.1.0 \
    ppx_deriving.5.2.1 \
    angstrom.0.16.0 \
    cmdliner.1.2.0 \
    alcotest.1.7.0 \
    odoc.2.4.0

# Install development tools
echo "Installing development tools..."
opam install -y \
    ocaml-lsp-server \
    ocamlformat.0.26.1 \
    utop \
    merlin

# Install performance-critical libraries
echo "Installing performance libraries..."
opam install -y \
    core_unix \
    lwt \
    lwt_ppx

# Create initial v25 directory structure
echo "Creating v25 project structure..."
mkdir -p src/core/layer0/{lexer,simd,cache}
mkdir -p src/core/layer0/tests
mkdir -p proofs/layer0
mkdir -p benchmarks/layer0

# Create dune-project if it doesn't exist
if [ ! -f "dune-project" ]; then
    echo "Creating dune-project..."
    cat > dune-project << 'EOF'
(lang dune 3.10)
(name latex-perfectionist)
(version 25.0.0-dev)
(generate_opam_files true)
(implicit_transitive_deps false)
(formatting (enabled_for ocaml))

(package
 (name latex-perfectionist)
 (synopsis "Real-time LaTeX validation with <1ms latency")
 (description "Formally verified LaTeX validator supporting 623 rules across 21 languages")
 (depends
  (ocaml (= 5.1.1))
  (dune (= 3.10))
  (coq (= 8.18))
  (coq-core (= 8.18))
  (yojson (>= 2.1))
  (ppx_deriving (>= 5.2))
  (angstrom (>= 0.16))
  (cmdliner (>= 1.2))
  (alcotest :with-test)
  (odoc :with-doc)))
EOF
fi

# Set up Rust toolchain for SIMD components
echo "Setting up Rust toolchain for SIMD..."
if ! command -v rustup &> /dev/null; then
    echo "Installing Rust..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source "$HOME/.cargo/env"
fi

# Install Rust nightly for SIMD features
rustup toolchain install nightly
rustup component add rust-src --toolchain nightly

# Create cargo workspace
if [ ! -f "Cargo.toml" ]; then
    cat > Cargo.toml << 'EOF'
[workspace]
members = ["src/core/layer0/simd"]
resolver = "2"

[workspace.package]
version = "25.0.0-dev"
edition = "2021"
authors = ["LaTeX Perfectionist Team"]

[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"

[profile.release-with-debug]
inherits = "release"
debug = true
EOF
fi

# Create SIMD crate structure
mkdir -p src/core/layer0/simd/src
cat > src/core/layer0/simd/Cargo.toml << 'EOF'
[package]
name = "latex-perfectionist-simd"
version.workspace = true
edition.workspace = true

[dependencies]

[build-dependencies]
cc = "1.0"

[features]
default = ["avx2"]
avx2 = []
avx512 = []
neon = []
EOF

# Create initial L0 module structure
cat > src/core/layer0/dune << 'EOF'
(library
 (name layer0)
 (public_name latex-perfectionist.layer0)
 (libraries core_unix lwt angstrom)
 (foreign_archives simd/libsimd)
 (foreign_stubs
  (language c)
  (names simd_stubs))
 (preprocess (pps ppx_deriving.std lwt_ppx)))

(rule
 (targets libsimd.a dllsimd.so)
 (deps (source_tree simd))
 (action
  (progn
   (chdir simd (run cargo build --release))
   (copy simd/target/release/liblatex_perfectionist_simd.a libsimd.a)
   (copy simd/target/release/liblatex_perfectionist_simd.so dllsimd.so))))
EOF

# Create test structure
cat > src/core/layer0/tests/dune << 'EOF'
(test
 (name test_layer0)
 (libraries layer0 alcotest))
EOF

# Create initial type definitions
cat > src/core/layer0/types.ml << 'EOF'
(** Core types for L0 Lexer - LaTeX Perfectionist v25 *)

type catcode = 
  | Escape      (* \ *)
  | BeginGroup  (* { *)
  | EndGroup    (* } *)
  | MathShift   (* $ *)
  | AlignTab    (* & *)
  | EndOfLine   (* \n *)
  | Parameter   (* # *)
  | Superscript (* ^ *)
  | Subscript   (* _ *)
  | Ignored     (* NUL *)
  | Space       (* space, tab *)
  | Letter      (* a-z, A-Z *)
  | Other       (* everything else *)
  | Active      (* ~ *)
  | Comment     (* % *)
  | Invalid     (* DEL *)

type position = {
  byte_offset : int;
  line : int;
  column : int;
}

type token = {
  kind : token_kind;
  span : position * position;
  raw : string;
}

and token_kind =
  | Command of string
  | Word of string
  | Number of string
  | Symbol of char
  | Whitespace of int (* count *)
  | Newline
  | CommentLine of string
  | BeginMath
  | EndMath
  | BeginDisplayMath
  | EndDisplayMath
  | OpenBrace
  | CloseBrace
  | OpenBracket
  | CloseBracket

type lexer_state = {
  position : position;
  catcode_table : catcode array; (* 256 entries *)
  buffer : bytes;
  buffer_pos : int;
  chunk_id : int;
}

(** Performance budget: 80μs p95, 160μs hard cutoff *)
EOF

echo "=== Setup Complete ==="
echo "Development environment ready for LaTeX Perfectionist v25"
echo ""
echo "Next steps:"
echo "1. eval \$(opam env --switch=latex-perfectionist-v25)"
echo "2. dune build"
echo "3. Begin L0 lexer implementation"