#!/bin/bash
# VSNA Development Environment Setup Script

set -euo pipefail

echo "🚀 Setting up VSNA development environment..."

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Print colored output
print_status() {
    echo -e "${GREEN}✓${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}⚠${NC} $1"
}

print_error() {
    echo -e "${RED}❌${NC} $1"
}

# Check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Check system requirements
echo "📋 Checking system requirements..."

# Check for required commands
REQUIRED_COMMANDS=("opam" "git" "make")
for cmd in "${REQUIRED_COMMANDS[@]}"; do
    if command_exists "$cmd"; then
        print_status "$cmd is installed"
    else
        print_error "$cmd is required but not installed"
        exit 1
    fi
done

# Check OCaml/Opam setup
if command_exists "opam"; then
    OPAM_VERSION=$(opam --version)
    print_status "OPAM version: $OPAM_VERSION"
    
    if ! opam switch list | grep -q "ocaml"; then
        print_warning "No OPAM switch found, creating default..."
        opam switch create default ocaml-base-compiler.5.0.0
        eval $(opam env)
    fi
else
    print_error "OPAM is required for VSNA development"
    exit 1
fi

# Install Coq and dependencies
echo "📦 Installing Coq and dependencies..."

# Update OPAM
opam update

# Install core dependencies
PACKAGES=(
    "coq.8.18.0"
    "dune.3.0"
    "alcotest.1.7.0"
    "benchmark.1.6"
    "cmdliner.1.2.0"
    "lwt.5.7.0"
)

for package in "${PACKAGES[@]}"; do
    if opam list --installed | grep -q "$(echo $package | cut -d. -f1)"; then
        print_status "$package already installed"
    else
        echo "Installing $package..."
        opam install -y "$package"
        print_status "$package installed"
    fi
done

# Verify Coq installation
if command_exists "coqc"; then
    COQ_VERSION=$(coqc --version | head -n1)
    print_status "Coq installed: $COQ_VERSION"
else
    print_error "Coq installation failed"
    exit 1
fi

# Setup project directory structure
echo "📁 Setting up project structure..."

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$PROJECT_ROOT"

# Ensure all directories exist
DIRECTORIES=(
    "src/coq/vsna"
    "src/coq/extraction" 
    "src/coq/rules"
    "src/coq/utilities"
    "src/ocaml/lib"
    "src/ocaml/bin"
    "tests/unit/vsna"
    "tests/integration"
    "benchmarks/baseline"
    "docs/api"
    "build"
)

for dir in "${DIRECTORIES[@]}"; do
    if [ ! -d "$dir" ]; then
        mkdir -p "$dir"
        print_status "Created directory: $dir"
    fi
done

# Initialize git hooks (if in git repo)
if [ -d ".git" ]; then
    echo "🔧 Setting up git hooks..."
    
    # Pre-commit hook to check for admits
    cat > .git/hooks/pre-commit << 'EOF'
#!/bin/bash
# Pre-commit hook: Check for admits in Coq code

if git diff --cached --name-only | grep -q "\.v$"; then
    echo "Checking for admits in Coq files..."
    if git diff --cached | grep -E "(admit|Admitted)" --color=never; then
        echo "❌ Found admits in staged Coq files"
        echo "Please complete proofs before committing"
        exit 1
    fi
    echo "✓ No admits found"
fi
EOF
    
    chmod +x .git/hooks/pre-commit
    print_status "Git pre-commit hook installed"
fi

# Create development configuration
echo "⚙️ Creating development configuration..."

# Create .vscode settings if not exists
if [ ! -f ".vscode/settings.json" ]; then
    mkdir -p .vscode
    cat > .vscode/settings.json << 'EOF'
{
    "coq.autoRevealProof": true,
    "coq.format.enable": true,
    "coq.format.indentSize": 2,
    "editor.rulers": [80],
    "files.trimTrailingWhitespace": true,
    "ocaml.sandbox": {
        "kind": "opam",
        "switch": "default"
    }
}
EOF
    print_status "VS Code settings created"
fi

# Test basic build
echo "🧪 Testing basic build..."

if [ -f "Makefile.vsna" ]; then
    if make -f Makefile.vsna help > /dev/null 2>&1; then
        print_status "Build system working"
    else
        print_warning "Build system test failed"
    fi
fi

# Generate completion message
echo ""
echo "🎉 VSNA development environment setup complete!"
echo ""
echo "Next steps:"
echo "1. Run: make -f Makefile.vsna phase1    # Build Phase 1"
echo "2. Run: make -f Makefile.vsna test      # Run tests"
echo "3. Run: make -f Makefile.vsna benchmark # Run benchmarks"
echo ""
echo "Development commands:"
echo "- make -f Makefile.vsna help           # Show all targets"
echo "- make -f Makefile.vsna check-admits   # Verify no admits"
echo "- make -f Makefile.vsna status         # Show system status"
echo ""
echo "Documentation:"
echo "- docs/implementation/Development-Guidelines.md"
echo "- docs/implementation/Phase-Gate-Plan.md"
echo "- docs/architecture/VSNA-Master-Architecture.md"
echo ""

# Final verification
echo "🔍 Final verification..."
eval $(opam env)
print_status "OPAM environment configured"
print_status "Ready for VSNA development!"