# Installation Guide

## Prerequisites

- **Coq**: Version 8.17+ required
  ```bash
  opam install coq
  ```

- **OCaml**: Version 4.14+ required
  ```bash
  opam install ocaml
  ```

- **Build Tools**: Make, Git
  ```bash
  # Linux/macOS
  sudo apt install build-essential git  # Ubuntu
  brew install make git                  # macOS
  ```

## Quick Installation

1. **Clone Repository**
   ```bash
   git clone <repository-url>
   cd latex-perfectionist-v24
   ```

2. **Build Core Components**
   ```bash
   coq_makefile -f _CoqProject -o CoqMakefile
   make -f CoqMakefile
   ```

3. **Verify Installation**
   ```bash
   make validation
   ```

## Build Targets

- `make -f CoqMakefile all` - Build all Coq components
- `make validation` - Verify system integrity
- `make clean` - Clean build artifacts

## Troubleshooting

### Common Issues

**Import errors**: Ensure Coq can find the modules:
```bash
coq_makefile -f _CoqProject -o CoqMakefile
```

**Performance issues**: Some proof files may take time to compile:
```bash
timeout 60 make -f CoqMakefile <target>
```

**Missing dependencies**: Check opam packages:
```bash
opam list --installed
```

## Next Steps

- See [Quick Start Guide](quick_start.md) for basic usage
- Check [User Guide](user_guide.md) for detailed features