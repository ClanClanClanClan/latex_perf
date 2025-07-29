# Contributing Guide

## Development Workflow

### Getting Started
1. Read [Installation Guide](../user/installation.md)
2. Study [Master Architecture](MASTER_ARCHITECTURE.md)
3. Check [Project Status](../internal/PROJECT_STATUS.md)
4. Review [API Reference](api_reference.md)

### Code Style

#### Coq Code
```coq
(** Documentation: Use triple asterisk comments *)
Definition function_name (arg : type) : return_type :=
  (* Use 2-space indentation *)
  match arg with
  | Pattern => result
  end.
```

#### File Organization
- Keep proof files separate from algorithm files
- One main theorem per file for large proofs
- Group related definitions together
- Use meaningful module names

#### Naming Conventions
- **Types**: `CamelCase` (e.g., `latex_token`, `exp_state`)
- **Functions**: `snake_case` (e.g., `expand_macro`, `check_balance`)
- **Theorems**: `snake_case` (e.g., `expand_fuel_insensitive`)
- **Constants**: `UPPER_CASE` for important constants

### Formal Verification Requirements

#### Zero Axioms Policy
- **No `Axiom`** declarations allowed in active code
- **No `admit`** tactics allowed in completed proofs
- All theorems must have complete constructive proofs

#### Proof Structure
```coq
Theorem theorem_name : forall (x : Type), P x -> Q x.
Proof.
  intros x H.
  (* Step-by-step proof *)
  (* Use tactics: induction, destruct, apply, exact, etc. *)
  exact proof_term.
Qed.
```

### Performance Guidelines

#### Compilation Time
- Individual files should compile in <30 seconds
- Complex proofs may be extracted to separate files
- Use `timeout 60` for performance testing

#### Runtime Performance
- L1 expander must meet 42ms SLA
- Validation rules should be O(n) in document size
- Use performance profiling for optimization

### Testing Requirements

#### Unit Tests
- Test files in `tests/unit/` directory
- One test file per major function
- Cover edge cases and error conditions

#### Integration Tests
- Test files in `tests/integration/` directory  
- Test complete L0→L1→V1½ pipeline
- Use realistic LaTeX documents

#### Performance Tests
- Benchmark critical paths
- Verify SLA compliance
- Test with large documents

### Documentation Standards

#### Code Documentation
```coq
(** * Module Title
    Brief description of module purpose
    
    Key functions:
    - function1: brief description
    - function2: brief description
*)

(** Helper function for X
    @param input: description
    @return: description
    
    Example usage:
    Definition example := function_name input.
*)
Definition function_name (input : type) : return_type :=
```

#### File Headers
```coq
(** * LaTeX Perfectionist v24 - Module Name
    
    Week X-Y Deliverable: Brief description
    
    This module implements:
    - Feature 1: description
    - Feature 2: description
    
    Dependencies: List key dependencies
    Exports: List key exports
*)
```

### Git Workflow

#### Commit Messages
```
type(scope): brief description

Longer description if needed

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>
```

#### Branching
- `main` - Stable releases only
- `develop` - Integration branch  
- `feature/name` - Feature development
- `bugfix/name` - Bug fixes

### Build System

#### _CoqProject Management
- Add new files in dependency order
- Test compilation after changes
- Update build documentation

#### Dependencies
- Minimize external dependencies
- Document required versions
- Test with clean opam environment

### Code Review Checklist

#### Functionality
- [ ] Code compiles without errors/warnings
- [ ] All tests pass
- [ ] Performance requirements met
- [ ] Zero axioms/admits maintained

#### Quality
- [ ] Code follows style guidelines
- [ ] Documentation is complete
- [ ] Error handling is appropriate
- [ ] Edge cases are covered

#### Integration
- [ ] Builds successfully with full project
- [ ] Does not break existing functionality
- [ ] Import statements are correct
- [ ] Dependencies are properly declared

### Debugging Tips

#### Common Issues
- **Import errors**: Check _CoqProject file order
- **Timeout errors**: Split complex proofs
- **Type errors**: Use `Check` to verify types
- **Tactic failures**: Use `Show Proof` to debug

#### Debug Tools
- `Print` - Show definitions
- `Check` - Verify types
- `Search` - Find related theorems
- `Locate` - Find definitions

### Release Process

1. **Verification Phase**
   - All tests pass
   - Zero axioms/admits
   - Performance benchmarks met

2. **Documentation Phase**  
   - Update API documentation
   - Update user guides
   - Update project status

3. **Integration Phase**
   - Test with full corpus
   - Verify SLA compliance
   - Update version numbers