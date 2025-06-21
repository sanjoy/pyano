# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Pyano is a formalization of first-order logic and Peano's axioms in Python. It provides:
1. Data structures to represent first-order logic formulae
2. An automated proof verifier using modus ponens
3. Helper classes to construct formal proofs

This is a toy project for educational purposes, not production software.

## Development Setup

Set up the development environment:
```bash
python3 -m venv venv
source venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
```

## Key Commands

**Run all tests:**
```bash
cd pyano && pytest
```

**Run specific test file:**
```bash
cd pyano && pytest formula_test.py -v
cd pyano && pytest theorems_test.py -v
```

**Generate all theorem proofs:**
```bash
cd pyano && python theorems.py
```

**Test a single theorem:**
```bash
cd pyano && python -c "
from theorems import *
from proof_builder import *
b = ProofBuilder()
prove_one_times_one_equals_one(b)  # or any other prove_* function
assert_proof_is_valid(b.proof)
print('Proof valid!')
"
```

**Format code:**
```bash
black pyano/
```

## Core Architecture

**Formula Representation (`formula.py`):**
- Base class `Formula` with subclasses for logical constructs
- Natural numbers: `Zero`, `Succ`, `Add`, `Mul`, `Var`
- Predicates: `Eq`, `And`, `Not`, `Implies`, `ForAll`
- Helper functions: `get_free_vars`, `substitute_forall`, `canonicalize_bound_vars`

**Axiom System (`axioms.py`):**
- ForAll instantiation and quantifier manipulation
- Sentential tautologies (propositional logic)
- Reflexivity: `forall x. x = x`
- Substitution: equality replacement
- Peano axioms for natural numbers
- Induction schema

**Proof Construction (`proof_builder.py`):**
- `ProofBuilder` class provides high-level proof construction
- Key methods:
  - `peano_axiom_*()` - access to Peano axioms
  - `immediately_implies()` - chain implications via modus ponens
  - `forall_split()` - instantiate universal quantifiers
  - `prove_values_transitively_equal()` - transitivity chains
- Each proof is a sequence of formulae verified by modus ponens

**Proof Verification (`proof_checker.py`):**
- `assert_proof_is_valid()` verifies entire proof sequences
- Each step must be either an axiom or follow from previous steps via modus ponens

**Theorem Library (`theorems.py`):**
- Functions starting with `prove_*` construct formal proofs
- Each function takes a `ProofBuilder` instance
- Proofs are exported to `proved_theorems/` directory
- Integration with verification system via `_iterate_proofs()`

## Writing New Theorems

1. Create a function `prove_theorem_name(b)` in `theorems.py`
2. Use `b.p()` to add formulae to the proof
3. Use axiom methods: `b.peano_axiom_x_plus_zero()`, `b.peano_axiom_x_times_succ_y()`, etc.
4. Chain reasoning with `b.immediately_implies(premise1, premise2, conclusion)`
5. The function is automatically discovered and tested by the system

Example pattern:
```python
def prove_my_theorem(b):
    """Proves some mathematical fact"""
    p = b.p
    v = get_cached_vars()
    
    # Get axioms and build reasoning chain
    axiom1 = b.peano_axiom_x_plus_zero()
    result = b.immediately_implies(axiom1, target_formula)
```

## Key Classes and Functions

**Variables (`formula_helpers.py`):**
- `get_cached_vars()` - provides standard variable instances (v.x, v.y, v.Z, v.i1, etc.)
- Use these for consistency across proofs

**Proof Patterns:**
- Universal quantifier instantiation via `immediately_implies()`
- Transitivity chains for equality reasoning
- Induction proofs using base case + inductive step
- Variable renaming and scope management

The codebase follows a functional style where formulae are immutable and proof construction builds sequences of valid logical steps.