# Lean 4 Formalization Guide for "What's a Computer?"

## Overview

This document provides guidance for working on the Lean 4 formalization of the paper "What's a Computer? A Rigorous Theoretical Framework for Three-Dimensional Spatial Computation". This formalization is intended for submission to Mathlib, Lean's mathematical library.

**Current Status: NO SORRY MODE** - All `sorry` statements have been replaced with earnest proof attempts. The formalization now contains no placeholder proofs.

## Core Values and Principles

### 1. Mathematical Rigor
- **Never compromise mathematical correctness** for convenience
- Do not introduce new axioms unless absolutely necessary and mathematically justified
- **We are in NO SORRY MODE** - do not add new `sorry` statements
- Do not use `admit` or other ways to circumvent proofs
- Every proof should be complete and mathematically sound
- All existing proofs have been completed with earnest attempts

### 1.5. Proper Use of Mathlib Definitions
- **CRITICAL: Always use existing Mathlib definitions** for standard mathematical concepts
- Do not create custom simplified versions of concepts that already exist in Mathlib
- **Do not take the easy way out** when integration with Mathlib becomes complex
- If something seems difficult to integrate with Mathlib, that's often a sign you're on the right track
- The formalization should properly connect to the broader mathematical library ecosystem
- Taking shortcuts by defining custom versions undermines the value of the formalization

### 2. Mathlib Standards
- The code must meet Mathlib's high standards for mathematical formalization
- Expect scrutiny from professional mathematicians during review
- Follow Lean 4 and Mathlib conventions for naming, style, and structure
- Use existing Mathlib lemmas and theorems whenever possible

### 3. Honest Mathematical Work
- Do not attempt to "game" the proof system or "reward hack"
- If a proof is difficult, move on to another rather than forcing an incorrect solution
- Be transparent about what works and what doesn't
- The goal is mathematical truth, not just getting code to compile

### 4. Concrete Mathematical Bounds Over Practical Assumptions
- **Never rely on "practical" bounds or assumptions** - all bounds must be proven mathematically
- Do not use `sorry` with comments like "Accept practical bound" or similar justifications
- If bounds are needed (e.g., on functions like `bits_needed`), they must be proven from first principles
- Avoid appealing to "real-world" limitations or "practical considerations" as substitutes for mathematical proof
- Every bound must be derived through rigorous mathematical reasoning, not empirical observation
- When a bound seems "obvious" or "practical," that's a signal to prove it formally, not to assume it

### 5. Avoid Hardcoded Values and Magic Numbers
- **Never use magic numbers** in definitions or proofs - all constants should be parameters or mathematically derived
- Examples of hardcoding to avoid:
  - Fixed constants like `100`, `1000`, `20`, `10` without justification
  - Hardcoded array indices or coordinate offsets (e.g., `symbol_track_y := 4`)
  - Arbitrary polynomial bounds (e.g., `(n + 1000)^4`)
  - Fixed buffer sizes or limits (e.g., `min max_cells 100`)
- Instead, all values should be:
  - **Passed as parameters** to functions and theorems
  - **Defined as named constants** with clear mathematical justification
  - **Derived from the problem structure** (e.g., number of tracks needed for encoding)
- The goal is to produce **general, parameterized proofs** that work for any valid configuration
- If you need a specific value for a proof, make it a hypothesis (e.g., `h : track_count ≥ 5`)
- This ensures the formalization is:
  - Reusable for different problem instances
  - Clear about its assumptions
  - Free from arbitrary choices that might not generalize

### 6. Prefer Abstract Mathematical Proofs Over Computational Approaches
- **Avoid computational proofs** that rely on concrete calculations with specific values
- Examples of computational approaches to avoid:
  - Setting high `maxHeartbeats` limits to brute-force through calculations
  - Using `norm_num` or `omega` to solve specific numeric inequalities
  - Computing exact polynomial bounds like `4 * n^3 + 1000` when existence suffices
  - Relying on concrete arithmetic to verify properties
- Instead, prefer abstract approaches:
  - **Use existence proofs** when specific values aren't needed (e.g., "∃ c k, f n ≤ c * n^k")
  - **Prove properties abstractly** without computing exact values
  - **Focus on asymptotic behavior** rather than precise constants
  - **Use mathematical reasoning** about growth rates and bounds
- Benefits of abstract proofs:
  - More mathematically rigorous and general
  - Don't require high computational limits
  - Focus on essential mathematical properties
  - More likely to be accepted by Mathlib
- Example: Instead of proving "encoding size ≤ 4 * n^3 + 1000", prove "∃ polynomial p, encoding size ≤ p(n)"
- This approach aligns with standard mathematical practice and produces cleaner, more maintainable proofs

## Workflow and Approach


### Working with Compilation Errors
When encountering build errors:
1. **Read the error carefully** - Lean's error messages are highly informative
2. **Check type mismatches** - Often the issue is using the wrong type or missing type class instances
3. **Look up Mathlib APIs** - Use grep/search to find the correct theorem names and signatures
4. **Break down complex proofs** - Add intermediate lemmas when needed
5. **Use the simplifier wisely** - `simp` can help but sometimes obscures what's happening

### Proof Development Strategy
1. **Start with high-priority items** - Fix compilation errors before tackling complex proofs
2. **Use helper lemmas** - Break complex proofs into manageable pieces
3. **Leverage definitional equality** - Many things in the simplified implementation are true by definition
4. **Pattern match carefully** - Ensure all cases are covered when doing case analysis
5. **Check computability** - Some definitions may need to be `noncomputable`

### Common Patterns and Solutions

#### Type Class Resolution
- Missing `Inhabited`, `DecidableEq`, or `Fintype` instances are common
- Add necessary type class constraints to function signatures
- Use `inferInstance` when the instance should be automatic

#### Working with Recursive Definitions
- Definitions using `Nat.rec` create dependent types that need special handling
- Consider using simpler definitions for prototyping
- Prove properties about recursive functions by induction

#### Finite Type Cardinality
- Use `Fintype.card` for counting elements
- `Fintype.card_sum` for sum types
- `Fintype.ofEquiv` preserves cardinality
- Build injections to prove cardinality bounds

### 6. Task Management
Use a systematic approach to track progress:
1. Maintain a todo list of tasks
2. Prioritize compilation errors (high priority)
3. ~~Then tackle missing proofs (medium priority)~~ **COMPLETED - No more sorry statements**
4. Finally, optimize and clean up (low priority)
5. Mark tasks as completed as you go
6. Focus on maintaining the "no sorry" status while improving existing proofs

## Common Pitfalls to Avoid

1. **Don't reintroduce sorry statements** - We are in "no sorry" mode
2. **Don't assume theorem names** - Always verify the exact Mathlib API
3. **Don't ignore universe levels** - They matter for type correctness
4. **Don't skip error checking** - Build frequently to catch issues early
5. **Don't oversimplify** - Maintain mathematical accuracy even in "simplified" implementations
6. **Don't compromise existing proofs** - When refactoring, ensure all proofs remain valid

## Debugging Tips

1. **Use `#check` and `#print`** - Verify types and definitions
2. **Add explicit types** - When type inference fails
3. **Unfold definitions** - To see what you're actually proving
4. **Use `calc` for chains** - Makes inequality proofs clearer
5. **Try `exact?` or `library_search`** or grep /,lake - To find applicable theorems

## Mathlib Inquires

- use local grep searches in /.lake exclusively for all mathlib related inquires. Other forms of search are slow and often produce poor results. 