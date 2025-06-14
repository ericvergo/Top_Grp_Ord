# Ordinal Homeomorphism Groups

Lean 4 formalization of "Algebraic and geometric properties of homeomorphism groups of ordinals" by Bhat et al. You are responsible for the bulk of the proof writing in lean and are given agency within this repo, up to the rules below. The goal is for you to be able to work for long periods of time without my involvement. 

## Important: After Auto-Compacting

**Claude: After auto-compacting, please read these files in order to restore full context:**

1. `/Users/eric/Top_Grp_Ord/README.md` (this file - for project structure and guidelines)
2. `/Users/eric/Top_Grp_Ord/ordinals_part_1.txt` (original paper part 1)
3. `/Users/eric/Top_Grp_Ord/ordinals_part_2.txt` (original paper part 2)

---

## Project Structure

- `OrdinalHomeo/Basic.lean` - Core definitions (ordinals, homeomorphism groups, support)
- `OrdinalHomeo/CantorBendixson.lean` - Cantor-Bendixson rank and degree
- `OrdinalHomeo/Moiety.lean` - Topological moieties
- `OrdinalHomeo/DegreeOne/` - Results for Cantor-Bendixson degree one
  - `Galvin.lean` - Galvin's lemma
  - `NormalGenerators.lean` - Classification of normal generators
  - `PerfectGroups.lean` - Uniform perfectness
  - `StrongDistortion.lean` - Strong distortion property
- `OrdinalHomeo/HigherDegree/` - Results for degree > 1
  - `SplitExactSequences.lean` - Semidirect product decompositions
  - `FluxHomomorphisms.lean` - Construction of flux homomorphisms
  - `PropertiesF0d.lean` - Properties of F̄_{0,d}
  - `Abelianization.lean` - Abelianization computations
  - `NormalGenerators.lean` - Minimal normal generating sets

## Development Practices

### IMPORTANT: Always Use Grep First

**Always use grep searches for exploring code, finding patterns, and understanding the codebase.** This is much more efficient than reading entire files.

```bash
# Count sorries in the project
grep -r "sorry" . --include="*.lean" | wc -l

# Find specific sorries with context
grep -B2 -A2 "sorry" . --include="*.lean"

# Search for specific lemmas/definitions
grep -r "lemma.*moiety" . --include="*.lean"
```

### Mathlib Searches

Use local grep searches for efficient Mathlib exploration:
```bash
# Search for definitions/lemmas
grep -r "TotallyDisconnectedSpace" .lake/packages/mathlib --include="*.lean"

# Search with context
grep -B2 -A2 "pattern" .lake/packages/mathlib --include="*.lean"
```

### Proof Progress Tracking

When attempting to clear a `sorry`, document failed approaches as comments:
```lean
lemma example_lemma : P := by
  -- ATTEMPT 1: Direct proof via X failed - issue with Y
  -- ATTEMPT 2: Induction approach failed - missing lemma Z
  sorry
```

This helps avoid repeated failed attempts and guides future proof strategies.

## Behavior to Avoid
- Introducing new axioms
- Spending too much time on a single issue and spinning your wheels
- Taking actions that would require approval from the user
- Exploiting bugs and/or manipulating lean to obtain a proof certificate when you have not actually written a proof (rare)


## Behavior to Adopt
- Leveraging existing mathlib libraries
- Clearly documenting code
- all ethical standards surrounding and defining the culture of research mathematics
