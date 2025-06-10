# Ordinal Homeomorphism Groups

Lean 4 formalization of "Algebraic and geometric properties of homeomorphism groups of ordinals" by Bhat et al.

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

## Build Status

The project builds successfully with `lake build`. All theorem statements are in place with `sorry` placeholders.

## Development Practices

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

## Completed Proofs

- ✓ `F_A.inv_mem'` - Fixed points preserved by inverse (Galvin.lean)
- ✓ `Fin_subgroup.one_mem'` - Identity has finite support (NormalGenerators.lean)
- ✓ `derivedSet_empty` - The derived set of the empty set is empty (CantorBendixson.lean)
- ✓ `not_mem_derivedSet_of_disjoint_neighborhood` - Points with disjoint neighborhoods are not in derived set (CantorBendixson.lean)

## References

- Original paper: [arXiv link to be added]
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/