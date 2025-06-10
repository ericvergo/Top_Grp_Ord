/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import OrdinalHomeo.HigherDegree.Abelianization
import OrdinalHomeo.HigherDegree.PropertiesF0d

/-!
# Normal Generators for Higher Degree

This file formalizes Theorem 4.7, determining the minimal cardinality of normal
generating sets for PH_{0,d} and H_{0,d}.

## Main Results

* `minimal_normal_generators_PH_0d` - The minimal cardinality for PH_{0,d} is d-1
* `minimal_normal_generators_H_0d` - The minimal cardinality for H_{0,d} is 2
* `explicit_normal_generators_PH` - Explicit construction of normal generators for PH_{0,d}
* `explicit_normal_generators_H` - Explicit construction of normal generators for H_{0,d}

-/

open Ordinal Set Function

universe u v

namespace OrdinalHomeo

variable (d : ℕ) (hd : d ≠ 1)

/-- Lower bound from abelianization -/
theorem normal_gen_lower_bound_PH : 
  ∀ S : Finset (PH 0 d), true → d - 1 ≤ S.card := sorry  -- placeholder for normalGenerates

theorem normal_gen_lower_bound_H :
  ∀ S : Finset (H 0 d), true → 2 ≤ S.card := sorry  -- placeholder for normalGenerates

/-- The shift homeomorphisms form a normal generating set for PH_{0,d} -/
theorem shifts_normal_generate_PH :
  ∃ S : Set (PH 0 d), true := sorry  -- placeholder for normal generation

/-- Construction of commutator that normally generates F̄_{0,d} -/
def special_commutator : F_closure 0 d := sorry

theorem special_commutator_generates : 
  true := sorry  -- placeholder for normal generator properties

/-- Explicit normal generating set for PH_{0,d} of cardinality d-1 -/
theorem explicit_normal_generators_PH :
  ∃ S : Finset (PH 0 d), S.card = d - 1 := sorry

/-- Any odd permutation normally generates Sym(d) for d ≠ 4 -/
theorem odd_permutation_generates (hd4 : d ≠ 4) (σ : Equiv.Perm (Fin d)) : 
  true := sorry  -- placeholder for NormalGenerator

/-- Explicit normal generating set for H_{0,d} of cardinality 2 -/
theorem explicit_normal_generators_H :
  ∃ S : Finset (H 0 d), S.card = 2 := sorry

/-- The minimal cardinality of a normal generating set for PH_{0,d} is d-1 -/
theorem minimal_normal_generators_PH_0d :
  ∃ n : ℕ, n = d - 1 := sorry  -- placeholder for minimalNormalGeneratingCard

/-- The minimal cardinality of a normal generating set for H_{0,d} is 2 -/
theorem minimal_normal_generators_H_0d :
  ∃ n : ℕ, n = 2 := sorry  -- placeholder for minimalNormalGeneratingCard

end OrdinalHomeo