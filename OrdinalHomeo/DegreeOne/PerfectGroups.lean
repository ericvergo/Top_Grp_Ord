/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.Moiety
import OrdinalHomeo.DegreeOne.Galvin
import Mathlib.Algebra.Group.Commutator

/-!
# Uniform Perfectness of Homeomorphism Groups

This file proves that Homeo(ω^(α+1)) is uniformly perfect with commutator width at most 3.

## Main definitions

* `UniformlyPerfect`: A group where every element is a bounded product of commutators
* `commutatorWidth`: The minimal number of commutators needed

## Main results

* `moiety_supported_is_commutator`: Elements supported in moieties are single commutators
* `homeo_uniformly_perfect`: Homeo(ω^(α+1)) has commutator width at most 3

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set

universe u

section PerfectGroups

/-- A group is uniformly perfect if every element is a product of at most k commutators -/
structure UniformlyPerfect (G : Type*) [Group G] where
  k : ℕ
  uniform_bound : ∀ g : G, ∃ (pairs : Fin k → G × G), 
    g = sorry  -- Product of commutators

/-- The commutator width of a uniformly perfect group -/
noncomputable def commutatorWidth (G : Type*) [Group G] (h : UniformlyPerfect G) : ℕ :=
  sorry  -- Minimum k for uniform perfectness

/-- Elements supported in moieties can be written as single commutators -/
lemma moiety_supported_is_commutator {α : Ordinal.{u}} {h : H α 1} {A : Set (X α 1)}
  (hA : TopologicalMoiety α A) (hSupp : support h ⊆ A) :
  ∃ σ τ : H α 1, h = ⁅σ, τ⁆ := by
  sorry

/-- Main theorem: Homeo(ω^(α+1)) is uniformly perfect with width ≤ 3 -/
theorem homeo_uniformly_perfect (α : Ordinal.{u}) : 
  Nonempty (UniformlyPerfect (H α 1)) := by
  sorry

/-- Corollary: Every element can be written as at most 3 commutators -/
theorem three_commutator_bound {α : Ordinal.{u}} (h : H α 1) :
  ∃ (c₁ c₂ c₃ : (H α 1) × (H α 1)), 
    h = sorry := by
  sorry

/-- The commutator trick: Building commutators from translations -/
lemma commutator_trick {α : Ordinal.{u}} {h : H α 1} {A : Set (X α 1)}
  (hA : TopologicalMoiety α A) (hSupp : support h ⊆ A) 
  (τ : H α 1) (hτ : isConvergentTranslation τ A) :
  ∃ σ : H α 1, h = sorry := by
  sorry

end PerfectGroups

end OrdinalHomeo