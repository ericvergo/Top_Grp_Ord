/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.Moiety
import OrdinalHomeo.DegreeOne.Galvin

/-!
# Normal Generators of Homeomorphism Groups

This file classifies the normal generators of Homeo(ω^(α+1)), proving that they are
exactly the homeomorphisms inducing infinite permutations on maximal rank elements.

## Main definitions

* `NormalGenerator`: An element that normally generates the entire group
* `UniformNormalGenerator`: A normal generator with bounded width
* `Fin(ω^(α+1))`: The maximal proper normal subgroup

## Main results

* `anderson_method`: Elements displacing moieties generate moiety-supported elements
* `normal_generator_classification`: Classification of normal generators
* `maximal_normal_subgroup`: Fin(ω^(α+1)) is the maximal proper normal subgroup

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set

universe u

section NormalGenerators

/-- An element normally generates G if G is the smallest normal subgroup containing it -/
def NormalGenerator {G : Type*} [Group G] (g : G) : Prop :=
  Subgroup.normalClosure {g} = ⊤

/-- A uniform normal generator has bounded width -/
def UniformNormalGenerator {G : Type*} [Group G] (g : G) (k : ℕ) : Prop :=
  NormalGenerator g ∧ 
  ∀ h : G, ∃ (n : Fin k) (conj : Fin k → G) (sign : Fin k → Bool),
    h = sorry  -- Product of conjugates

/-- Anderson's method: Elements displacing moieties generate all moiety-supported elements -/
theorem anderson_method {α : Ordinal.{u}} {h : H α 1} (A : TopologicalMoiety α)
  (hDisjoint : h.toFun '' (A : Set (X α 1)) ∩ (A : Set (X α 1)) = ∅) :
  ∀ f : H α 1, ∀ B : TopologicalMoiety α, support f ⊆ (B : Set (X α 1)) →
    ∃ (conj : Fin 4 → H α 1) (sign : Fin 4 → Bool),
      f = sorry := by  -- Product of conjugates
  sorry

/-- Elements inducing infinite permutations displace some moiety -/
lemma infinite_permutation_displaces_moiety {α : Ordinal.{u}} {h : H α 1}
  (hInf : Set.Infinite {x ∈ maximalRankElements α 1 | h.toFun x ≠ x}) :
  ∃ A : TopologicalMoiety α, h.toFun '' (A : Set (X α 1)) ∩ (A : Set (X α 1)) = ∅ := by
  sorry

/-- Main theorem: Classification of normal generators -/
theorem normal_generator_classification {α : Ordinal.{u}} (h : H α 1) :
  (NormalGenerator h ↔ Set.Infinite {x ∈ maximalRankElements α 1 | h.toFun x ≠ x}) ∧
  (NormalGenerator h ↔ ∃ k, UniformNormalGenerator h k) := by
  sorry

/-- The h-width is at most 12 for any normal generator -/
theorem normal_generator_width_bound {α : Ordinal.{u}} {h : H α 1} 
  (hGen : NormalGenerator h) : UniformNormalGenerator h 12 := by
  sorry

/-- The subgroup of finite permutations -/
noncomputable def Fin_subgroup (α : Ordinal.{u}) : Subgroup (H α 1) :=
  { carrier := {f | Set.Finite {x ∈ maximalRankElements α 1 | f.toFun x ≠ x}}
    mul_mem' := by sorry
    one_mem' := by 
      simp only [Set.mem_setOf_eq]
      -- The identity doesn't move any points
      convert Set.finite_empty
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro ⟨hx_max, hx_moved⟩
      -- hx_max : x ∈ maximalRankElements α 1
      -- hx_moved : 1.toFun x ≠ x
      -- For the identity homeomorphism, 1.toFun x = x for all x
      exact hx_moved rfl
    inv_mem' := by 
      intro f hf
      simp only [Set.mem_setOf_eq] at hf ⊢
      -- The points moved by f⁻¹ are exactly those moved by f
      -- For a homeomorphism f, we have f(x) = x iff f⁻¹(x) = x
      -- This is a standard fact about bijections
      -- MISSING: Full proof requires showing that for homeomorphisms,
      -- the set of moved points is preserved under taking inverses
      sorry }

/-- Fin(ω^(α+1)) is the maximal proper normal subgroup -/
theorem maximal_normal_subgroup (α : Ordinal.{u}) :
  ∀ N : Subgroup (H α 1), N.Normal → N ≠ ⊤ → N ≤ Fin_subgroup α := by
  sorry

end NormalGenerators

end OrdinalHomeo