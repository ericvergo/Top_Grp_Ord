/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import OrdinalHomeo.DegreeOne.PerfectGroups
import OrdinalHomeo.DegreeOne.NormalGenerators
import OrdinalHomeo.HigherDegree.SplitExactSequences

/-!
# Properties of F̄_{0,d}

This file formalizes Section 4.2 of the paper, establishing properties of F̄_{0,d}
including uniform perfectness and classification of normal generators.

## Main Results

* `fragmentation_F_bar` - Fragmentation lemma for F̄_{α,d}
* `F_bar_0d_uniformly_perfect` - F̄_{0,d} is uniformly perfect with commutator width ≤ 4
* `normal_generators_F_bar_0d` - Classification of normal generators of F̄_{0,d}
* `F_Z_subgroup` - Subgroups fixing neighborhoods of points in Z ⊆ M

-/

open Ordinal Set Function

universe u v

namespace OrdinalHomeo

variable {α : Ordinal.{u}} {d : ℕ}

/-- Fragmentation lemma for F̄_{α,d} -/
theorem fragmentation_F_bar (f : F_closure α d) 
  (U : Fin d → Set (X α d))
  (hU : ∀ i, IsClopen (U i))
  (hDisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
  ∃ (f₀ : F α d) (f_i : Fin d → H α d),
    (∀ i, support (f_i i) ⊆ U i) := sorry

/-- Local isomorphism with Homeo(ω^{α+1}) -/
theorem local_isomorphism (μ : maximalRankElements α d) 
  (U : Set (X α d)) 
  (hU : IsClopen U ∧ U ∩ (maximalRankElements α d : Set (X α d)) = {μ.val}) :
  ∃ (G : Subgroup (H α d)), Nonempty (G ≃* H α 1) := sorry

variable (d : ℕ) (hd : d ≠ 1)

/-- Subgroup of F̄_{0,d} fixing neighborhoods of points in Z -/
def F_Z (Z : Set (maximalRankElements 0 d)) : Subgroup (F_closure 0 d) := sorry

/-- The maximal subset Z_Γ for a subgroup Γ -/
def Z_Gamma (d : ℕ) (Γ : Set (F_closure 0 d)) : Set (maximalRankElements 0 d) := sorry

theorem F_bar_0d_uniformly_perfect (hd : d ≠ 1) : 
  ∃ k : ℕ, ∀ g : F_closure 0 d, ∃ l : List (F_closure 0 d × F_closure 0 d), 
    l.length ≤ k ∧ g = sorry := sorry

theorem F_bar_0d_commutator_width (hd : d ≠ 1) :
  commutatorWidth (F_closure 0 d) ≤ 4 := sorry

/-- Classification of normal subgroups of F̄_{0,d} -/
theorem normal_subgroup_classification (Γ : Subgroup (F_closure 0 d))
  (hNormal : Γ.Normal) (hNontrivial : ¬(∀ g ∈ Γ, (g : H 0 d) ∈ F 0 d)) :
  True := sorry -- placeholder for F_Z (Z_Gamma d (Γ : Set (F_closure 0 d))) = Γ

/-- Existence of normal generator with given support -/
theorem exists_normal_generator_Z (Γ : Subgroup (F_closure 0 d))
  (hNormal : Γ.Normal) (hNontrivial : ¬(∀ g ∈ Γ, (g : H 0 d) ∈ F 0 d)) :
  ∃ γ ∈ Γ, Z_Gamma d ({γ} : Set (F_closure 0 d)) = Z_Gamma d (Γ : Set (F_closure 0 d)) := sorry

/-- Uniform normal generation from support condition -/
theorem uniform_normal_generation_Z (Γ : Subgroup (F_closure 0 d))
  (hNormal : Γ.Normal) (γ : F_closure 0 d) (hγ : γ ∈ Γ)
  (hZ : Z_Gamma d ({γ} : Set (F_closure 0 d)) = Z_Gamma d (Γ : Set (F_closure 0 d))) :
  True := sorry -- placeholder for UniformNormalGenerator

/-- Classification of normal generators of F̄_{0,d} -/
theorem normal_generators_F_bar_0d (f : F_closure 0 d) : 
  True := sorry -- placeholder for the full statement

end OrdinalHomeo