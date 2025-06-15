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
    g = (List.ofFn (fun i : Fin k => ⁅(pairs i).1, (pairs i).2⁆)).prod  -- Product of commutators

/-- The commutator width of a uniformly perfect group -/
noncomputable def commutatorWidth (G : Type*) [Group G] : ℕ :=
  sInf {k : ℕ | ∃ (up : UniformlyPerfect G), up.k = k}  -- Minimum k for uniform perfectness

/-- Elements supported in moieties can be written as single commutators -/
lemma moiety_supported_is_commutator {α : Ordinal.{u}} {h : H α 1} (A : TopologicalMoiety α)
  (hSupp : support h ⊆ (A : Set (X α 1))) :
  ∃ σ τ : H α 1, h = ⁅σ, τ⁆ := by
  -- Use the commutator trick with a convergent A-translation
  obtain ⟨τ, hτ_trans, ⟨B, hB_moiety⟩⟩ := exists_convergent_translation A
  -- τ is a convergent A-translation supported in moiety B
  -- Apply commutator_trick to get h = ⁅σ, τ⁆ for some σ
  obtain ⟨σ, hσ⟩ := commutator_trick A hSupp τ hτ_trans
  use σ, τ
  exact hσ

/-- Main theorem: Homeo(ω^(α+1)) is uniformly perfect with width ≤ 3 -/
theorem homeo_uniformly_perfect (α : Ordinal.{u}) : 
  ∃ (up : UniformlyPerfect (H α 1)), up.k ≤ 3 := by
  -- We'll show every element can be written as at most 3 commutators
  use {
    k := 3
    uniform_bound := fun h => by
      -- Apply Galvin's lemma to fragment h into at most 3 pieces
      obtain ⟨A, B, f₁, f₂, f₃, hSupp₁, hSupp₂, hSupp₃, h_eq⟩ := fragmentation_bound h
      -- Each f_i is supported in either A or B (both moieties)
      -- By moiety_supported_is_commutator, each f_i is a commutator
      have hComm₁ : ∃ σ τ : H α 1, f₁ = ⁅σ, τ⁆ := by
        cases hSupp₁ with
        | inl h => exact moiety_supported_is_commutator A h
        | inr h => exact moiety_supported_is_commutator B h
      have hComm₂ : ∃ σ τ : H α 1, f₂ = ⁅σ, τ⁆ := by
        cases hSupp₂ with
        | inl h => exact moiety_supported_is_commutator A h
        | inr h => exact moiety_supported_is_commutator B h
      have hComm₃ : ∃ σ τ : H α 1, f₃ = ⁅σ, τ⁆ := by
        cases hSupp₃ with
        | inl h => exact moiety_supported_is_commutator A h
        | inr h => exact moiety_supported_is_commutator B h
      -- Now construct the Fin 3 → G × G function
      obtain ⟨σ₁, τ₁, h₁⟩ := hComm₁
      obtain ⟨σ₂, τ₂, h₂⟩ := hComm₂
      obtain ⟨σ₃, τ₃, h₃⟩ := hComm₃
      use fun i => match i with
        | ⟨0, _⟩ => (σ₁, τ₁)
        | ⟨1, _⟩ => (σ₂, τ₂)
        | ⟨2, _⟩ => (σ₃, τ₃)
      -- Show h equals the product of these commutators
      simp only [List.ofFn]
      rw [h_eq, ← h₁, ← h₂, ← h₃]
      -- The product of 3 commutators
      simp [List.prod_cons, List.prod_nil]
      rfl
  }
  -- Show that 3 ≤ 3
  rfl

/-- Corollary: Every element can be written as at most 3 commutators -/
theorem three_commutator_bound {α : Ordinal.{u}} (h : H α 1) :
  ∃ (c₁ c₂ c₃ : (H α 1) × (H α 1)), 
    h = ⁅c₁.1, c₁.2⁆ * ⁅c₂.1, c₂.2⁆ * ⁅c₃.1, c₃.2⁆ := by
  sorry

/-- The commutator trick: Building commutators from translations -/
lemma commutator_trick {α : Ordinal.{u}} {h : H α 1} (A : TopologicalMoiety α)
  (hSupp : support h ⊆ (A : Set (X α 1))) 
  (τ : H α 1) (hτ : IsConvergentATranslation A τ.toHomeomorph) :
  ∃ σ : H α 1, h = ⁅σ, τ⁆ := by
  -- The standard commutator trick: define σ = Σ_{n≥0} τⁿ h τ⁻ⁿ
  -- Since τ is a convergent A-translation and h is supported in A,
  -- the conjugates τⁿ h τ⁻ⁿ have disjoint supports and form a locally finite family
  
  -- First, we need to show that the infinite product converges
  -- This uses that τ is a convergent translation, so the supports form a locally finite family
  
  -- For now, we construct σ directly but need to verify convergence
  sorry -- Need to formalize infinite products and local finiteness

end PerfectGroups

end OrdinalHomeo