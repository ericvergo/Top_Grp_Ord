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

/-- The commutator trick: Building commutators from translations -/
lemma commutator_trick {α : Ordinal.{u}} {h : H α 1} (A : TopologicalMoiety α)
  (hSupp : support h ⊆ (A : Set (X α 1))) 
  (τ : H α 1) (hτ : IsConvergentATranslation A τ) :
  ∃ σ : H α 1, h = ⁅σ, τ⁆ := by
  -- The standard commutator trick: define σ = Σ_{n≥0} τⁿ h τ⁻ⁿ
  -- Since τ is a convergent A-translation and h is supported in A,
  -- the conjugates τⁿ h τ⁻ⁿ have disjoint supports and form a locally finite family
  
  -- We need to construct σ as an infinite product of conjugates
  -- For ordinals, we can work directly with the homeomorphism
  
  -- Define the sequence of conjugates
  let conjugates (n : ℕ) : H α 1 := τ^n * h * τ^(-n : ℤ)
  
  -- The key properties we need:
  -- 1. The supports of conjugates are disjoint
  -- 2. The family of supports is locally finite
  -- 3. This allows us to define the infinite product
  
  -- For now, we assume we can construct such an infinite product
  -- In the actual formalization, this would require:
  -- - Showing local finiteness of the conjugate supports
  -- - Using the compact-open topology to define the limit
  -- - Verifying that [σ, τ] = h
  
  sorry -- This requires formalizing infinite products in the homeomorphism group

/-- Elements supported in moieties can be written as single commutators -/
lemma moiety_supported_is_commutator {α : Ordinal.{u}} {h : H α 1} (A : TopologicalMoiety α)
  (hSupp : support h ⊆ (A : Set (X α 1))) :
  ∃ σ τ : H α 1, h = ⁅σ, τ⁆ := by
  -- Use the commutator trick with a convergent A-translation
  obtain ⟨τ, hτ_trans, ⟨B, hB_moiety⟩⟩ := exists_convergent_translation A
  -- τ is a convergent A-translation supported in moiety B
  -- Apply commutator_trick to get h = ⁅σ, τ⁆ for some σ
  sorry -- TODO: Complete using commutator_trick once it's proven

/-- Main theorem: Homeo(ω^(α+1)) is uniformly perfect with width ≤ 3 -/
theorem homeo_uniformly_perfect (α : Ordinal.{u}) : 
  ∃ (up : UniformlyPerfect (H α 1)), up.k ≤ 3 := by
  -- We'll show every element can be written as at most 3 commutators
  refine ⟨{
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
      rw [h_eq, h₁, h₂, h₃]
      -- Now we need to show ⁅σ₁, τ₁⁆ * ⁅σ₂, τ₂⁆ * ⁅σ₃, τ₃⁆ equals the product
      -- First, let's understand what List.ofFn produces for our function
      suffices h_list : (List.ofFn (fun i : Fin 3 => ⁅(match i with
        | ⟨0, _⟩ => (σ₁, τ₁)
        | ⟨1, _⟩ => (σ₂, τ₂)
        | ⟨2, _⟩ => (σ₃, τ₃)).1, (match i with
        | ⟨0, _⟩ => (σ₁, τ₁)
        | ⟨1, _⟩ => (σ₂, τ₂)
        | ⟨2, _⟩ => (σ₃, τ₃)).2⁆)).prod = ⁅σ₁, τ₁⁆ * ⁅σ₂, τ₂⁆ * ⁅σ₃, τ₃⁆ by
        exact h_list
      -- Simplify the List.ofFn expression
      -- For Fin 3, List.ofFn gives us [f 0, f 1, f 2]
      -- We need to show this equals ⁅σ₁, τ₁⁆ * ⁅σ₂, τ₂⁆ * ⁅σ₃, τ₃⁆
      -- The list is [⁅σ₁, τ₁⁆, ⁅σ₂, τ₂⁆, ⁅σ₃, τ₃⁆]
      -- and its product is ⁅σ₁, τ₁⁆ * ⁅σ₂, τ₂⁆ * ⁅σ₃, τ₃⁆
      simp only [List.ofFn]
      -- List.ofFn for Fin 3 creates [f ⟨0, _⟩, f ⟨1, _⟩, f ⟨2, _⟩]
      sorry  -- TODO: Show the list product equals the desired expression
  }, le_refl 3⟩

/-- Corollary: Every element can be written as at most 3 commutators -/
theorem three_commutator_bound {α : Ordinal.{u}} (h : H α 1) :
  ∃ (c₁ c₂ c₃ : (H α 1) × (H α 1)), 
    h = ⁅c₁.1, c₁.2⁆ * ⁅c₂.1, c₂.2⁆ * ⁅c₃.1, c₃.2⁆ := by
  -- This follows from homeo_uniformly_perfect
  obtain ⟨up, hup⟩ := homeo_uniformly_perfect α
  -- up.k ≤ 3, so h can be written as at most 3 commutators
  -- We have up.k = 3 and up.uniform_bound says any h can be written as product of up.k commutators
  obtain ⟨pairs, h_eq⟩ := up.uniform_bound h
  -- pairs : Fin up.k → (H α 1) × (H α 1)
  -- and h = (List.ofFn (fun i => ⁅(pairs i).1, (pairs i).2⁆)).prod
  -- Since up.k ≤ 3 and actually up.k = 3, we have Fin 3
  -- So we can extract the three pairs
  use pairs ⟨0, by norm_num⟩, pairs ⟨1, by norm_num⟩, pairs ⟨2, by norm_num⟩
  -- Now we need to show h equals the product of these three commutators
  sorry  -- This requires showing List.prod for a 3-element list

end PerfectGroups

end OrdinalHomeo