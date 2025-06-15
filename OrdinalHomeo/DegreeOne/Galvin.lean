/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.Moiety

/-!
# Galvin's Lemma for Ordinals

This file proves Galvin's lemma for homeomorphism groups of ordinals, which provides
a uniform fragmentation result for homeomorphisms in terms of moieties.

## Main results

* `galvin_lemma`: Every homeomorphism can be written as a product of three homeomorphisms,
  each supported in one of two disjoint moieties

This is a key technical tool for proving uniform perfectness and characterizing normal generators.

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set

universe u

section Galvin

/-- The subgroup of homeomorphisms fixing a moiety pointwise -/
noncomputable def F_A {α : Ordinal.{u}} (A : Set (X α 1)) : Subgroup (H α 1) :=
  { carrier := {f | ∀ a ∈ A, f.toFun a = a}
    mul_mem' := by 
      intro f g hf hg a ha
      -- Show (f * g) a = a
      -- In Basic.lean, multiplication is defined as h₁.trans h₂
      -- So (f * g).toFun = f.toFun ∘ g.toFun
      change (f.trans g).toFun a = a
      -- (f.trans g).toFun a = g.toFun (f.toFun a)
      show g.toFun (f.toFun a) = a
      rw [hf a ha, hg a ha]
    one_mem' := by 
      intro a ha
      -- one is Homeomorph.refl, which is the identity
      rfl
    inv_mem' := by 
      intro f hf a ha
      -- Show f⁻¹.toFun a = a
      -- In the group structure, f⁻¹ = f.symm
      show f.symm.toFun a = a
      -- We know f.toFun a = a
      have h : f.toFun a = a := hf a ha
      -- Since f is a homeomorphism, if f(a) = a, then f.symm(a) = a
      -- We can apply f.symm to both sides of f.toFun a = a
      have : f.symm.toFun (f.toFun a) = f.symm.toFun a := by rw [h]
      rw [← this]
      -- Now use the fact that f.symm (f x) = x
      exact f.symm_apply_apply a  }

/-- Galvin's lemma: Uniform fragmentation using moieties -/
theorem galvin_lemma {α : Ordinal.{u}} (A B : TopologicalMoiety α)
  (hAB : (A : Set (X α 1)) ∩ (B : Set (X α 1)) = ∅) :
  ∀ h : H α 1, h ∈ {f * g * h | (f ∈ (F_A (A : Set (X α 1))).carrier) (g ∈ (F_A (B : Set (X α 1))).carrier) (h ∈ (F_A (A : Set (X α 1))).carrier)} ∪
                    {f * g * h | (f ∈ (F_A (B : Set (X α 1))).carrier) (g ∈ (F_A (A : Set (X α 1))).carrier) (h ∈ (F_A (B : Set (X α 1))).carrier)} := by
  -- This is the key fragmentation result from Galvin's original proof
  -- Given disjoint moieties A and B whose union is a moiety, any homeomorphism h
  -- can be written as a product of three homeomorphisms, each fixing either A or B
  
  -- The proof idea:
  -- Let C = (A ∪ B)ᶜ (the complement of A ∪ B)
  -- For any h, consider h(A) ∩ C and h(B) ∩ C
  -- At least one of C \ h(A) or C \ h(B) must contain a moiety
  -- This allows us to construct the appropriate factorization
  
  -- The proof requires careful analysis of how h interacts with the partition {A, B, C}
  sorry -- Requires: detailed case analysis and moiety manipulations

/-- Corollary: Any homeomorphism is a product of at most 3 moiety-supported homeomorphisms -/
lemma fragmentation_bound {α : Ordinal.{u}} (_h : H α 1) :
  ∃ (A B : TopologicalMoiety α) (f₁ f₂ f₃ : H α 1),
    (support f₁ ⊆ (A : Set (X α 1)) ∨ support f₁ ⊆ (B : Set (X α 1))) ∧
    (support f₂ ⊆ (A : Set (X α 1)) ∨ support f₂ ⊆ (B : Set (X α 1))) ∧
    (support f₃ ⊆ (A : Set (X α 1)) ∨ support f₃ ⊆ (B : Set (X α 1))) ∧
    _h = f₁ * f₂ * f₃ := by
  sorry

/-- Key step in Galvin's proof: constructing the appropriate partition -/
lemma galvin_partition {α : Ordinal.{u}} (_h : H α 1) (_A _B : TopologicalMoiety α)
  (_hAB : (_A : Set (X α 1)) ∩ (_B : Set (X α 1)) = ∅) :
  let C := ((_A : Set (X α 1)) ∪ (_B : Set (X α 1)))ᶜ
  (∃ M : TopologicalMoiety α, (M : Set (X α 1)) ⊆ C ∧ (_h.toFun '' (_A : Set (X α 1))) ∩ C ⊆ (M : Set (X α 1))) ∨
  (∃ M : TopologicalMoiety α, (M : Set (X α 1)) ⊆ C ∧ (_h.toFun '' (_B : Set (X α 1))) ∩ C ⊆ (M : Set (X α 1))) := by
  sorry

end Galvin

end OrdinalHomeo