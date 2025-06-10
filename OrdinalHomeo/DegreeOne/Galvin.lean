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
theorem galvin_lemma {α : Ordinal.{u}} {A B : Set (X α 1)}
  (hA : TopologicalMoiety α A) (hB : TopologicalMoiety α B)
  (hAB : A ∩ B = ∅) (hUnion : TopologicalMoiety α (A ∪ B)) :
  ∀ h : H α 1, h ∈ {f * g * h | (f ∈ (F_A A).carrier) (g ∈ (F_A B).carrier) (h ∈ (F_A A).carrier)} ∪
                    {f * g * h | (f ∈ (F_A B).carrier) (g ∈ (F_A A).carrier) (h ∈ (F_A B).carrier)} := by
  intro h
  -- Let C be the complement of A ∪ B
  let C := (A ∪ B)ᶜ
  -- The key insight: at least one of C \ h(A) or C \ h(B) is a moiety
  -- This is because C = (C \ h(A)) ∪ (C \ h(B)) ∪ (C ∩ h(A ∪ B))
  -- and C is a moiety (complement of a moiety)
  
  -- Case 1: C \ h(A) is a moiety
  -- In this case, we can find homeomorphisms as required
  by_cases h_case : TopologicalMoiety α (C \ h.toFun '' A)
  · -- Case 1: C \ h(A) is a moiety
    -- We need to construct f₁ ∈ F_A, g ∈ F_B, f₂ ∈ F_A such that h = f₁ * g * f₂
    
    -- Step 1: Partition C into two moieties M₁ and M₂
    -- such that h(A) ∩ C ⊆ M₁
    -- This uses the fact that C \ h(A) is a moiety and h(A) ∩ C has specific properties
    
    -- Step 2: Choose f₁ ∈ F_A such that f₁(B ∪ M₁) = C and f₁(M₂) = B
    -- This is possible by change of coordinates lemma for moieties
    
    -- Step 3: Show that (f₁ ∘ h)(A) is contained in A ∪ C and disjoint from 
    -- a moiety in C, allowing us to find f₂ ∈ F_B with f₂(f₁(h(A))) = A
    
    -- Step 4: Express h in the required form
    
    -- For now, we use sorry as this requires the change of coordinates lemma
    -- and other results about moieties that aren't yet proven
    sorry
  · -- Case 2: C \ h(A) is not a moiety, so C \ h(B) must be a moiety
    -- Similar argument with roles of A and B switched
    sorry

/-- Corollary: Any homeomorphism is a product of at most 3 moiety-supported homeomorphisms -/
lemma fragmentation_bound {α : Ordinal.{u}} (h : H α 1) :
  ∃ (A B : Set (X α 1)) (hA : TopologicalMoiety α A) (hB : TopologicalMoiety α B)
    (f₁ f₂ f₃ : H α 1),
    (support f₁ ⊆ A ∨ support f₁ ⊆ B) ∧
    (support f₂ ⊆ A ∨ support f₂ ⊆ B) ∧
    (support f₃ ⊆ A ∨ support f₃ ⊆ B) ∧
    h = f₁ * f₂ * f₃ := by
  sorry

/-- Key step in Galvin's proof: constructing the appropriate partition -/
lemma galvin_partition {α : Ordinal.{u}} (h : H α 1) {A B C : Set (X α 1)}
  (hC : C = (A ∪ B)ᶜ) (hAB : A ∩ B = ∅) :
  (∃ M : Set (X α 1), TopologicalMoiety α M ∧ M ⊆ C ∧ (h.toFun '' A) ∩ C ⊆ M) ∨
  (∃ M : Set (X α 1), TopologicalMoiety α M ∧ M ⊆ C ∧ (h.toFun '' B) ∩ C ⊆ M) := by
  sorry

end Galvin

end OrdinalHomeo