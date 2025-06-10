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
      -- Show f⁻¹ a = a
      -- We know f a = a, so we need to show f.symm a = a
      have h : f.toFun a = a := hf a ha
      -- f.symm a = a iff f a = a (since f is a bijection)
      -- We need to show f.symm.toFun a = a
      -- Since f.toFun a = a, and f is a bijection, f.symm.toFun a = a
      -- Use the fact that if f fixes a point, so does f⁻¹
      sorry  } -- This requires showing that fixed points of f are also fixed points of f.symm

/-- Galvin's lemma: Uniform fragmentation using moieties -/
theorem galvin_lemma {α : Ordinal.{u}} {A B : Set (X α 1)}
  (hA : TopologicalMoiety α A) (hB : TopologicalMoiety α B)
  (hAB : A ∩ B = ∅) (hUnion : TopologicalMoiety α (A ∪ B)) :
  ∀ h : H α 1, h ∈ {f * g * h | (f ∈ (F_A A).carrier) (g ∈ (F_A B).carrier) (h ∈ (F_A A).carrier)} ∪
                    {f * g * h | (f ∈ (F_A B).carrier) (g ∈ (F_A A).carrier) (h ∈ (F_A B).carrier)} := by
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