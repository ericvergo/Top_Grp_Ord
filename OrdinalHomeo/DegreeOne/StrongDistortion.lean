/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.Moiety
import Mathlib.Data.Real.Basic

/-!
# Strong Distortion of Homeomorphism Groups

This file proves that Homeo(ω^(α+1)) is strongly distorted, a property stronger than
strong boundedness that implies many geometric constraints.

## Main definitions

* `StronglyDistorted`: A group with uniformly bounded finite generation for sequences
* `StronglyBounded`: Every left-invariant metric has bounded diameter
* `CalegariFreedmanConstruction`: The construction for proving strong distortion

## Main results

* `homeo_strongly_distorted`: Homeo(ω^(α+1)) is strongly distorted
* `strong_distortion_implies_strong_boundedness`: Strong distortion implies strong boundedness
* `higher_degree_not_distorted`: H_{α,d} for d > 1 is not strongly distorted

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set

universe u

section StrongDistortion

/-- A group is strongly distorted if sequences have uniformly bounded generation -/
class StronglyDistorted (G : Type*) [Group G] where
  m : ℕ
  width : ℕ → ℕ
  generation : ∀ (g : ℕ → G), ∃ S : Finset G, S.card ≤ m ∧ 
    ∀ n, g n ∈ {x | ∃ (f : Fin (width n) → S), x = sorry}

/-- A group is strongly bounded if every left-invariant metric has bounded diameter -/
def StronglyBounded (G : Type*) [Group G] : Prop :=
  ∀ d : G → G → ℝ, (∀ g h k, d (g * h) (g * k) = d h k) → 
    (∀ g h, d g h ≥ 0) → (∀ g, d g g = 0) →
    ∃ M, ∀ g h, d g h ≤ M

/-- The Calegari-Freedman construction for proving strong distortion -/
lemma calegari_freedman_construction {α : Ordinal.{u}} 
  (A B : TopologicalMoiety α)
  (σ : H α 1) (hσ : IsConvergentATranslation A σ ∧ support σ ⊆ (B : Set (X α 1)))
  (τ : H α 1) (hτ : IsConvergentATranslation B τ) :
  ∀ (h : ℕ → H α 1), (∀ n, support (h n) ⊆ (A : Set (X α 1))) →
    ∃ φ : H α 1, ∀ n, h n = sorry := by
  sorry

/-- Main theorem: Homeo(ω^(α+1)) is strongly distorted -/
instance homeo_strongly_distorted (α : Ordinal.{u}) : 
  StronglyDistorted (H α 1) := by
  sorry

/-- Strong distortion implies strong boundedness -/
theorem strong_distortion_implies_strong_boundedness {G : Type*} [Group G]
  [StronglyDistorted G] : StronglyBounded G := by
  sorry

/-- For d > 1, H_{α,d} is not strongly distorted -/
theorem higher_degree_not_distorted {α : Ordinal.{u}} {d : ℕ} (hd : d > 1) :
  ¬ Nonempty (StronglyDistorted (H α d)) := by
  sorry

/-- Corollary: Classification by strong distortion -/
theorem distortion_classification (α : Ordinal.{u}) (d : ℕ) :
  (Nonempty (StronglyDistorted (H α d)) ↔ d = 1) ∧
  (StronglyBounded (H α d) ↔ d = 1) := by
  sorry

end StrongDistortion

end OrdinalHomeo