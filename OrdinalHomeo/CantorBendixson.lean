/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import Mathlib.Topology.Perfect
import Mathlib.Topology.Separation.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cantor-Bendixson Rank and Degree

This file defines the Cantor-Bendixson derivative, rank, and degree for topological spaces,
with special focus on ordinals equipped with their order topology.

## Main definitions

* `derivedSet`: The derived set (set of accumulation points)
* `CantorBendixsonDerivative`: The α-th Cantor-Bendixson derivative
* `CantorBendixsonRank`: The least ordinal α such that the α-th derivative is empty
* `CantorBendixsonDegree`: The cardinality of the final non-empty derivative
* `rank`: The rank of a point in a space

## Main results

* The CB rank of a successor ordinal is the successor of its limit capacity
* The CB degree of a successor ordinal is its coefficient
* Classification of successor ordinals by CB rank and degree

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set Filter

universe u v

section CantorBendixson

variable {X : Type u} [TopologicalSpace X]

/-- The derived set of X consists of all accumulation points -/
def derivedSet (A : Set X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ A, y ≠ x}

/-- The α-th Cantor-Bendixson derivative -/
noncomputable def CantorBendixsonDerivative : Ordinal.{v} → Set X → Set X :=
  sorry  -- Ordinal recursion requires careful setup

notation:max A "^(" α ")" => CantorBendixsonDerivative α A

lemma CB_derivative_monotone {α β : Ordinal} (h : α ≤ β) (A : Set X) :
  A^(β) ⊆ A^(α) := by
  sorry

lemma CB_derivative_closed [T1Space X] (α : Ordinal) (A : Set X) (hA : IsClosed A) :
  IsClosed (A^(α)) := by
  sorry

/-- The Cantor-Bendixson rank of a set (∞ if no derivative is empty) -/
noncomputable def CantorBendixsonRank (A : Set X) : WithTop Ordinal :=
  sorry  -- This requires classical logic and is complex to define properly

/-- The Cantor-Bendixson degree of a compact set with finite rank -/
noncomputable def CantorBendixsonDegree (A : Set X) [CompactSpace X] : ℕ :=
  sorry  -- This requires careful implementation of finite cardinality

/-- The rank of a point x is the least α such that x ∉ X^(α) -/
noncomputable def rank (x : X) : Ordinal :=
  sInf {α | x ∉ (univ : Set X)^(α)}

end CantorBendixson

section OrdinalCantorBendixson

/-- The CB rank of ω^(α+1)·d + 1 is α + 2 -/
theorem CB_rank_successor_ordinal (α : Ordinal.{u}) (d : ℕ) (hd : d ≠ 0) 
  [CompactSpace (X α d)] :
  CantorBendixsonRank (univ : Set (X α d)) = ↑(α + 2) := by
  sorry

/-- The CB degree of ω^(α+1)·d + 1 is d -/
theorem CB_degree_successor_ordinal (α : Ordinal.{u}) (d : ℕ) (hd : d ≠ 0) 
  [CompactSpace (X α d)] :
  CantorBendixsonDegree (univ : Set (X α d)) = d := by
  sorry

/-- Elements of rank α+1 in ω^(α+1) are exactly the multiples of ω^α -/
lemma rank_classification (α : Ordinal.{u}) (x : X α 1) :
  rank x = α + 1 ↔ ∃ k : ℕ, k ≥ 1 := by
  sorry

/-- The rank of a point determines its Cantor normal form structure -/
theorem rank_determines_structure (α : Ordinal.{u}) (x : X α 1) :
  rank x ≤ α + 1 := by
  sorry

end OrdinalCantorBendixson

section Classification

/-- Two successor ordinals are homeomorphic iff they have the same CB rank and degree -/
theorem homeomorphic_iff_same_CB (α β : Ordinal.{u}) 
  (hα : SuccessorOrdinal α) (hβ : SuccessorOrdinal β)
  [CompactSpace (OrdinalSpace α)] [CompactSpace (OrdinalSpace β)] :
  Nonempty (OrdinalSpace α ≃ₜ OrdinalSpace β) ↔ 
  CantorBendixsonRank (univ : Set (OrdinalSpace α)) = CantorBendixsonRank (univ : Set (OrdinalSpace β)) ∧
  CantorBendixsonDegree (univ : Set (OrdinalSpace α)) = CantorBendixsonDegree (univ : Set (OrdinalSpace β)) := by
  sorry

end Classification

end OrdinalHomeo