/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import Mathlib.Topology.Perfect
import Mathlib.Topology.Separation.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.ClusterPt

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

open Ordinal Topology Set Filter Classical

universe u v

section CantorBendixson

variable {X : Type u} [TopologicalSpace X]

/-- The derived set of X consists of all accumulation points -/
def derivedSet (A : Set X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ A, y ≠ x}

@[simp]
lemma mem_derivedSet {A : Set X} {x : X} : x ∈ derivedSet A ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ A, y ≠ x := 
  Iff.rfl

-- Note: This is equivalent to Mathlib's definition using AccPt
lemma derivedSet_eq_mathlib (A : Set X) : derivedSet A = {x | AccPt x (𝓟 A)} := by
  ext x
  simp only [mem_derivedSet, Set.mem_setOf_eq]
  exact @accPt_iff_nhds X _ x A

/-- The derived set operator is monotone with respect to set inclusion -/
lemma derivedSet_mono {A B : Set X} (h : A ⊆ B) : derivedSet A ⊆ derivedSet B := by
  intro x hx
  simp only [derivedSet, Set.mem_setOf_eq] at hx ⊢
  intro U hU
  obtain ⟨y, hy_mem, hy_ne⟩ := hx U hU
  use y
  exact ⟨⟨hy_mem.1, h hy_mem.2⟩, hy_ne⟩

/-- The derived set of a closed set is closed in a T1 space -/
lemma derivedSet_closed [T1Space X] {A : Set X} (hA : IsClosed A) : IsClosed (derivedSet A) := by
  -- Use Mathlib's result
  rw [derivedSet_eq_mathlib]
  exact isClosed_derivedSet A

/-- The α-th Cantor-Bendixson derivative -/
noncomputable def CantorBendixsonDerivative {X : Type u} [TopologicalSpace X] (A : Set X) : Ordinal.{v} → Set X := fun α =>
  if α = 0 then A
  else if h : ∃ β, α = Order.succ β then
    have : α = Order.succ (Classical.choose h) := Classical.choose_spec h
    derivedSet (CantorBendixsonDerivative A (Classical.choose h))
  else
    -- α is a limit ordinal
    ⋂ β < α, CantorBendixsonDerivative A β
termination_by α => α
decreasing_by 
  -- We have two goals, one for each recursive call
  · simp_wf
    have heq : _ = Order.succ (Classical.choose h) := Classical.choose_spec h
    calc Classical.choose h < Order.succ (Classical.choose h) := Order.lt_succ _
         _ = _ := heq.symm
  · simp_wf
    assumption

notation:max A "^(" α ")" => CantorBendixsonDerivative A α

/-- The derived set of the empty set is empty -/
lemma derivedSet_empty : derivedSet (∅ : Set X) = ∅ := by
  ext x
  simp only [derivedSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  -- h says: ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ ∅, y ≠ x
  -- But U ∩ ∅ = ∅, so this is impossible
  have : (Set.univ : Set X) ∈ 𝓝 x := univ_mem
  obtain ⟨y, hy, _⟩ := h Set.univ this
  -- y ∈ univ ∩ ∅ means y ∈ ∅
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and] at hy
  exact hy

/-- A point not in A cannot be in the derived set of A if it has an open neighborhood disjoint from A -/
lemma not_mem_derivedSet_of_disjoint_neighborhood {A : Set X} {x : X} 
  (hx : x ∉ A) (U : Set X) (hU : U ∈ 𝓝 x) (hDisj : U ∩ A = ∅) : 
  x ∉ derivedSet A := by
  intro h
  -- h says: ∀ V ∈ 𝓝 x, ∃ y ∈ V ∩ A, y ≠ x
  -- Apply this to U
  obtain ⟨y, hy, hy_ne⟩ := h U hU
  -- But y ∈ U ∩ A contradicts U ∩ A = ∅
  rw [hDisj, Set.mem_empty_iff_false] at hy
  exact hy

lemma CB_derivative_closed [T1Space X] (α : Ordinal) (A : Set X) (hA : IsClosed A) :
  IsClosed (A^(α)) := by
  -- We prove by transfinite induction on α
  induction α using Ordinal.induction with
  | h β ih =>
    -- Consider the different cases for β
    by_cases h0 : β = 0
    · -- Base case: CB^0(A) = A
      rw [h0]
      unfold CantorBendixsonDerivative
      simp only [eq_self_iff_true, if_true]
      exact hA
    · by_cases hsucc : ∃ γ, β = Order.succ γ
      · -- Successor case: CB^(succ γ)(A) = derivedSet(CB^γ(A))
        obtain ⟨γ, rfl⟩ := hsucc
        -- By IH, A^(γ) is closed
        have h_closed : IsClosed (A^(γ)) := ih γ (Order.lt_succ γ)
        -- The derived set of a closed set is closed in T1 spaces
        -- We need to show that A^(Order.succ γ) is closed
        -- A^(Order.succ γ) = derivedSet (A^(γ)) by definition
        -- For successor ordinals, A^(Order.succ γ) = derivedSet (A^(γ))
        -- Since A^(γ) is closed by IH, derivedSet (A^(γ)) is closed
        exact derivedSet_closed h_closed
      · -- Limit case: CB^β(A) = ⋂_{γ<β} CB^γ(A)
        push_neg at hsucc
        -- Intersection of closed sets is closed
        -- We need to show that A^(β) is closed
        -- A^(β) = ⋂_{γ<β} A^(γ) by definition (since β is limit)
        -- For limit ordinals, A^(β) = ⋂ γ < β, A^(γ)
        -- Each A^(γ) is closed by IH, so their intersection is closed
        apply isClosed_biInter
        intro γ hγ
        exact ih γ hγ

lemma CB_derivative_monotone [T1Space X] {α β : Ordinal} (h : α ≤ β) (A : Set X) (hA : IsClosed A) :
  A^(β) ⊆ A^(α) := by
  -- We prove by transfinite induction on β
  induction β using Ordinal.induction with
  | h γ ih =>
    -- Case split on whether α = γ
    by_cases hαγ : α = γ
    · -- If α = γ, then A^(γ) ⊆ A^(α) is reflexive
      rw [hαγ]
    · -- If α < γ, we need to use the structure of γ
      have hlt : α < γ := lt_of_le_of_ne h hαγ
      -- Case split on whether γ is successor or limit
      by_cases hsucc : ∃ δ, γ = Order.succ δ
      · -- Successor case
        obtain ⟨δ, rfl⟩ := hsucc
        have hδ : α ≤ δ := Order.le_of_lt_succ hlt
        -- We need to show A^(Order.succ δ) ⊆ A^(α)
        -- By definition, A^(Order.succ δ) = derivedSet (A^(δ))
        -- Case split on whether α = δ or α < δ
        by_cases hαδ : α = δ
        · -- Case α = δ: need to show derivedSet (A^(δ)) ⊆ A^(δ)
          rw [hαδ]
          -- By definition of Cantor-Bendixson derivative, derivedSet only removes points
          -- This is a standard fact about derived sets
          -- First, rewrite using our derivedSet definition
          rw [derivedSet_eq_mathlib]
          -- Apply Mathlib's result about closed sets
          have hclosed : IsClosed (A^(δ)) := CB_derivative_closed δ A hA
          rw [derivedSet_eq_mathlib] at *
          exact (isClosed_iff_derivedSet_subset _).mp hclosed
        · -- Case α < δ: use IH
          have hα_lt_δ : α < δ := lt_of_le_of_ne hδ hαδ
          have h_sub : A^(δ) ⊆ A^(α) := ih δ (Order.lt_succ δ) (le_of_lt hα_lt_δ) hA
          -- Need to show A^(Order.succ δ) ⊆ A^(α), i.e., derivedSet (A^(δ)) ⊆ A^(α)
          -- We have A^(δ) ⊆ A^(α), so derivedSet (A^(δ)) ⊆ derivedSet (A^(α))
          -- Since derivedSet is monotone
          trans derivedSet (A^(α))
          · exact derivedSet_mono h_sub
          · -- Need: derivedSet (A^(α)) ⊆ A^(α)
            have hclosed_α : IsClosed (A^(α)) := CB_derivative_closed α A hA
            rw [derivedSet_eq_mathlib]
            exact (isClosed_iff_derivedSet_subset _).mp hclosed_α
      · -- Limit case
        -- CB^γ(A) = ⋂_{δ<γ} CB^δ(A)
        -- Since α < γ, CB^γ(A) ⊆ CB^α(A)
        push_neg at hsucc
        -- We need to show A^(γ) ⊆ A^(α)
        -- By definition, A^(γ) = ⋂ δ < γ, A^(δ) (since γ is a limit ordinal)
        -- Since α < γ, we have α ∈ {δ | δ < γ}
        -- So ⋂ δ < γ, A^(δ) ⊆ A^(α)
        -- For limit ordinals, A^(γ) = ⋂ β < γ, A^(β) by definition
        -- Since α < γ, the intersection is over a set containing α
        apply Set.biInter_subset_of_mem
        exact hlt

/-- The Cantor-Bendixson rank of a set (∞ if no derivative is empty) -/
noncomputable def CantorBendixsonRank (A : Set X) : WithTop Ordinal :=
  if h : ∃ α : Ordinal, CantorBendixsonDerivative A α = ∅ then
    ↑(Ordinal.sInf {α : Ordinal | CantorBendixsonDerivative A α = ∅})
  else 
    ⊤

/-- The Cantor-Bendixson degree of a compact set with finite rank -/
noncomputable def CantorBendixsonDegree (A : Set X) [CompactSpace X] 
  (h : CantorBendixsonRank A < ⊤) : ℕ :=
  -- The degree is the cardinality of A^(α-1) where α is the rank
  -- Since the rank is finite (not ∞), we can extract it
  let α := (CantorBendixsonRank A).toOrdinal
  -- For successor ordinals, the degree is the finite cardinality of the last non-empty derivative
  if hα : α = 0 then 0
  else
    -- The previous derivative A^(α-1) is finite and non-empty
    -- Its cardinality is the Cantor-Bendixson degree
    0 -- Placeholder: need to prove finiteness and extract cardinality

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
  -- The space X α 1 = ω^(α+1) + 1 has Cantor-Bendixson rank α + 2
  -- So every point has rank at most α + 1
  -- This follows from the fact that (univ)^(α+2) = ∅
  
  -- We need to show x ∈ (univ)^(α+1), which means rank x ≤ α + 1
  -- Since X α 1 = ω^(α+1) + 1, and this space has CB rank α + 2,
  -- all points disappear by the (α+2)-th derivative
  sorry -- Requires showing that ordinals have the expected CB rank

end OrdinalCantorBendixson

section Classification

/-- Two successor ordinals are homeomorphic iff they have the same CB rank and degree -/
theorem homeomorphic_iff_same_CB (α β : Ordinal.{u}) 
  (hα : SuccessorOrdinal α) (hβ : SuccessorOrdinal β)
  [CompactSpace (OrdinalSpace α)] [CompactSpace (OrdinalSpace β)] :
  Nonempty (OrdinalSpace α ≃ₜ OrdinalSpace β) ↔ 
  CantorBendixsonRank (univ : Set (OrdinalSpace α)) = CantorBendixsonRank (univ : Set (OrdinalSpace β)) ∧
  (∀ (hα_fin : CantorBendixsonRank (univ : Set (OrdinalSpace α)) < ⊤)
     (hβ_fin : CantorBendixsonRank (univ : Set (OrdinalSpace β)) < ⊤),
     CantorBendixsonDegree (univ : Set (OrdinalSpace α)) hα_fin = 
     CantorBendixsonDegree (univ : Set (OrdinalSpace β)) hβ_fin) := by
  sorry

end Classification

end OrdinalHomeo