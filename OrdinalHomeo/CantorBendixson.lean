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
  exact (@accPt_iff_nhds X _ x A).symm

/-- The derived set operator is monotone with respect to set inclusion -/
lemma derivedSet_mono {A B : Set X} (h : A ⊆ B) : derivedSet A ⊆ derivedSet B := by
  intro x hx
  simp only [derivedSet, Set.mem_setOf_eq] at hx ⊢
  intro U hU
  obtain ⟨y, hy_mem, hy_ne⟩ := hx U hU
  use y
  exact ⟨⟨hy_mem.1, h hy_mem.2⟩, hy_ne⟩

/-- The derived set of a closed set is closed in a T1 space -/
lemma derivedSet_closed [T1Space X] {A : Set X} : IsClosed (derivedSet A) := by
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
  (U : Set X) (hU : U ∈ 𝓝 x) (hDisj : U ∩ A = ∅) : 
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
        unfold CantorBendixsonDerivative
        rw [if_neg (Ordinal.succ_ne_zero _)]
        have : ∃ β, Order.succ γ = Order.succ β := ⟨γ, rfl⟩
        rw [dif_pos this]
        -- The expression is `have this := ...; derivedSet A^(choose this)`
        -- We need to show that it's closed
        exact derivedSet_closed
      · -- Limit case: CB^β(A) = ⋂_{γ<β} CB^γ(A)
        push_neg at hsucc
        -- Intersection of closed sets is closed
        -- We need to show that A^(β) is closed
        -- A^(β) = ⋂_{γ<β} A^(γ) by definition (since β is limit)
        -- For limit ordinals, A^(β) = ⋂ γ < β, A^(γ)
        -- Each A^(γ) is closed by IH, so their intersection is closed
        unfold CantorBendixsonDerivative
        rw [if_neg h0]
        have h_neg : ¬∃ β_1, β = Order.succ β_1 := by
          push_neg
          exact hsucc
        rw [dif_neg h_neg]
        exact isClosed_iInter fun γ => isClosed_iInter fun hγ => ih γ hγ

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
          -- First, show that derivedSet S ⊆ S for closed sets S
          intro x hx
          -- hx : x ∈ A^(Order.succ δ) = derivedSet (A^(δ))
          -- Goal: x ∈ A^(δ)
          have hclosed : IsClosed (A^(δ)) := CB_derivative_closed δ A hA
          -- Use the fact that for closed sets, derivedSet subset the set
          have h_sub : derivedSet (A^(δ)) ⊆ A^(δ) := by
            rw [derivedSet_eq_mathlib]
            exact (isClosed_iff_derivedSet_subset _).mp hclosed
          -- Now unfold A^(Order.succ δ) to show it equals derivedSet (A^(δ))
          -- By definition, A^(Order.succ δ) = derivedSet (A^(δ))
          apply h_sub
          -- Need to show x ∈ derivedSet (A^(δ))
          unfold CantorBendixsonDerivative at hx
          rw [if_neg (Ordinal.succ_ne_zero _)] at hx
          have hex : ∃ β, Order.succ δ = Order.succ β := ⟨δ, rfl⟩
          rw [dif_pos hex] at hx
          convert hx
          have : Classical.choose hex = δ := by
            have : Order.succ δ = Order.succ (Classical.choose hex) := Classical.choose_spec hex
            have : Order.succ (Classical.choose hex) = Order.succ δ := this.symm
            exact Order.succ_eq_succ_iff.mp this
          exact this.symm
        · -- Case α < δ: use IH
          have hα_lt_δ : α < δ := lt_of_le_of_ne hδ hαδ
          have h_sub : A^(δ) ⊆ A^(α) := ih δ (Order.lt_succ δ) (le_of_lt hα_lt_δ)
          -- Need to show A^(Order.succ δ) ⊆ A^(α), i.e., derivedSet (A^(δ)) ⊆ A^(α)
          -- We have A^(δ) ⊆ A^(α), so derivedSet (A^(δ)) ⊆ derivedSet (A^(α))
          -- Since derivedSet is monotone
          trans derivedSet (A^(α))
          · -- Need to show: A^(Order.succ δ) ⊆ derivedSet (A^(α))
            -- First show A^(Order.succ δ) = derivedSet (A^(δ))
            intro x hx
            unfold CantorBendixsonDerivative at hx
            rw [if_neg (Ordinal.succ_ne_zero _)] at hx
            have hex : ∃ β, Order.succ δ = Order.succ β := ⟨δ, rfl⟩
            rw [dif_pos hex] at hx
            have heq : Classical.choose hex = δ := by
              have : Order.succ δ = Order.succ (Classical.choose hex) := Classical.choose_spec hex
              have : Order.succ (Classical.choose hex) = Order.succ δ := this.symm
              exact Order.succ_eq_succ_iff.mp this
            -- hx is of the form x ∈ (have this := ...; derivedSet A^(choose hex))
            -- We need to show x ∈ derivedSet (A^(α))
            apply derivedSet_mono h_sub
            convert hx
            exact heq.symm
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
        intro x hx
        -- hx : x ∈ A^(γ)
        -- By definition of limit case
        unfold CantorBendixsonDerivative at hx
        by_cases h0' : γ = 0
        · -- γ can't be 0 since it's a limit ordinal with γ > α
          exfalso
          rw [h0'] at hlt
          exact absurd hlt (Ordinal.not_lt_zero α)
        rw [if_neg h0'] at hx
        have h_neg : ¬∃ β, γ = Order.succ β := by
          push_neg
          exact hsucc
        rw [dif_neg h_neg] at hx
        -- hx : x ∈ ⋂ β < γ, A^(β)
        -- Since α < γ, we have x ∈ A^(α)
        simp only [Set.mem_iInter] at hx
        exact hx α hlt

/-- The Cantor-Bendixson rank of a set (∞ if no derivative is empty) -/
noncomputable def CantorBendixsonRank (A : Set X) : WithTop Ordinal.{v} :=
  if ∃ α : Ordinal.{v}, CantorBendixsonDerivative A α = ∅ then
    ↑(sInf {α : Ordinal.{v} | CantorBendixsonDerivative A α = ∅})
  else 
    ⊤

/-- The Cantor-Bendixson degree of a compact set with finite rank -/
noncomputable def CantorBendixsonDegree (A : Set X) [CompactSpace X] 
  (h : CantorBendixsonRank A < ⊤) : ℕ :=
  -- The degree is the cardinality of A^(α-1) where α is the rank
  -- Since the rank is finite (not ∞), we can extract it
  match CantorBendixsonRank A, h with
  | some α, _ => 
    -- α is the CB rank
    -- For successor ordinals, the degree is the finite cardinality of the last non-empty derivative
    if α = 0 then 
      -- If rank is 0, then A itself is finite
      -- The degree is the cardinality of A
      if hfin : A.Finite then hfin.toFinset.card else 0
    else if h : ∃ β, α = Order.succ β then
      -- α = β + 1 for some β
      -- The degree is the cardinality of A^(β)
      let β := Classical.choose h
      have : α = Order.succ β := Classical.choose_spec h
      -- A^(β) is finite and non-empty (since A^(α) = ∅ but A^(β) ≠ ∅)
      if hfin : (A^(β)).Finite then hfin.toFinset.card else 0
    else
      -- α is a limit ordinal
      -- This shouldn't happen for finite rank in typical spaces
      0
  | none, h => absurd h (lt_irrefl ⊤)

/-- The rank of a point x is the least α such that x ∉ X^(α) -/
noncomputable def rank (x : X) : Ordinal.{v} :=
  sInf {α : Ordinal.{v} | x ∉ (univ : Set X)^(α)}

-- Additional lemmas about CB derivatives

/-- The CB derivative is empty iff the original set is empty (for 0th derivative) -/
lemma CB_derivative_zero (A : Set X) : A^(0) = A := by
  unfold CantorBendixsonDerivative
  simp

/-- For finite sets in T1 spaces, the derived set is empty -/
lemma derivedSet_of_finite [T1Space X] {A : Set X} (h : A.Finite) : 
  derivedSet A = ∅ := by
  -- In a T1 space, finite sets have no accumulation points
  -- This is because we can isolate each point from the others
  
  -- First, show that finite sets are closed in T1 spaces
  have hclosed : IsClosed A := h.isClosed
  
  -- We'll show that no point can be an accumulation point of A
  ext x
  simp only [mem_derivedSet, Set.mem_empty_iff_false, iff_false]
  -- We need to show: not (∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ A, y ≠ x)
  -- i.e., ∃ U ∈ 𝓝 x, ∀ y ∈ U ∩ A, y = x
  intro h_acc
  
  -- For any x, we'll find a neighborhood that contains at most x from A
  by_cases hx : x ∈ A
  · -- Case 1: x ∈ A
    -- Since A is finite and closed, A \ {x} is also finite and closed
    have h_diff : (A \ {x}).Finite := h.subset (diff_subset)
    have h_diff_closed : IsClosed (A \ {x}) := h_diff.isClosed
    
    -- Since A \ {x} is closed and x ∉ A \ {x}, there's an open neighborhood of x
    -- disjoint from A \ {x}
    have hx_not_in : x ∉ A \ {x} := by simp
    
    -- The complement of A \ {x} is open and contains x
    have h_compl_open : IsOpen (A \ {x})ᶜ := h_diff_closed.isOpen_compl
    have hx_in_compl : x ∈ (A \ {x})ᶜ := by simp
    
    -- Apply h_acc to this neighborhood
    obtain ⟨y, hy_mem, hy_ne_x⟩ := h_acc (A \ {x})ᶜ (h_compl_open.mem_nhds hx_in_compl)
    
    -- Now we have y ∈ ((A \ {x})ᶜ) ∩ A with y ≠ x
    -- This means y ∈ A and y ≠ x, so y ∈ A \ {x}
    have hy_diff : y ∈ A \ {x} := ⟨hy_mem.2, hy_ne_x⟩
    -- But y ∈ (A \ {x})ᶜ, so y ∉ A \ {x}
    have : y ∉ A \ {x} := hy_mem.1
    exact absurd hy_diff this
      
  · -- Case 2: x ∉ A
    -- Since A is closed and x ∉ A, the complement of A is open and contains x
    have h_compl_open : IsOpen Aᶜ := hclosed.isOpen_compl
    have hx_in_compl : x ∈ Aᶜ := hx
    
    -- Apply h_acc to this neighborhood
    obtain ⟨y, hy_mem, _⟩ := h_acc Aᶜ (h_compl_open.mem_nhds hx_in_compl)
    
    -- This is impossible since Aᶜ is disjoint from A
    exact absurd hy_mem.2 hy_mem.1

end CantorBendixson

section OrdinalCantorBendixson

/-- The CB rank of ω^(α+1)·d + 1 is α + 2 -/
theorem CB_rank_successor_ordinal (α : Ordinal.{u}) (d : ℕ) (hd : d ≠ 0) 
  [CompactSpace (X α d)] :
  CantorBendixsonRank (univ : Set (X α d)) = ↑(α + 2) := by
  -- X α d = ω^(α+1)·d + 1 is a successor ordinal
  -- By Proposition in the paper: CB rank = successor of limit capacity
  -- Limit capacity of ω^(α+1)·d + 1 is α+1
  -- So CB rank = (α+1) + 1 = α + 2
  
  -- This is a deep theorem about ordinal topology
  -- The proof requires:
  -- 1. Computing CB derivatives explicitly
  -- 2. Showing (univ)^(α+2) = ∅
  -- 3. Showing (univ)^(α+1) ≠ ∅
  
  -- The paper states this as an exercise using Cantor normal form
  -- and transfinite induction
  
  -- MISSING: Full development of CB derivatives for ordinals
  -- This requires substantial theory about ordinal arithmetic and topology
  sorry

/-- The CB degree of ω^(α+1)·d + 1 is d -/
theorem CB_degree_successor_ordinal (α : Ordinal.{u}) (d : ℕ) (hd : d ≠ 0) 
  [CompactSpace (X α d)] 
  (h_rank : CantorBendixsonRank (univ : Set (X α d)) < ⊤) :
  CantorBendixsonDegree (univ : Set (X α d)) h_rank = d := by
  -- By the paper: CB degree = coefficient
  -- For X α d = ω^(α+1)·d + 1, the coefficient is d
  
  -- By definition, CB degree is the cardinality of (univ)^(α+1)
  -- when CB rank is α+2
  
  -- The points in (univ)^(α+1) are exactly the d maximal points:
  -- ω^(α+1)·1, ω^(α+1)·2, ..., ω^(α+1)·d
  
  -- MISSING: Same as above - requires explicit CB derivative calculations
  sorry

/-- Elements of rank α+1 in ω^(α+1) are exactly the multiples of ω^α -/
lemma rank_classification (α : Ordinal.{u}) (x : X α 1) :
  rank x = α + 1 ↔ ∃ k : ℕ, k ≥ 1 := by
  -- X α 1 = ω^(α+1) + 1
  -- Points of the form k·ω^α where k ≥ 1 have rank α+1
  -- This is because they are isolated in the (α+1)-th derivative
  
  -- The characterization depends on understanding the Cantor normal form
  -- of elements in X α 1
  
  constructor
  · intro h_rank
    -- If rank x = α + 1, then x is of the form k·ω^α for some k ≥ 1
    -- This requires understanding the structure of ordinals
    
    -- MISSING: Need explicit computation of CB derivatives for ordinals
    -- This requires developing the theory of ordinal arithmetic and topology
    sorry
  · intro ⟨k, hk⟩
    -- If x = k·ω^α for k ≥ 1, then rank x = α + 1
    -- This is because such points are exactly those that survive
    -- α derivatives but not α+1 derivatives
    
    -- MISSING: Same as above - requires ordinal arithmetic
    sorry

/-- The rank of a point determines its Cantor normal form structure -/
theorem rank_determines_structure (α : Ordinal.{u}) (x : X α 1) :
  rank x ≤ α + 1 := by
  -- The space X α 1 = ω^(α+1) + 1 has Cantor-Bendixson rank α + 2
  -- So every point has rank at most α + 1
  
  -- This theorem requires knowing that the CB rank of X α 1 is α + 2
  -- which is stated in CB_rank_successor_ordinal
  
  -- The proof would show that (univ)^(α+2) = ∅, which implies
  -- no point can have rank > α + 1
  
  -- MISSING: Requires CB_rank_successor_ordinal or direct computation
  -- of CB derivatives for ordinals
  sorry

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
  -- This is the classification theorem from the paper
  -- Two successor ordinals are homeomorphic iff:
  -- 1. They have the same limit capacity (equivalently, same CB rank)
  -- 2. They have the same coefficient (equivalently, same CB degree)
  
  -- The proof requires showing:
  -- (→) If homeomorphic, then same CB invariants
  -- (←) If same CB invariants, then homeomorphic
  
  -- The forward direction uses that CB rank and degree are topological invariants
  -- The reverse direction uses explicit construction of homeomorphisms
  
  -- MISSING: This is the main classification theorem and requires
  -- developing the full theory of ordinal homeomorphisms
  sorry

end Classification

end OrdinalHomeo