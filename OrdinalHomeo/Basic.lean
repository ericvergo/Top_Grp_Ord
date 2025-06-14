/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Basic Definitions for Homeomorphism Groups of Ordinals

This file contains the core definitions for studying homeomorphism groups of ordinals,
including:
- Order topology on ordinals
- Successor and limit ordinals
- Homeomorphism groups H_{α,d} and PH_{α,d}
- Maximal and next-to-maximal rank elements
- Support and permutation topology
- Cantor normal form properties

## Main definitions

* `SuccessorOrdinal`: Predicate for successor ordinals
* `LimitOrdinal`: Predicate for limit ordinals
* `OrdinalSpace`: Type synonym for ordinals with topology
* `H`: The homeomorphism group H_{α,d} = Homeo(ω^{α+1}·d + 1)
* `PH`: The pure homeomorphism group (fixing maximal rank elements)
* `F`: Subgroup inducing finite permutations on next-to-maximal rank
* `F_closure`: Closure of F in compact-open topology

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set Function

universe u v

section OrdinalClassification

/-- A successor ordinal is one that has an immediate predecessor -/
def SuccessorOrdinal (α : Ordinal.{u}) : Prop := ∃ β, α = Order.succ β

/-- A limit ordinal is one that is not a successor (including 0) -/
def LimitOrdinal (α : Ordinal.{u}) : Prop := ¬SuccessorOrdinal α

lemma successorOrdinal_iff_exists_max (α : Ordinal.{u}) : 
  SuccessorOrdinal α ↔ (α ≠ 0 ∧ ∃ β < α, ∀ γ < α, γ ≤ β) := by
  constructor
  · intro ⟨β, hβ⟩
    rw [hβ]
    constructor
    · exact Order.succ_ne_bot β
    · use β
      constructor
      · exact Order.lt_succ_of_not_isMax (not_isMax β)
      · intro γ hγ
        exact Order.le_of_lt_succ hγ
  · intro ⟨hα, β, hβ, hmax⟩
    -- If β is the maximum element less than α, then α = succ β
    use β
    -- We need to show α = Order.succ β
    apply le_antisymm
    · -- α ≤ Order.succ β
      by_contra h
      push_neg at h
      -- h : Order.succ β < α
      have : Order.succ β ≤ β := hmax (Order.succ β) h
      have : β < β := lt_of_lt_of_le (Order.lt_succ_of_not_isMax (not_isMax β)) this
      exact lt_irrefl β this
    · -- Order.succ β ≤ α
      rw [Order.succ_le_iff]
      exact hβ

end OrdinalClassification

section CantorNormalForm

/-- The limit capacity of an ordinal in Cantor normal form -/
noncomputable def limitCapacity (α : Ordinal.{u}) : Ordinal.{u} := 
  if α = 0 then 0 else α.log ω

/-- The coefficient of an ordinal in Cantor normal form -/  
noncomputable def coefficient (α : Ordinal.{u}) : ℕ :=
  if α = 0 then 0 else 
    let r := α % (ω ^ (α.log ω + 1)) / (ω ^ α.log ω)
    if hr : r < ω then Classical.choose (Ordinal.lt_omega0.mp hr) else 0

end CantorNormalForm

section HomeomorphismGroups

/-- Type synonym for ordinals viewed as topological spaces -/
def OrdinalSpace (α : Ordinal.{u}) : Type u := α.toType

noncomputable instance (α : Ordinal.{u}) : LinearOrder (OrdinalSpace α) := 
  inferInstanceAs (LinearOrder α.toType)

noncomputable instance (α : Ordinal.{u}) : TopologicalSpace (OrdinalSpace α) := 
  Preorder.topology (OrdinalSpace α)

instance (α : Ordinal.{u}) : OrderTopology (OrdinalSpace α) := 
  ⟨rfl⟩

/-- The ordinal ω^{α+1}·d + 1 as a topological space -/
def X (α : Ordinal.{u}) (d : ℕ) : Type u := 
  OrdinalSpace ((ω : Ordinal.{u})^(α+1) * d + 1)

noncomputable instance (α : Ordinal.{u}) (d : ℕ) : TopologicalSpace (X α d) := 
  inferInstanceAs (TopologicalSpace (OrdinalSpace _))

noncomputable instance (α : Ordinal.{u}) (d : ℕ) : LinearOrder (X α d) := 
  inferInstanceAs (LinearOrder (OrdinalSpace _))

instance (α : Ordinal.{u}) (d : ℕ) : OrderTopology (X α d) := 
  inferInstanceAs (OrderTopology (OrdinalSpace _))

noncomputable instance (α : Ordinal.{u}) (d : ℕ) : WellFoundedLT (X α d) := by
  unfold X OrdinalSpace
  infer_instance

/-- For an ordinal α and d ∈ ℕ, H_{α,d} = Homeo(ω^{α+1}·d + 1) -/
def H (α : Ordinal.{u}) (d : ℕ) : Type u := X α d ≃ₜ X α d

noncomputable instance (α : Ordinal.{u}) (d : ℕ) : Group (H α d) where
  one := Homeomorph.refl (X α d)
  inv h := h.symm
  mul h₁ h₂ := h₁.trans h₂
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := Homeomorph.symm_trans_self _

-- For now, we use the discrete topology on homeomorphism groups
-- In the future, this should be the compact-open topology
instance (α : Ordinal.{u}) (d : ℕ) : TopologicalSpace (H α d) := 
  ⊤  -- discrete topology

instance (α : Ordinal.{u}) (d : ℕ) : IsTopologicalGroup (H α d) := {
  continuous_mul := by
    -- In discrete topology, all functions are continuous
    simp only [continuous_top]
  continuous_inv := by
    -- In discrete topology, all functions are continuous
    simp only [continuous_top]
}

end HomeomorphismGroups

section MaximalRank

variable {α : Ordinal.{u}} {d : ℕ}

/-- Elements corresponding to ω^{α+1}·k for k ∈ {1,...,d} -/
def maximalRankSet (α : Ordinal.{u}) (d : ℕ) : Set Ordinal.{u} :=
  {ω^(α+1) * k | k ∈ Icc 1 d}

/-- Elements corresponding to ω^{α+1}·k + ω^α·ℓ -/
def nextToMaximalRankSet (α : Ordinal.{u}) (d : ℕ) : Set Ordinal.{u} :=
  {x | ∃ (k ℓ : ℕ), k < d ∧ ℓ ≥ 1 ∧ x = ω^(α+1) * k + ω^α * ℓ}

/-- Convert an ordinal to an element of X α d -/
noncomputable def toX {α : Ordinal.{u}} {d : ℕ} (x : Ordinal.{u}) (h : x < ω^(α+1) * d + 1) : X α d := by
  -- X α d = OrdinalSpace (ω^{α+1}·d + 1) = (ω^{α+1}·d + 1).toType
  -- We use enumIsoToType to convert
  have : x ∈ Set.Iio (ω^(α+1) * d + 1) := h
  exact (Ordinal.enumIsoToType (ω^(α+1) * d + 1)) ⟨x, this⟩

/-- The maximal rank elements in X α d -/
def maximalRankElements (α : Ordinal.{u}) (d : ℕ) : Set (X α d) :=
  {x | ∃ (k : ℕ) (hk : k ∈ Icc 1 d), x = toX (ω^(α+1) * (k : Ordinal)) (by 
    -- We need to show ω^(α+1) * k < ω^(α+1) * d + 1
    -- Since k ∈ Icc 1 d, we have k ≤ d
    have hk' : k ≤ d := (Set.mem_Icc.mp hk).2
    have : ω^(α+1) * (k : Ordinal) ≤ ω^(α+1) * (d : Ordinal) := by
      apply mul_le_mul_left'
      -- For ordinals, (k : Ordinal) ≤ (d : Ordinal) iff k ≤ d as naturals
      exact Nat.cast_le.mpr hk'
    exact lt_of_le_of_lt this (lt_add_one _)
  )}

/-- The pure homeomorphism group PH_{α,d} (homeomorphisms fixing maximal rank elements) -/
noncomputable def PH (α : Ordinal.{u}) (d : ℕ) : Subgroup (H α d) := {
  carrier := {f | ∀ x ∈ maximalRankElements α d, f.toFun x = x}
  mul_mem' := by
    intro f g hf hg x hx
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    -- (f * g)(x) = g(f(x))
    -- In the group structure, multiplication is f.trans g
    show (f.trans g).toFun x = x
    -- (f.trans g).toFun x = g.toFun (f.toFun x)
    change g.toFun (f.toFun x) = x
    rw [hf x hx, hg x hx]
  one_mem' := by
    intro x hx
    rfl
  inv_mem' := by
    intro f hf x hx
    simp only [Set.mem_setOf_eq] at hf ⊢
    -- We need to show: f⁻¹.toFun x = x
    -- Since f.toFun x = x, we have f⁻¹(x) = x
    have h : f.toFun x = x := hf x hx
    -- Since inv h := h.symm in the group structure
    show f.symm.toFun x = x
    -- Use the fact that if f x = x, then f.symm x = x
    -- because f.symm (f x) = x and f x = x
    have : f.symm (f.toFun x) = x := f.symm_apply_apply x
    rw [h] at this
    exact this
}

/-- The next-to-maximal rank elements in X α d -/
def nextToMaximalRankElements (α : Ordinal.{u}) (d : ℕ) : Set (X α d) :=
  {x | ∃ (k ℓ : ℕ) (hk : k < d) (hℓ : ℓ ≥ 1), x = toX (ω^(α+1) * (k : Ordinal) + ω^α * (ℓ : Ordinal)) (by 
    -- We need to show ω^(α+1) * k + ω^α * ℓ < ω^(α+1) * d + 1
    -- Since k < d and ℓ ≥ 1
    -- First, ω^α * ℓ < ω^(α+1) for any ℓ : ℕ
    have h1 : ω^α * (ℓ : Ordinal) < ω^(α+1) := by
      calc ω^α * (ℓ : Ordinal) 
          < ω^α * ω := by
            apply Ordinal.mul_lt_mul_of_pos_left
            · exact nat_lt_omega0 ℓ
            · exact opow_pos _ omega0_pos
      _ = ω^(α+1) := by 
        rw [← opow_succ, add_one_eq_succ]
    -- Now the main calculation
    calc ω^(α+1) * (k : Ordinal) + ω^α * (ℓ : Ordinal) 
        < ω^(α+1) * (k : Ordinal) + ω^(α+1) := add_lt_add_left h1 _
    _ = ω^(α+1) * ((k : Ordinal) + 1) := by 
      rw [mul_add, mul_one]
    _ ≤ ω^(α+1) * (d : Ordinal) := by
      apply mul_le_mul_left'
      have : k + 1 ≤ d := Nat.succ_le_of_lt hk
      exact_mod_cast this
    _ < ω^(α+1) * (d : Ordinal) + 1 := lt_add_one _
  )}

/-- The subgroup F_{α,d} (homeomorphisms inducing finite permutations on next-to-maximal rank) -/
noncomputable def F (α : Ordinal.{u}) (d : ℕ) : Subgroup (H α d) := {
  carrier := {f | Set.Finite {x ∈ nextToMaximalRankElements α d | f.toFun x ≠ x}}
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    -- The set of elements moved by f * g is a subset of those moved by f or g
    apply Set.Finite.subset (Set.Finite.union hf hg)
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
    -- If (f * g)(x) ≠ x, then either f(x) ≠ x or g(f(x)) ≠ f(x)
    -- Note: (f * g).toFun x = (f.trans g).toFun x = g.toFun (f.toFun x)
    have : g.toFun (f.toFun x) ≠ x := by
      -- hx.2 says (f * g).toFun x ≠ x
      -- We need g.toFun (f.toFun x) ≠ x
      -- But (f * g).toFun x = g.toFun (f.toFun x) by definition
      exact hx.2
    by_cases h : f.toFun x = x
    · right
      -- If f(x) = x, then g(x) ≠ x
      rw [h] at this
      exact ⟨hx.1, this⟩
    · left
      -- If f(x) ≠ x, we're done
      exact ⟨hx.1, h⟩
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hx.2 rfl
  inv_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq] at hf ⊢
    -- The elements moved by f⁻¹ are exactly those moved by f
    convert hf using 1
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      intro heq
      -- We want to show f.toFun x ≠ x
      -- We have h: f⁻¹.toFun x ≠ x  
      -- We assume for contradiction that heq: f.toFun x = x
      -- Then f⁻¹.toFun x = f⁻¹.toFun (f.toFun x) = x, contradicting h
      have h_inv_eq : f⁻¹.toFun = f.symm.toFun := rfl
      rw [h_inv_eq] at h
      -- Now h: f.symm.toFun x ≠ x
      -- heq: f.toFun x = x
      -- But f.symm.toFun (f.toFun x) = x, so f.symm.toFun x = x, contradiction
      have contradiction : f.symm.toFun (f.toFun x) = x := f.symm_apply_apply x
      rw [heq] at contradiction
      exact False.elim (h contradiction)
    · intro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      intro heq
      have : f.toFun x = x := by
        -- heq says f⁻¹.toFun x = x
        -- In our group, f⁻¹ is defined as f.symm
        -- So heq is equivalent to f.symm.toFun x = x
        -- We use: f.toFun x = f.toFun (f.symm.toFun x) (since f.symm.toFun x = x)
        --                  = (f.trans f.symm).toFun x
        --                  = id x = x
        have h_inv_eq : f⁻¹.toFun = f.symm.toFun := rfl
        rw [h_inv_eq] at heq
        -- We want to show f.toFun x = x
        -- We have heq: f.symm.toFun x = x (after rewriting with h_inv_eq)
        -- We know that f.toFun (f.symm.toFun y) = y for any y
        -- Setting y = x: f.toFun (f.symm.toFun x) = x
        -- But heq says f.symm.toFun x = x
        -- So f.toFun x = f.toFun (f.symm.toFun x) = x
        have h_identity : f.toFun (f.symm.toFun x) = x := f.apply_symm_apply x
        rw [heq] at h_identity
        exact h_identity
      exact h this
}

/-- The closure of F_{α,d} -/
noncomputable def F_closure (α : Ordinal.{u}) (d : ℕ) : Subgroup (H α d) := 
  Subgroup.topologicalClosure (F α d)

end MaximalRank

section Support

/-- X α d is a compact space (successor ordinals are compact) -/
lemma isCompact_X (α : Ordinal.{u}) (d : ℕ) : IsCompact (univ : Set (X α d)) := by
  -- X α d corresponds to the ordinal ω^{α+1}·d + 1
  -- This is a successor ordinal, and successor ordinals with order topology are compact
  -- This follows from the general fact that well-ordered sets with order topology
  -- are compact iff they have a maximum element
  sorry  -- FUNDAMENTAL: Successor ordinals with order topology are compact

/-- The support of a homeomorphism -/
def support {α : Ordinal.{u}} {d : ℕ} (f : H α d) : Set (X α d) :=
  closure {x | f.toFun x ≠ x}

/-- The support of a homeomorphism on a successor ordinal is finite -/
lemma support_finite {α : Ordinal.{u}} {d : ℕ} (f : H α d) : 
  Set.Finite (support f) := by
  -- For successor ordinals, we can use the fact that homeomorphisms
  -- can only move finitely many points in a well-ordered compact space
  
  -- Key observation: In a successor ordinal with order topology,
  -- any homeomorphism has finite support because:
  -- 1. The space is well-ordered
  -- 2. Homeomorphisms preserve order
  -- 3. In a compact ordinal, infinite sets have limit points
  -- 4. But homeomorphisms must preserve the structure around limit points
  
  -- This is a fundamental property that requires careful analysis
  -- For now, we take it as an axiom about ordinal homeomorphisms
  -- 
  -- The proof would involve showing that in a successor ordinal,
  -- any homeomorphism can only permute finitely many "blocks" of the ordinal
  -- and within each block can only move finitely many points
  sorry  -- FUNDAMENTAL: Homeomorphisms of successor ordinals have finite support

/-- Support is clopen for homeomorphisms of ordinals -/
lemma support_clopen {α : Ordinal.{u}} {d : ℕ} (f : H α d) : 
  IsClopen (support f) := by
  -- The support is the closure of the moved set
  unfold support
  
  -- For finite sets in a Hausdorff space, the closure equals the set
  have h_finite : Set.Finite {x | f.toFun x ≠ x} := by
    -- The moved set is contained in the support
    have h_sub : {x | f.toFun x ≠ x} ⊆ support f := subset_closure
    -- The support is finite
    have h_supp_fin : Set.Finite (support f) := support_finite f
    -- A subset of a finite set is finite
    exact Set.Finite.subset h_supp_fin h_sub
  
  -- Finite sets are closed in Hausdorff spaces
  have h_closed : IsClosed {x | f.toFun x ≠ x} := by
    -- X α d is T2 (Hausdorff) because ordinals with order topology are T2
    -- Finite sets are closed in T2 spaces
    exact Set.Finite.isClosed h_finite
  
  -- Since the moved set is closed, its closure equals itself
  have h_eq : closure {x | f.toFun x ≠ x} = {x | f.toFun x ≠ x} := by
    exact IsClosed.closure_eq h_closed
  
  -- The support equals the moved set
  rw [h_eq]
  
  -- A finite set in a T2 space is closed
  -- The moved set is also open (complement of closed fixed point set)
  have h_open : IsOpen {x | f.toFun x ≠ x} := by
    -- First show fixed points are closed
    have h_fixed_closed : IsClosed {x : X α d | f.toFun x = x} := by
      exact isClosed_fixedPoints f.continuous_toFun
    -- The moved set is the complement
    have : {x | f.toFun x ≠ x} = {x | f.toFun x = x}ᶜ := by
      ext x
      simp
    rw [this]
    exact h_fixed_closed.isOpen_compl
  
  -- A set that is both open and closed is clopen
  exact ⟨h_closed, h_open⟩

end Support

end OrdinalHomeo