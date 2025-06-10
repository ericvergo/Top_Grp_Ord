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

open Ordinal Topology Set

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
    · exact Ordinal.succ_ne_zero β
    · use β
      constructor
      · sorry -- β < succ β
      · intro γ hγ
        sorry -- Need the correct lemma name for le_of_lt_succ
  · intro ⟨hα, β, hβ, hmax⟩
    -- If β is the maximum element less than α, then α = succ β
    sorry

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
  -- This requires proper handling of ordinal embeddings
  sorry

/-- The maximal rank elements in X α d -/
def maximalRankElements (α : Ordinal.{u}) (d : ℕ) : Set (X α d) :=
  {toX (ω^(α+1) * k) (by sorry) | k ∈ Icc 1 d}

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
    -- f⁻¹(x) = y iff f(y) = x
    -- Since f(x) = x, we have f⁻¹(x) = x
    have : f.toFun x = x := hf x hx
    -- Use the fact that f is bijective
    -- We need: f.symm.toFun x = x
    -- We know: f.toFun x = x
    -- f.symm is the inverse of f, so if f fixes x, then f.symm fixes x too
    -- We want to show: f.symm.toFun x = x
    -- We know: f.toFun x = x
    -- Key fact: f.symm.toFun y = z iff f.toFun z = y
    -- So: f.symm.toFun x = z iff f.toFun z = x
    -- Since f.toFun x = x, we have z = x
    sorry  -- This requires showing that fixed points of f are also fixed points of f.symm
}

/-- The next-to-maximal rank elements in X α d -/
def nextToMaximalRankElements (α : Ordinal.{u}) (d : ℕ) : Set (X α d) :=
  {x | ∃ (k ℓ : ℕ), k < d ∧ ℓ ≥ 1 ∧ x = toX (ω^(α+1) * k + ω^α * ℓ) (by sorry)}

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
      apply h
      -- We need to show f.symm.toFun (f.toFun x) ≠ f.toFun x
      -- But f.symm.toFun (f.toFun x) = x by definition
      -- And heq says f.toFun x = x
      -- So we need x ≠ x, which is what h says
      sorry
    · intro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      intro heq
      have : f.toFun x = x := by
        -- heq says f.symm.toFun x = x
        -- We need f.toFun x = x
        -- This follows because f and f.symm are inverses
        sorry
      exact h this
}

/-- The closure of F_{α,d} -/
noncomputable def F_closure (α : Ordinal.{u}) (d : ℕ) : Subgroup (H α d) := 
  Subgroup.topologicalClosure (F α d)

end MaximalRank

section Support

/-- The support of a homeomorphism -/
def support {α : Ordinal.{u}} {d : ℕ} (f : H α d) : Set (X α d) :=
  closure {x | f.toFun x ≠ x}

/-- Support is clopen for homeomorphisms of ordinals -/
lemma support_clopen {α : Ordinal.{u}} {d : ℕ} (f : H α d) : 
  IsClopen (support f) := by
  -- In ordinal topology, the set of fixed points is closed, hence its complement is open
  -- Since ordinals are zero-dimensional, every open set is also closed
  sorry -- This requires understanding that ordinals are zero-dimensional spaces

end Support

end OrdinalHomeo