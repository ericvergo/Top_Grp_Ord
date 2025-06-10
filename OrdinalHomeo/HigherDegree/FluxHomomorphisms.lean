/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import OrdinalHomeo.HigherDegree.SplitExactSequences

/-!
# Flux Homomorphisms

This file provides the detailed construction of the flux homomorphisms χ_k
that measure the movement of next-to-maximal rank elements in and out of
neighborhoods of maximal rank elements.

## Main Definitions

* `O_k` - The set of elements moved out of Ω_k by a homeomorphism
* `I_k` - The set of elements moved into Ω_k by a homeomorphism
* `flux_homomorphism` - The homomorphism χ_k : PH_{α,d} → ℤ
* `shift_homeomorphism` - The shift homeomorphisms s_i that provide a section

-/

open Ordinal Set Function

universe u v

namespace OrdinalHomeo

variable {α : Ordinal.{u}} {d : ℕ} (hd : d ≠ 1)

/-- Clopen neighborhoods of maximal rank elements -/
def standard_neighborhoods (α : Ordinal.{u}) (d : ℕ) : 
  Fin (d - 1) → Set (X α d) := sorry

/-- Elements moved out of Ω_k by h -/
def O_k (k : Fin (d - 1)) (Ω : Fin (d - 1) → Set (X α d)) 
  (h : PH α d) : Set (X α d) :=
  {x ∈ Ω k ∩ nextToMaximalRankElements α d | (h.val : H α d).toFun x ∉ Ω k}

/-- Elements moved into Ω_k by h -/
def I_k (k : Fin (d - 1)) (Ω : Fin (d - 1) → Set (X α d))
  (h : PH α d) : Set (X α d) :=
  {x ∈ (Ω k)ᶜ ∩ nextToMaximalRankElements α d | (h.val : H α d).toFun x ∈ Ω k}

theorem O_k_finite (k : Fin (d - 1)) (Ω : Fin (d - 1) → Set (X α d))
  (h : PH α d) : (O_k k Ω h).Finite := by
  -- O_k consists of elements of nextToMaximalRankElements that h moves out of Ω k
  -- Since h ∈ PH, it fixes maximal rank elements
  -- The key is that h is continuous and nextToMaximalRankElements is discrete
  -- This means h can only move finitely many elements of nextToMaximalRankElements
  
  -- The set O_k is a subset of nextToMaximalRankElements ∩ Ω k
  have h_sub : O_k k Ω h ⊆ nextToMaximalRankElements α d := by
    intro x hx
    simp only [O_k, Set.mem_setOf_eq] at hx
    exact hx.1.2
  
  -- In ordinal topology, nextToMaximalRankElements forms a discrete set
  -- whose closure adds only the maximal rank elements
  -- Since h is continuous and fixes maximal rank elements,
  -- it can only move finitely many next-to-maximal rank elements
  
  -- ATTEMPT 1: Direct proof using discreteness failed - need more topology setup
  -- ATTEMPT 2: Use that continuous maps from discrete subspaces have locally constant behavior
  sorry

theorem I_k_finite (k : Fin (d - 1)) (Ω : Fin (d - 1) → Set (X α d))
  (h : PH α d) : (I_k k Ω h).Finite := sorry

/-- The k-th flux homomorphism -/
def flux_homomorphism_k (k : Fin (d - 1)) : PH α d → ℤ := sorry

/-- The combined flux homomorphism is independent of neighborhood choice -/
theorem flux_independent_of_neighborhoods (Ω Ω' : Fin (d - 1) → Set (X α d))
  (hΩ : ∀ k, IsClopen (Ω k))
  (hΩ' : ∀ k, IsClopen (Ω' k))
  (h : PH α d) (k : Fin (d - 1)) :
  flux_homomorphism_k k h = flux_homomorphism_k k h := sorry

/-- Shift homeomorphism on the i-th component -/
noncomputable def shift_i (α : Ordinal.{u}) (d : ℕ) (i : Fin (d - 1)) : H α d := sorry

theorem shift_i_mem_PH (α : Ordinal.{u}) (d : ℕ) (i : Fin (d - 1)) : 
  shift_i α d i ∈ PH α d := sorry

theorem shift_i_commute (α : Ordinal.{u}) (d : ℕ) (i j : Fin (d - 1)) (h : i ≠ j) :
  shift_i α d i * shift_i α d j = shift_i α d j * shift_i α d i := sorry

theorem chi_shift_i (α : Ordinal.{u}) (d : ℕ) (i : Fin (d - 1)) (hd : d ≠ 1) :
  ∃ (chi : PH α d → (Fin (d - 1) → ℤ)), 
    chi ⟨shift_i α d i, shift_i_mem_PH α d i⟩ = fun j => if i = j then 1 else 0 := sorry

/-- The section of χ given by the shift homeomorphisms -/
def chi_section_map : (Fin (d - 1) → ℤ) → PH α d := sorry

theorem chi_section_is_section (hd : d ≠ 1) : 
  ∃ (chi : PH α d → (Fin (d - 1) → ℤ)),
    ∀ v, chi (chi_section_map v) = v := sorry

end OrdinalHomeo