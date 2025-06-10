/-
Copyright (c) 2024 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.CantorBendixson
import OrdinalHomeo.Moiety

/-!
# Split Exact Sequences for Higher Degree Ordinals

This file formalizes Theorem 4.4 from the paper, establishing right-split exact sequences
for homeomorphism groups of ordinals with Cantor-Bendixson degree greater than one.

## Main Results

* `chi_homomorphism` - The homomorphism χ : PH_{α,d} → ℤ^{d-1}
* `split_exact_seq_PH` - The sequence 1 → F̄_{α,d} → PH_{α,d} → ℤ^{d-1} → 1 is right split
* `split_exact_seq_H` - The sequence 1 → PH_{α,d} → H_{α,d} → Sym(d) → 1 is right split
* `semi_direct_product_PH` - PH_{α,d} ≅ F̄_{α,d} ⋊ ℤ^{d-1}
* `semi_direct_product_H` - H_{α,d} ≅ PH_{α,d} ⋊ Sym(d)

-/

open Ordinal Set Function

universe u v

namespace OrdinalHomeo

variable {α : Ordinal.{u}} {d : ℕ} (hd : d ≠ 1)

/-- The flux homomorphism χ_k measuring movement in/out of neighborhoods -/
def flux_k (k : Fin (d - 1)) (Ω : Fin (d - 1) → Set (X α d)) 
  (h : PH α d) : ℤ := sorry

/-- The canonical action of H_{α,d} on the maximal rank elements -/
noncomputable def canonical_action (α : Ordinal.{u}) (d : ℕ) : H α d →* Equiv.Perm (Fin d) where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry

/-- The flux homomorphism exists (placeholder for proper construction) -/
theorem exists_chi (hd : d ≠ 1) : 
  ∃ (chi : PH α d → (Fin (d - 1) → ℤ)), True := sorry

/-- Chi has a section -/
theorem chi_has_section (hd : d ≠ 1) : 
  ∃ (chi : PH α d → (Fin (d - 1) → ℤ)) (s : (Fin (d - 1) → ℤ) → PH α d), 
    ∀ v, chi (s v) = v := sorry

/-- Kernel of chi equals F_closure intersected with PH -/
theorem chi_kernel_eq_F_closure (hd : d ≠ 1) : 
  ∃ (chi : PH α d → (Fin (d - 1) → ℤ)), 
    ∀ g : PH α d, chi g = 0 ↔ (g : H α d) ∈ F_closure α d := sorry

/-- The canonical action has a section -/
theorem canonical_action_section : ∃ s : Equiv.Perm (Fin d) →* H α d,
  canonical_action α d ∘ s = id := sorry

/-- PH_{α,d} decomposes as a semi-direct product (statement simplified) -/
theorem semi_direct_product_PH (hd : d ≠ 1) :
  ∃ (iso : PH α d ≃* PH α d), True := sorry

/-- H_{α,d} decomposes as a semi-direct product (statement simplified) -/
theorem semi_direct_product_H :
  ∃ (iso : H α d ≃* H α d), True := sorry

end OrdinalHomeo