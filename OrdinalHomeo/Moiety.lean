/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.CantorBendixson

/-!
# Topological Moieties

This file defines topological moieties in ordinals and establishes their key properties.
A topological moiety is a clopen subset that contains infinitely many maximal rank points,
as does its complement.

## Main definitions

* `TopologicalMoiety`: A clopen subset with infinitely many rank α+1 points in both it and its complement
* `convergentTranslation`: A homeomorphism that translates a moiety off itself with local finiteness
* `StableNeighborhood`: A clopen neighborhood where a point has unique maximal rank

## Main results

* Every topological moiety is homeomorphic to ω^(α+1)
* Change of coordinates principle for moieties
* Existence of convergent translations

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set

universe u

section TopologicalMoieties

/-- A topological moiety in ω^(α+1) -/
def TopologicalMoiety (α : Ordinal.{u}) (A : Set (X α 1)) : Prop :=
  IsClopen A ∧ 
  (∃ S : Set (X α 1), Set.Infinite S ∧ S ⊆ A ∧ ∀ x ∈ S, rank x = α + 1) ∧
  (∃ S : Set (X α 1), Set.Infinite S ∧ S ⊆ Aᶜ ∧ ∀ x ∈ S, rank x = α + 1)

/-- Every topological moiety is homeomorphic to ω^(α+1) -/
theorem moiety_homeomorphic_to_ordinal {α : Ordinal.{u}} {A : Set (X α 1)} 
  (hA : TopologicalMoiety α A) : 
  Nonempty (A ≃ₜ X α 1) := by
  sorry

/-- Change of coordinates: Any two moieties are related by a homeomorphism -/
lemma change_of_coordinates {α : Ordinal.{u}} {A B : Set (X α 1)}
  (hA : TopologicalMoiety α A) (hB : TopologicalMoiety α B) :
  ∃ σ : H α 1, σ.toFun '' A = B := by
  sorry

/-- If two moieties are disjoint, there's an involution swapping them -/
lemma disjoint_moiety_involution {α : Ordinal.{u}} {A B : Set (X α 1)}
  (hA : TopologicalMoiety α A) (hB : TopologicalMoiety α B) (hAB : A ∩ B = ∅) :
  ∃ ι : H α 1, ι.toFun '' A = B ∧ ι.trans ι = Homeomorph.refl _ ∧ support ι ⊆ A ∪ B := by
  sorry

end TopologicalMoieties

section Translations

/-- An A-translation is a homeomorphism with pairwise disjoint iterates of A -/
def isTranslation {α : Ordinal.{u}} (φ : H α 1) (A : Set (X α 1)) : Prop :=
  ∀ n m : ℤ, n ≠ m → 
    (if n ≥ 0 then φ.toFun^[n.toNat] else φ.symm.toFun^[(-n).toNat]) '' A ∩ 
    (if m ≥ 0 then φ.toFun^[m.toNat] else φ.symm.toFun^[(-m).toNat]) '' A = ∅

/-- A convergent A-translation has locally finite iterates -/
def isConvergentTranslation {α : Ordinal.{u}} (φ : H α 1) (A : Set (X α 1)) : Prop :=
  isTranslation φ A ∧ 
  ∀ K : Set (X α 1), IsCompact K → 
    Set.Finite {n : ℤ | 
      (if n ≥ 0 then φ.toFun^[n.toNat] else φ.symm.toFun^[(-n).toNat]) '' A ∩ K ≠ ∅}

/-- Existence of convergent translations for moieties -/
theorem exists_convergent_translation {α : Ordinal.{u}} {A : Set (X α 1)}
  (hA : TopologicalMoiety α A) :
  ∃ φ : H α 1, isConvergentTranslation φ A ∧ 
    TopologicalMoiety α (support φ) := by
  sorry

end Translations

section StableNeighborhoods

/-- A stable neighborhood has a unique element of maximal rank -/
def StableNeighborhood {α : Ordinal.{u}} (U : Set (X α 1)) (b : X α 1) : Prop :=
  IsClopen U ∧ b ∈ U ∧ ∀ x ∈ U, x ≠ b → rank.{u, u} x < rank.{u, u} b

/-- Every point has arbitrarily small stable neighborhoods -/
lemma exists_stable_neighborhood {α : Ordinal.{u}} (b : X α 1) :
  ∀ V ∈ 𝓝 b, ∃ U ⊆ V, StableNeighborhood U b := by
  sorry

/-- Stable neighborhoods of points of rank β+1 are homeomorphic to ω^β + 1 -/
theorem stable_neighborhood_homeomorphism {α β : Ordinal.{u}} {U : Set (X α 1)} 
  {b : X α 1} (hU : StableNeighborhood U b) (hb : rank b = β + 1) :
  Nonempty (U ≃ₜ X β 1) := by
  sorry

end StableNeighborhoods

section Support

-- support_clopen is already defined in Basic.lean

/-- Alternative characterization of being outside the support -/
lemma not_mem_support_iff {α : Ordinal.{u}} {d : ℕ} (f : H α d) (x : X α d) :
  x ∉ support f ↔ f.toFun x = x := by
  rw [support]
  simp only [mem_closure_iff, not_forall, not_and, exists_prop]
  push_neg
  constructor
  · intro h
    by_contra h_contra
    have : x ∈ {y | f.toFun y ≠ y} := h_contra
    -- Since x is not in the closure, there exists an open set containing x
    -- that's disjoint from the set of moved points
    obtain ⟨U, hU_open, hU_mem, hUdisj⟩ := h
    have : (U ∩ {y | f.toFun y ≠ y}).Nonempty := ⟨x, hU_mem, this⟩
    rw [Set.nonempty_iff_ne_empty] at this
    exact this hUdisj
  · intro hfx
    -- If f x = x, then x is not in the closure of {y | f.toFun y ≠ y}
    -- Strategy: Use continuity of f and the fact that ordinals have a basis of clopen sets
    
    -- Since f is continuous and f(x) = x, by continuity of f at x:
    -- For the open neighborhood {f(x)} = {x} of f(x), there exists U ∈ 𝓝 x with f(U) ⊆ {x}
    -- This means for all y ∈ U, f(y) = x
    
    -- But we need something stronger: a neighborhood where f acts as identity
    -- Use the fact that f is a homeomorphism (bijective and continuous)
    
    -- Key insight: If f is continuous, f(x) = x, and f is injective,
    -- then there exists a neighborhood U of x where f|_U = id|_U
    
    -- For now, let's use a direct approach
    -- The set {y | f y ≠ y} is open (as complement of closed fixed point set)
    -- Since x is not in this open set, there's a neighborhood of x disjoint from it
    
    sorry

/-- If homeomorphisms have disjoint clopen supports, each preserves the other's support -/
lemma support_preserved_of_disjoint {α : Ordinal.{u}} (f g : H α 1)
  (h : support f ∩ support g = ∅) 
  (hf_clopen : IsClopen (support f)) (hg_clopen : IsClopen (support g)) :
  f.toFun '' (support g) ⊆ support g ∧ g.toFun '' (support f) ⊆ support f := by
  constructor
  · -- Show f preserves support g
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    by_contra h_notin
    -- If f(x) ∉ support g, then since support g is clopen (hence open),
    -- there's a neighborhood U of f(x) disjoint from support g
    -- By continuity of f⁻¹, f⁻¹(U) is a neighborhood of x
    -- Since x ∈ support g (closed), f⁻¹(U) ∩ support g is nonempty
    -- So there exists z ∈ f⁻¹(U) ∩ support g, meaning f(z) ∈ U
    -- But f(z) ∈ support g (by what we're trying to prove), contradiction
    sorry
  · -- By symmetry
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    sorry

/-- Key lemma: disjoint clopen supports are preserved by homeomorphisms -/
lemma disjoint_support_preserved {α : Ordinal.{u}} (f g : H α 1) 
  (h : support f ∩ support g = ∅) (hg_clopen : IsClopen (support g)) :
  f.toFun '' (support g)ᶜ ⊆ (support g)ᶜ := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  -- x ∉ support g, need to show f x ∉ support g
  -- Actually, this is not generally true without more assumptions
  -- Let's use a different approach: if supports are disjoint and clopen,
  -- then the restriction of f to (support g)ᶜ is well-defined
  sorry

/-- Homeomorphisms with disjoint supports commute -/
lemma disjoint_support_commute {α : Ordinal.{u}} (f g : H α 1) 
  (h : support f ∩ support g = ∅) : f * g = g * f := by
  -- Two homeomorphisms commute if they have disjoint supports
  -- H α 1 = X α 1 ≃ₜ X α 1, so use Homeomorph.ext
  apply Homeomorph.ext
  intro x
  
  -- We need to show (f * g) x = (g * f) x
  -- Since multiplication is composition (trans), this means f (g x) = g (f x)
  
  -- Since supports are closed and disjoint, for any x:
  -- if f moves x, then g fixes x (and vice versa)
  -- if g moves f(x), then f(x) ∈ support g, but support g is disjoint from support f
  
  -- The goal after Homeomorph.ext is to show the functions are equal at x
  -- i.e., ⇑(f * g) x = ⇑(g * f) x
  
  -- Case analysis on whether x is in either support
  by_cases hfx : f.toFun x = x
  · -- f fixes x
    by_cases hgx : g.toFun x = x
    · -- Both fix x
      -- Both fix x, so (f * g) x = g (f x) = g x = x
      -- and (g * f) x = f (g x) = f x = x
      -- The goal is (f * g) x = (g * f) x
      -- Since both f and g fix x, both sides equal x
      -- Since both fix x, we can directly show both sides equal x
      have h1 : (f * g).toFun x = x := by
        -- (f * g) = f.trans g in the group structure
        -- By definition, (f * g) x = g (f x)
        -- Since f x = x and g x = x, we get x
        calc (f * g).toFun x = g.toFun (f.toFun x) := rfl
        _ = g.toFun x := by rw [hfx]
        _ = x := hgx
      have h2 : (g * f).toFun x = x := by
        -- Similarly, (g * f).toFun x = f.toFun (g.toFun x) = x
        calc (g * f).toFun x = f.toFun (g.toFun x) := rfl
        _ = f.toFun x := by rw [hgx]
        _ = x := hfx
      -- The goal has coercion notation, need to convert
      change (f * g).toFun x = (g * f).toFun x
      rw [h1, h2]
    · -- f fixes x, g moves x
      -- Then x ∈ support g
      have hxg : x ∈ support g := by
        apply subset_closure
        -- hgx : ¬(g.toFun x = x), which is the same as g.toFun x ≠ x
        exact hgx
      -- Since supports are disjoint, x ∉ support f
      have hxf : x ∉ support f := by
        intro hcontra
        have : x ∈ support f ∩ support g := ⟨hcontra, hxg⟩
        rw [h] at this
        exact absurd this (Set.notMem_empty x)
      -- We need to show g(f(x)) = f(g(x)) = g(x) [since f x = x]
      -- Since g moves x and supports are disjoint, g(x) ∉ support f
      have gx_notin : g.toFun x ∉ support f := by
        -- We'll show that if f and g have disjoint supports, g(x) ∉ support f
        -- Key: if g(x) ∈ support f, then x ∈ g⁻¹(support f)
        -- But x ∈ support g (since g moves x), so x ∈ support g ∩ g⁻¹(support f)
        -- We'll show this intersection is empty due to disjoint supports
        by_contra h_contra
        -- Suppose g(x) ∈ support f
        -- Then x ∈ g⁻¹(support f)
        have : x ∈ g.toFun⁻¹' (support f) := by
          exact h_contra
        -- But x ∈ support g, so x is in the intersection
        have : x ∈ support g ∩ g.toFun⁻¹' (support f) := ⟨hxg, this⟩
        -- We'll show this intersection is contained in support f ∩ support g = ∅
        -- For any y ∈ support g with g(y) ∈ support f:
        -- Since y ∈ support g, g doesn't fix y
        -- Since g(y) ∈ support f, f doesn't fix g(y)
        -- But if supports are disjoint and g moves y, then f fixes y
        -- So f(g(y)) ≠ g(y), but also f(y) = y, which gives f(g(y)) ≠ g(f(y))
        -- This contradicts commutativity on the complement of both supports
        
        -- Let's think differently: if g(x) ∈ support f, then f moves g(x)
        -- So there exists a neighborhood U of g(x) where f is not the identity
        -- Since g is continuous and moves x, we can pull back to get a neighborhood
        -- of x where g⁻¹ ∘ f ∘ g differs from the identity
        -- But on support g, we have g⁻¹ ∘ f ∘ g = f (by the disjointness)
        -- This means f moves points in support g, contradicting disjointness
        
        -- Actually, let's use that support is the closure of moved points
        -- If g(x) ∈ support f, then g(x) is in the closure of {y | f y ≠ y}
        -- Since f and g have disjoint supports and x ∈ support g,
        -- we must have f x = x (as x ∉ support f)
        -- But then g(x) being in support f while x is not creates issues
        
        -- For now, we'll leave this as is - it requires careful topological argument
        sorry
      -- So f(g(x)) = g(x)
      have fgx_eq : f.toFun (g.toFun x) = g.toFun x := by
        exact not_mem_support_iff f (g.toFun x) |>.mp gx_notin
      -- Now compute: (f * g) x = g (f x) = g x = f (g x) = (g * f) x
      show (f * g).toFun x = (g * f).toFun x
      -- The goal is (f * g) x = (g * f) x
      -- We have hfx : f.toFun x = x and fgx_eq : f.toFun (g.toFun x) = g.toFun x
      calc (f * g).toFun x = (f.trans g).toFun x := rfl
      _ = g.toFun (f.toFun x) := rfl
      _ = g.toFun x := by rw [hfx]
      _ = f.toFun (g.toFun x) := fgx_eq.symm
      _ = (g.trans f).toFun x := rfl
      _ = (g * f).toFun x := rfl
  · -- f moves x  
    -- Then x ∈ support f
    have hxf : x ∈ support f := by
      apply subset_closure
      -- hfx : ¬(f.toFun x = x), which is the same as f.toFun x ≠ x
      exact hfx
    -- Since supports are disjoint, x ∉ support g
    have hxg : x ∉ support g := by
      intro hcontra
      have : x ∈ support f ∩ support g := ⟨hxf, hcontra⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty x)
    -- So g(x) = x
    have gx : g.toFun x = x := by
      exact not_mem_support_iff g x |>.mp hxg
    -- Since f moves x and supports are disjoint, f(x) ∉ support g
    have fx_notin : f.toFun x ∉ support g := by
      -- By symmetry with the previous case
      by_contra h_contra
      -- If f(x) ∈ support g, then x ∈ f⁻¹(support g)
      have : x ∈ f.toFun⁻¹' (support g) := h_contra
      -- But x ∈ support f, so x is in the intersection
      have : x ∈ support f ∩ f.toFun⁻¹' (support g) := ⟨hxf, this⟩
      -- Similar contradiction as before
      sorry -- Same issue as above
    -- So g(f(x)) = f(x)
    have gfx_eq : g.toFun (f.toFun x) = f.toFun x := by
      exact not_mem_support_iff g (f.toFun x) |>.mp fx_notin
    -- Now compute: (f * g) x = g (f x) = f x = f (g x) = (g * f) x
    show (f * g).toFun x = (g * f).toFun x
    -- We have gx : g.toFun x = x and gfx_eq : g.toFun (f.toFun x) = f.toFun x
    calc (f * g).toFun x = (f.trans g).toFun x := rfl
    _ = g.toFun (f.toFun x) := rfl
    _ = f.toFun x := gfx_eq
    _ = f.toFun (g.toFun x) := by rw [gx]
    _ = (g.trans f).toFun x := rfl
    _ = (g * f).toFun x := rfl

end Support

end OrdinalHomeo