/-
Copyright (c) 2024 OrdinalAutoFormalization Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import OrdinalHomeo.Basic
import OrdinalHomeo.CantorBendixson

/-!
# Topological Moieties

This file defines topological moieties for ordinals of the form ω^(α+1) and proves their
key properties used in the proofs about homeomorphism groups.

## Main definitions

* `TopologicalMoiety`: A clopen subset of ω^(α+1) that contains infinitely many rank α+1 points
  and whose complement also contains infinitely many rank α+1 points
* `ATranslation`: A homeomorphism φ such that φⁿ(A) are pairwise disjoint for all n ∈ ℤ
* `ConvergentATranslation`: An A-translation where {φⁿ(A)} is locally finite

## Main results

* Every topological moiety is homeomorphic to ω^(α+1)
* For any two disjoint moieties, there exists an involution swapping them
* Every moiety admits a convergent translation

## References

* [Bhat et al., Algebraic and geometric properties of homeomorphism groups of ordinals]
-/

namespace OrdinalHomeo

open Ordinal Topology Set Filter Classical Homeomorph

universe u v

section Moiety


/-- The set of rank α+1 points in X α 1 = ω^(α+1) -/
def MaximalRankPoints (α : Ordinal.{u}) : Set (X α 1) :=
  {x | @rank.{u, u} (X α 1) _ x = α + 1}

/-- A topological moiety is a clopen set containing infinitely many maximal rank points
    with complement also containing infinitely many maximal rank points -/
structure TopologicalMoiety (α : Ordinal.{u}) where
  carrier : Set (X α 1)
  is_clopen : IsClopen carrier
  inf_maximal : (carrier ∩ MaximalRankPoints α).Infinite
  inf_compl_maximal : ((carrierᶜ) ∩ MaximalRankPoints α).Infinite

instance {α : Ordinal.{u}} : SetLike (TopologicalMoiety α) (X α 1) where
  coe := TopologicalMoiety.carrier
  coe_injective' := fun A B h => by
    cases A; cases B; congr

@[simp]
lemma mem_topologicalMoiety {α : Ordinal.{u}} (A : TopologicalMoiety α) (x : X α 1) :
  x ∈ A ↔ x ∈ A.carrier := Iff.rfl

/-- Every topological moiety is homeomorphic to ω^(α+1) -/
theorem moiety_homeomorphic_to_omega_power (α : Ordinal.{u}) (A : TopologicalMoiety α) :
  Nonempty ((A : Set (X α 1)) ≃ₜ X α 1) := by
  -- The proof follows from the fact that A contains infinitely many rank α+1 points
  -- and can be decomposed as a disjoint union of clopen neighborhoods of these points
  -- Each neighborhood is homeomorphic to ω^α + 1
  
  -- Extract the set of maximal rank points in A
  let maximal_in_A := A.carrier ∩ MaximalRankPoints α
  
  -- By inf_maximal, this set is infinite
  have h_inf : maximal_in_A.Infinite := A.inf_maximal
  
  -- Since A is a subset of a well-ordered set (ordinal), we can enumerate the maximal points
  -- in increasing order. Use the fact that any infinite subset of an ordinal has order type ω
  have : ∃ (enum : ℕ → X α 1), StrictMono enum ∧ range enum = maximal_in_A := by
    -- maximal_in_A is an infinite subset of X α 1, which is well-ordered
    -- Any infinite subset of a well-ordered set contains a copy of ω
    -- This gives us a strictly increasing enumeration
    -- The key fact: infinite subsets of ordinals can be order-isomorphic to ω
    sorry  -- Requires: theory of order types and well-ordered sets
  
  obtain ⟨enum, h_mono, h_range⟩ := this
  
  -- Define intervals: U₁ = [0, enum 1] ∩ A, Uₙ = [enum (n-1) + 1, enum n] ∩ A
  let U : ℕ → Set (X α 1) := fun n =>
    if n = 0 then ∅  -- dummy value, we start from n = 1
    else if n = 1 then {x ∈ A.carrier | x ≤ enum 1}
    else {x ∈ A.carrier | enum (n-1) < x ∧ x ≤ enum n}
  
  -- Show that A is the disjoint union of the Uₙ for n ≥ 1
  have h_union : A.carrier = ⋃ n ∈ Ici 1, U n := by
    sorry
  
  -- Show that the Uₙ are pairwise disjoint clopen sets
  have h_disj : Pairwise fun i j => Disjoint (U i) (U j) := by
    sorry
  
  have h_clopen : ∀ n ≥ 1, IsClopen (U n) := by
    sorry
  
  -- Each Uₙ is homeomorphic to ω^α + 1 by the classification theorem
  have h_homeo : ∀ n ≥ 1, Nonempty ((U n) ≃ₜ X α 1) := by
    intro n hn
    -- U n contains exactly one maximal rank point (enum n)
    -- and is a clopen subset, so by classification it's homeomorphic to a successor ordinal
    -- with CB rank α+1 and degree 1, which is ω^α + 1 ≃ X α 1
    sorry
  
  -- Therefore A ≃ ⨆ₙ Uₙ ≃ ℕ × (ω^α + 1) ≃ ω^(α+1)
  -- Use that a disjoint union of copies of X α 1 is homeomorphic to ℕ × (X α 1) ≃ X α 1
  sorry

/-- Two disjoint moieties can be swapped by an involution -/
theorem exists_involution_swapping_moieties {α : Ordinal.{u}} 
  (A B : TopologicalMoiety α) (h_disj : Disjoint (A : Set (X α 1)) (B : Set (X α 1))) :
  ∃ σ : X α 1 ≃ₜ X α 1, Function.Involutive σ ∧ σ '' A.carrier = B.carrier ∧ 
    ∀ x, x ∉ A.carrier ∪ B.carrier → σ x = x := by
  -- Use the homeomorphisms from each moiety to ω^(α+1) to construct the involution
  -- The involution swaps elements of A with elements of B and fixes everything else
  sorry

/-- An A-translation is a homeomorphism φ such that all iterates of A under φ are disjoint -/
def IsATranslation {α : Ordinal.{u}} (A : TopologicalMoiety α) (φ : X α 1 ≃ₜ X α 1) : Prop :=
  ∀ n m : ℤ, n ≠ m → 
    Disjoint ((if n ≥ 0 then (φ.toFun)^[n.toNat] else (φ.symm.toFun)^[(-n).toNat]) '' A.carrier) 
             ((if m ≥ 0 then (φ.toFun)^[m.toNat] else (φ.symm.toFun)^[(-m).toNat]) '' A.carrier)

/-- A convergent A-translation has locally finite orbit of A -/
def IsConvergentATranslation {α : Ordinal.{u}} (A : TopologicalMoiety α) (φ : X α 1 ≃ₜ X α 1) : Prop :=
  IsATranslation A φ ∧ LocallyFinite (fun n : ℤ => 
    (if n ≥ 0 then (φ.toFun)^[n.toNat] else (φ.symm.toFun)^[(-n).toNat]) '' A.carrier)

/-- Every topological moiety admits a convergent translation -/
theorem exists_convergent_translation {α : Ordinal.{u}} (A : TopologicalMoiety α) :
  ∃ φ : X α 1 ≃ₜ X α 1, IsConvergentATranslation A φ ∧ 
    ∃ B : TopologicalMoiety α, ∀ x, x ∈ support φ → x ∈ B := by
  -- The proof constructs φ by first establishing a homeomorphism between
  -- ω^(α+1) and ℤ × ℕ² × (ω^α + 1), then defining a shift on the ℤ component
  
  -- Step 1: Use that X α 1 ≃ ℕ × (X α 0) by Prop 3.13 in the paper
  -- Actually X α 1 = ω^(α+1) ≃ ℕ × (ω^α + 1)
  -- We can further decompose as ℤ × ℕ² × (ω^α + 1)
  
  -- For the construction, we use change of coordinates to assume A has a specific form
  -- Consider A' = {0} × {1} × ℕ × (ω^α + 1) in the space ℤ × ℕ² × (ω^α + 1)
  
  -- Define τ' on ℤ × ℕ² × (ω^α + 1) by:
  -- τ'(ℓ, 1, n, x) = (ℓ+1, 1, n, x)
  -- τ'(ℓ, m, n, x) = (ℓ, m, n, x) when m > 1
  
  -- This shifts the ℤ-coordinate only for elements with second coordinate 1
  -- The iterates τ'^n(A') are disjoint and locally finite
  
  -- Using the homeomorphism between X α 1 and ℤ × ℕ² × (ω^α + 1),
  -- we transport this construction back to get the desired φ
  
  sorry

/-- The complement of a topological moiety is also a topological moiety -/
theorem complement_is_moiety {α : Ordinal.{u}} (A : TopologicalMoiety α) :
  ∃ B : TopologicalMoiety α, (B : Set (X α 1)) = (A : Set (X α 1))ᶜ := by
  use {
    carrier := (A : Set (X α 1))ᶜ
    is_clopen := A.is_clopen.compl
    inf_maximal := A.inf_compl_maximal
    inf_compl_maximal := by
      simp only [compl_compl]
      exact A.inf_maximal
  }
  rfl

/-- Any clopen neighborhood of infinitely many maximal rank points extends to a moiety -/
theorem extend_to_moiety {α : Ordinal.{u}} (U : Set (X α 1)) (hU : IsClopen U)
  (h_inf : (U ∩ MaximalRankPoints α).Infinite) :
  ∃ A : TopologicalMoiety α, U ⊆ (A : Set (X α 1)) := by
  -- We can decompose X α 1 into clopen sets containing maximal rank points
  -- and arrange them so that both U and its complement get infinitely many
  sorry

/-- Change of coordinates: any two moieties are related by a homeomorphism -/
theorem change_of_coordinates {α : Ordinal.{u}} (A B : TopologicalMoiety α) :
  ∃ σ : X α 1 ≃ₜ X α 1, σ '' A.carrier = B.carrier := by
  -- Both A and B are homeomorphic to ω^(α+1), so we can compose these homeomorphisms
  obtain ⟨f⟩ := moiety_homeomorphic_to_omega_power α A
  obtain ⟨g⟩ := moiety_homeomorphic_to_omega_power α B
  
  -- f : A ≃ₜ X α 1 and g : B ≃ₜ X α 1
  -- We need a global homeomorphism σ : X α 1 ≃ₜ X α 1 with σ(A) = B
  
  -- The complement of a moiety is also a moiety
  have hAc : ∃ Ac : TopologicalMoiety α, (Ac : Set (X α 1)) = (A : Set (X α 1))ᶜ := complement_is_moiety A
  have hBc : ∃ Bc : TopologicalMoiety α, (Bc : Set (X α 1)) = (B : Set (X α 1))ᶜ := complement_is_moiety B
  
  obtain ⟨Ac, hAc_eq⟩ := hAc
  obtain ⟨Bc, hBc_eq⟩ := hBc
  
  -- Get homeomorphisms for the complements
  obtain ⟨fc⟩ := moiety_homeomorphic_to_omega_power α Ac
  obtain ⟨gc⟩ := moiety_homeomorphic_to_omega_power α Bc
  
  -- Now we can define σ by cases:
  -- On A, use f followed by g⁻¹
  -- On Aᶜ, use fc followed by gc⁻¹
  -- This works because A and Aᶜ partition X α 1
  
  -- First establish that f can be viewed as A → X α 1 and similarly for others
  -- Then compose to get the desired global homeomorphism
  sorry

end Moiety

section StableNeighborhoods

/-- A stable neighborhood is a clopen neighborhood of a point that is the unique
    highest rank element in that neighborhood -/
def IsStableNeighborhood {α : Ordinal.{u}} (U : Set (X α 1)) (b : X α 1) : Prop :=
  IsClopen U ∧ b ∈ U ∧ ∀ x ∈ U, x ≠ b → @rank.{u, u} (X α 1) _ x < @rank.{u, u} (X α 1) _ b

/-- Every element has arbitrarily small stable neighborhoods -/
theorem has_stable_neighborhood_basis {α : Ordinal.{u}} (b : X α 1) :
  (𝓝 b).HasBasis (IsStableNeighborhood · b) id := by
  -- Use the fact that ordinals have a basis of clopen neighborhoods
  -- and that rank is locally constant on small enough neighborhoods
  sorry

/-- Stable neighborhoods of rank β+1 elements are homeomorphic to ω^β + 1 -/
theorem stable_neighborhood_homeomorphic {α β : Ordinal.{u}} {b : X α 1} 
  {U : Set (X α 1)} (hU : IsStableNeighborhood U b) (h_rank : @rank.{u, u} (X α 1) _ b = β + 1) :
  Nonempty (U ≃ₜ X β 1) := by
  -- The proof uses the classification of successor ordinals by CB rank and degree
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
    -- We use that support is clopen (proven in Basic.lean)
    have supp_clopen : IsClopen (support f) := support_clopen f
    
    -- First show x ∉ support f
    have x_not_in_supp : x ∉ support f := by
      rw [support]
      intro h_contra
      -- If x ∈ closure {y | f.toFun y ≠ y}, but f.toFun x = x,
      -- then x would be in the closure but not in the set itself
      have x_not_moved : x ∉ {y | f.toFun y ≠ y} := by
        simp only [Set.mem_setOf_eq]
        exact not_ne_iff.mpr hfx
      -- Key insight: support is clopen, so if x ∈ support = closure(moved),
      -- but x ∉ moved, we need to use that the moved set itself is clopen
      
      -- Since support is clopen (by support_clopen), it equals the closure
      -- of moved points only if the moved points form a clopen set
      -- For ordinals, the moved points of a homeomorphism form a clopen set
      
      -- Actually, let's use a different approach:
      -- If x is fixed by f, then there's a neighborhood of x where all points
      -- are either fixed or their image is far from x
      
      -- Since f.toFun x = x and f is continuous, for any neighborhood V of x,
      -- f⁻¹(V) is a neighborhood of x
      -- In particular, if we take V small enough, f acts locally near x
      
      -- For ordinals with order topology, we can use the basis of clopen intervals
      -- Since x is fixed and support is clopen, if x were in support,
      -- then x would be in the interior of support (as support is open)
      -- But x ∉ {y | f.toFun y ≠ y}, so x is isolated from moved points
      
      -- This requires the fact that for homeomorphisms of ordinals,
      -- the set of moved points is clopen, which we haven't established
      sorry  -- Requires: moved points form clopen set for ordinal homeomorphisms
    
    -- Now use that (support f)ᶜ is open and contains x
    use (support f)ᶜ
    use supp_clopen.compl.isOpen
    use x_not_in_supp
    -- Show (support f)ᶜ ∩ {y | f.toFun y ≠ y} = ∅
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨hy_not_supp, hy_moved⟩
    -- y ∉ support f but f moves y, contradiction
    have : y ∈ support f := by
      apply subset_closure
      exact hy_moved
    exact hy_not_supp this

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