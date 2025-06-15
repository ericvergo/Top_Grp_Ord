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

/-- The maximal rank points in X α 1 are infinite -/
lemma maximalRankPoints_infinite (α : Ordinal.{u}) : 
  (MaximalRankPoints α).Infinite := by
  -- X α 1 = ω^(α+1) · 1 + 1 = ω^(α+1) + 1
  -- Elements of the form ω^α · k for k ∈ ℕ\{0} have rank α+1
  -- There are infinitely many such elements
  -- This follows from the Cantor-Bendixson analysis of ordinals
  sorry  -- Requires CB rank computation for ordinals

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
  -- Strategy: A moiety can be decomposed as a disjoint union of clopen sets,
  -- each containing exactly one maximal rank point
  -- Since A contains infinitely many maximal rank points, we can enumerate them
  -- Let {aₙ} be the maximal rank points in A
  -- Define Uₙ = clopen neighborhood of aₙ in A containing no other maximal rank points
  -- Then A = ⋃ₙ Uₙ where each Uₙ ≃ ω^α + 1
  -- Therefore A ≃ ℕ × (ω^α + 1) ≃ ω^(α+1)
  sorry -- Requires: decomposition of moieties and ordinal arithmetic

/-- Two disjoint moieties can be swapped by an involution -/
theorem exists_involution_swapping_moieties {α : Ordinal.{u}} 
  (A B : TopologicalMoiety α) (h_disj : Disjoint (A : Set (X α 1)) (B : Set (X α 1))) :
  ∃ σ : X α 1 ≃ₜ X α 1, Function.Involutive σ ∧ σ '' A.carrier = B.carrier ∧ 
    ∀ x, x ∉ A.carrier ∪ B.carrier → σ x = x := by
  -- Since A and B are disjoint moieties, we can construct an involution that swaps them
  -- The idea: define σ to swap A and B pointwise, and fix everything else
  -- Since A and B are homeomorphic (both homeomorphic to ω^(α+1)), 
  -- we can find a homeomorphism between them
  -- First get homeomorphisms A ≃ₜ X α 1 ≃ₜ B
  obtain ⟨φ_A⟩ := moiety_homeomorphic_to_omega_power α A
  obtain ⟨φ_B⟩ := moiety_homeomorphic_to_omega_power α B
  -- Construct the involution by cases:
  -- - If x ∈ A, map it to the corresponding point in B
  -- - If x ∈ B, map it to the corresponding point in A  
  -- - Otherwise, fix x
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
theorem exists_convergent_translation {α : Ordinal.{u}} (_A : TopologicalMoiety α) :
  ∃ φ : X α 1 ≃ₜ X α 1, IsConvergentATranslation _A φ ∧ 
    ∃ B : TopologicalMoiety α, ∀ x, x ∈ support φ → x ∈ B := by
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
  -- We need to extend U to a larger clopen set that's a moiety
  -- The strategy: keep adding clopen neighborhoods until we get a moiety
  -- For now, we can try the simpler approach: if U already satisfies the moiety conditions, use it
  -- Otherwise, we need to ensure the complement also has infinitely many maximal rank points
  
  -- Check if Uᶜ also has infinitely many maximal rank points
  by_cases h_compl : (Uᶜ ∩ MaximalRankPoints α).Infinite
  · -- If yes, then U itself is a moiety
    use {
      carrier := U
      is_clopen := hU
      inf_maximal := h_inf
      inf_compl_maximal := h_compl
    }
    -- U ⊆ U is trivial
    exact subset_rfl
  · -- If not, we need to extend U
    -- The complement has only finitely many maximal rank points
    -- We need to shrink U to ensure its complement has infinitely many maximal rank points
    -- This requires a more sophisticated construction
    
    -- Key insight: The set of all maximal rank points is infinite (this should be proven elsewhere)
    -- So if Uᶜ has only finitely many, we can find another clopen set V disjoint from U
    -- with infinitely many maximal rank points, then U ∪ V works
    sorry

/-- Change of coordinates: any two moieties are related by a homeomorphism -/
theorem change_of_coordinates {α : Ordinal.{u}} (A B : TopologicalMoiety α) :
  ∃ σ : X α 1 ≃ₜ X α 1, σ '' A.carrier = B.carrier := by
  -- The key insight is that all moieties are homeomorphic to ω^(α+1)
  -- So we can compose homeomorphisms A ≃ₜ ω^(α+1) ≃ₜ B
  -- First, get homeomorphisms from each moiety to X α 1
  obtain ⟨φ_A⟩ := moiety_homeomorphic_to_omega_power α A
  obtain ⟨φ_B⟩ := moiety_homeomorphic_to_omega_power α B
  -- Now compose: A → X α 1 → B
  -- We need a homeomorphism from the whole space that maps A to B
  -- This requires extending the partial homeomorphisms
  sorry

/-- We can partition the maximal rank points into two infinite sets -/
lemma exists_partition_maximal_rank_points (α : Ordinal.{u}) :
  ∃ (S T : Set (X α 1)), S ∩ T = ∅ ∧ S ∪ T = MaximalRankPoints α ∧ S.Infinite ∧ T.Infinite := by
  -- Since MaximalRankPoints α is infinite, we can partition it into two infinite sets
  -- A standard way is to take even/odd indexed elements after some enumeration
  sorry -- Requires: partition of infinite sets

/-- There exists at least one topological moiety -/
lemma exists_moiety (α : Ordinal.{u}) : ∃ A : TopologicalMoiety α, True := by
  -- We construct a moiety by taking a clopen set containing half of the maximal rank points
  -- Use the partition from exists_partition_maximal_rank_points
  obtain ⟨S, T, h_disj, h_union, h_S_inf, h_T_inf⟩ := exists_partition_maximal_rank_points α
  -- For each point in S, take a clopen neighborhood disjoint from other maximal rank points
  -- The union of these neighborhoods forms a moiety
  sorry -- Requires: construction of clopen neighborhoods

end Moiety

section StableNeighborhoods

/-- A stable neighborhood is a clopen neighborhood of a point that is the unique
    highest rank element in that neighborhood -/
def IsStableNeighborhood {α : Ordinal.{u}} (U : Set (X α 1)) (b : X α 1) : Prop :=
  IsClopen U ∧ b ∈ U ∧ ∀ x ∈ U, x ≠ b → @rank.{u, u} (X α 1) _ x < @rank.{u, u} (X α 1) _ b

/-- Every element has arbitrarily small stable neighborhoods -/
theorem has_stable_neighborhood_basis {α : Ordinal.{u}} (b : X α 1) :
  (𝓝 b).HasBasis (IsStableNeighborhood · b) id := by
  -- We need to show that stable neighborhoods form a neighborhood basis
  -- This means: for any neighborhood U of b, there exists a stable neighborhood V ⊆ U
  refine Filter.hasBasis_iff.mpr ?_
  intro t
  constructor
  · -- If t ∈ 𝓝 b, then there exists a stable neighborhood V with b ∈ V ⊆ t
    intro ht
    -- Since X α 1 has the order topology and ordinals are well-ordered,
    -- we can find a basic open interval containing b
    -- In ordinal topology, basic opens are intervals which are clopen
    -- For any point b, we can find an interval [a, c) or (a, c] containing b
    -- where b is the maximum in this interval (making it stable)
    use t  -- For now, use t itself as the stable neighborhood
    constructor
    · -- Show that t is a stable neighborhood
      sorry
    · -- Show id t ⊆ t, which is just t ⊆ t
      exact subset_rfl
  · -- If there exists a stable neighborhood V ⊆ t, then t ∈ 𝓝 b
    intro ⟨V, hV_stable, hV_sub⟩
    -- hV_stable : IsStableNeighborhood V b
    obtain ⟨hV_clopen, hb_in_V, _⟩ := hV_stable
    -- Since V is open, b ∈ V, and V ⊆ t, we have t ∈ 𝓝 b
    exact mem_of_superset (mem_nhds_iff.mpr ⟨V, subset_rfl, hV_clopen.isOpen, hb_in_V⟩) hV_sub

/-- Stable neighborhoods of rank β+1 elements are homeomorphic to ω^β + 1 -/
theorem stable_neighborhood_homeomorphic {α β : Ordinal.{u}} {b : X α 1} 
  {U : Set (X α 1)} (hU : IsStableNeighborhood U b) (h_rank : @rank.{u, u} (X α 1) _ b = β + 1) :
  Nonempty (U ≃ₜ X β 1) := by
  -- A stable neighborhood U of b where b has rank β+1 consists of:
  -- - The point b itself (the unique point of rank β+1 in U)
  -- - Points of rank < β+1
  -- This structure is similar to X β 1 = ω^(β+1) which has:
  -- - Points of rank up to β+1
  -- The homeomorphism can be constructed by mapping the Cantor-Bendixson ranks appropriately
  sorry

end StableNeighborhoods

section Support

-- support_clopen is already defined in Basic.lean


/-- Alternative characterization of being outside the support -/
lemma not_mem_support_iff {α : Ordinal.{u}} {d : ℕ} (f : H α d) (x : X α d) :
  x ∉ support f ↔ f.toFun x = x := by
  -- From Basic.lean, we know that support is clopen, which means
  -- the moved set equals its closure, i.e., support f = {y | f.toFun y ≠ y}
  have h_clopen : IsClopen (support f) := support_clopen f
  -- The proof in Basic.lean shows that support equals the moved set
  -- because the moved set is clopen in ordinal topology
  have h_eq : support f = {y | f.toFun y ≠ y} := by
    -- From the proof of support_clopen, we know the moved set is clopen
    -- (though the full proof uses properties of ordinal topology)
    -- Since clopen sets equal their closure, we have:
    simp only [support]
    -- We need to show: closure {y | f.toFun y ≠ y} = {y | f.toFun y ≠ y}
    -- This follows from the fact that support is open (from h_clopen)
    -- and support = closure {y | f.toFun y ≠ y} by definition
    -- The only way the closure can be open is if the set was already closed
    apply IsClosed.closure_eq
    -- Need to show {y | f.toFun y ≠ y} is closed
    -- Since support is clopen and equals the closure of this set,
    -- and the closure is the smallest closed set containing it,
    -- the set must equal its closure, hence is closed
    have : IsOpen (support f) := h_clopen.isOpen
    have : support f = closure {y | f.toFun y ≠ y} := rfl
    -- If the closure is open, then the set must already be closed
    -- This is because ordinals have a basis of clopen sets
    -- For now, we use that the support is clopen, which is proven in Basic.lean
    -- The fact that support equals the moved set for ordinals requires
    -- deeper understanding of ordinal topology
    -- Since we established in Basic.lean that support is clopen,
    -- and support = closure {y | f.toFun y ≠ y} by definition,
    -- and clopen sets equal their closure, the moved set must equal the support
    -- This is a fundamental property of ordinal homeomorphisms
    -- For the full proof we would show the moved set is clopen directly
    -- but this follows from the proof of support_clopen in Basic.lean
    -- We know from Basic.lean that support is clopen
    -- For clopen sets, if the closure equals the set, then the set was already closed
    -- We need to establish that for ordinals, the moved set is clopen
    -- This follows from the fact proven in Basic.lean
    
    -- Actually, let's use a different approach
    -- Since support f is clopen (by h_clopen), it equals its closure
    -- So support f = closure {y | f.toFun y ≠ y} = {y | f.toFun y ≠ y}
    -- This means the moved set must be closed (and open)
    
    -- The moved set is clopen in ordinals because:
    -- 1. It's the complement of the fixed set (which is closed)
    -- 2. In ordinals with order topology, such sets are clopen
    
    -- We extract this from the proof of support_clopen
    -- The key is that in Basic.lean, we showed the moved set is clopen
    -- (though the full proof was left as sorry)
    -- For the purposes of this proof, we use that fact
    have h_moved_clopen : IsClopen {y | f.toFun y ≠ y} := by
      -- This is the key property of ordinal homeomorphisms
      -- proven (or asserted) in Basic.lean
      sorry -- This is the same sorry as in Basic.lean's support_clopen proof
    exact h_moved_clopen.isClosed
  -- Now the equivalence is straightforward
  rw [h_eq]
  simp only [mem_setOf_eq, not_not]

/-- If homeomorphisms have disjoint clopen supports, each preserves the other's support -/
lemma support_preserved_of_disjoint {α : Ordinal.{u}} (f g : H α 1)
  (h : support f ∩ support g = ∅) 
  (_hf_clopen : IsClopen (support f)) (_hg_clopen : IsClopen (support g)) :
  f.toFun '' (support g) ⊆ support g ∧ g.toFun '' (support f) ⊆ support f := by
  constructor
  · -- Show f.toFun '' (support g) ⊆ support g
    intro y hy
    -- y ∈ f.toFun '' (support g), so ∃ x ∈ support g, f.toFun x = y
    obtain ⟨x, hx_supp_g, rfl⟩ := hy
    -- We need to show f.toFun x ∈ support g
    -- By contradiction, suppose f.toFun x ∉ support g
    by_contra h_not_in
    -- Then g.toFun (f.toFun x) = f.toFun x
    have g_fix : g.toFun (f.toFun x) = f.toFun x := 
      (not_mem_support_iff g (f.toFun x)).mp h_not_in
    -- Since x ∈ support g, we have g.toFun x ≠ x
    have g_moves_x : g.toFun x ≠ x := by
      intro h_eq
      have : x ∉ support g := (not_mem_support_iff g x).mpr h_eq
      exact this hx_supp_g
    -- Also, x ∉ support f (by disjointness)
    have x_not_in_f : x ∉ support f := by
      intro h_in
      have : x ∈ support f ∩ support g := ⟨h_in, hx_supp_g⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty x)
    -- So f.toFun x = x
    have f_fix : f.toFun x = x := (not_mem_support_iff f x).mp x_not_in_f
    -- But then f.toFun x = x ∈ support g
    rw [f_fix] at h_not_in
    exact h_not_in hx_supp_g
  · -- Show g.toFun '' (support f) ⊆ support f (symmetric argument)
    intro y hy
    obtain ⟨x, hx_supp_f, rfl⟩ := hy
    by_contra h_not_in
    have f_fix : f.toFun (g.toFun x) = g.toFun x := 
      (not_mem_support_iff f (g.toFun x)).mp h_not_in
    have f_moves_x : f.toFun x ≠ x := by
      intro h_eq
      have : x ∉ support f := (not_mem_support_iff f x).mpr h_eq
      exact this hx_supp_f
    have x_not_in_g : x ∉ support g := by
      intro h_in
      have : x ∈ support f ∩ support g := ⟨hx_supp_f, h_in⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty x)
    have g_fix : g.toFun x = x := (not_mem_support_iff g x).mp x_not_in_g
    rw [g_fix] at h_not_in
    exact h_not_in hx_supp_f

/-- Key lemma: disjoint clopen supports are preserved by homeomorphisms -/
lemma disjoint_support_preserved {α : Ordinal.{u}} (f g : H α 1) 
  (h : support f ∩ support g = ∅) (_hg_clopen : IsClopen (support g)) :
  f.toFun '' (support g)ᶜ ⊆ (support g)ᶜ := by
  intro y hy
  -- y ∈ f.toFun '' (support g)ᶜ, so ∃ x ∉ support g with f.toFun x = y
  obtain ⟨x, hx_not_g, rfl⟩ := hy
  -- We need to show f.toFun x ∉ support g
  -- Consider two cases based on whether x ∈ support f
  by_cases hx_f : x ∈ support f
  · -- Case 1: x ∈ support f
    -- Since supports are disjoint and x ∈ support f, we have x ∉ support g (already known)
    -- We need to show f.toFun x ∉ support g
    -- Key insight: if f.toFun x ∈ support g, then since g moves points in its support,
    -- and f, g have disjoint supports, we get a contradiction
    -- This is a deep property that requires the full theory
    sorry
  · -- Case 2: x ∉ support f
    -- Then f.toFun x = x
    have f_fix : f.toFun x = x := (not_mem_support_iff f x).mp hx_f
    -- So f.toFun x = x ∉ support g
    rw [f_fix]
    exact hx_not_g

/-- Homeomorphisms with disjoint supports commute -/
lemma disjoint_support_commute {α : Ordinal.{u}} (f g : H α 1) 
  (h : support f ∩ support g = ∅) : f * g = g * f := by
  -- Two homeomorphisms are equal if they agree pointwise
  apply Homeomorph.ext
  intro x
  -- We need to show (f * g) x = (g * f) x
  -- In the group structure, (f * g) = f.trans g
  -- Let's directly compute what this means
  show (f * g).toFun x = (g * f).toFun x
  -- By definition of multiplication in Homeomorph
  show (f.trans g).toFun x = (g.trans f).toFun x
  -- By definition of trans
  show g.toFun (f.toFun x) = f.toFun (g.toFun x)
  -- Get the fact that supports are clopen
  have hf_clopen : IsClopen (support f) := support_clopen f
  have hg_clopen : IsClopen (support g) := support_clopen g
  -- Use the preservation lemma
  have hpres := support_preserved_of_disjoint f g h hf_clopen hg_clopen
  -- Case analysis on where x is
  by_cases hf : x ∈ support f
  · -- If x ∈ support f, then x ∉ support g (by disjointness)
    have hg : x ∉ support g := by
      intro h_in
      have : x ∈ support f ∩ support g := ⟨hf, h_in⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty x)
    -- Since x ∉ support g, we have g.toFun x = x
    have g_fix : g.toFun x = x := (not_mem_support_iff g x).mp hg
    -- So we need to show f.toFun (g.toFun x) = g.toFun (f.toFun x)
    -- which becomes f.toFun x = g.toFun (f.toFun x)
    rw [g_fix]
    -- Now we need to show f.toFun x = g.toFun (f.toFun x)
    -- Since x ∈ support f, f.toFun x might be anywhere
    -- But by hpres.2, g.toFun '' (support f) ⊆ support f
    -- Since x ∈ support f, if f.toFun x ∈ support g, then
    -- g.toFun (f.toFun x) ∈ g.toFun '' support g ⊆ support g by hpres.1
    -- This would contradict that supports are disjoint
    have : f.toFun x ∉ support g := by
      by_contra h_in_g
      -- f.toFun x ∈ support g and x ∈ support f
      -- We need to derive a contradiction
      -- The key insight: if f.toFun x ∈ support g, then since supports are preserved,
      -- we would have a cycle that contradicts disjointness
      -- Actually, we just need that f.toFun x ∉ support g because
      -- f maps support f to itself or outside both supports
      -- If f.toFun x ∈ support g, then g moves f.toFun x
      -- But f moves x, so x ≠ f.toFun x
      -- If g also moves f.toFun x, and supports are disjoint, we get a contradiction
      -- This is a key property that requires the full development of support theory
      sorry  -- Requires: disjoint supports imply no overlap in orbits
    -- So g fixes f.toFun x
    have g_fix' : g.toFun (f.toFun x) = f.toFun x := 
      (not_mem_support_iff g (f.toFun x)).mp this
    rw [g_fix']
  · -- If x ∉ support f
    -- Symmetric case
    by_cases hg : x ∈ support g
    · -- x ∈ support g, x ∉ support f
      have f_fix : f.toFun x = x := (not_mem_support_iff f x).mp hf
      rw [f_fix]
      have : g.toFun x ∉ support f := by
        by_contra h_in_f
        -- g.toFun x ∈ support f means f moves g.toFun x
        -- But x ∈ support g and supports are disjoint, so x ∉ support f
        -- This means f.toFun x = x (shown above in f_fix)
        -- We have a similar situation as before: disjoint supports should preserve orbits
        sorry  -- Same issue: requires orbit preservation under disjoint supports
      have f_fix' : f.toFun (g.toFun x) = g.toFun x := 
        (not_mem_support_iff f (g.toFun x)).mp this
      exact f_fix'.symm
    · -- x ∉ support f and x ∉ support g
      -- Both fix x
      have f_fix : f.toFun x = x := (not_mem_support_iff f x).mp hf
      have g_fix : g.toFun x = x := (not_mem_support_iff g x).mp hg
      -- Need to show g.toFun (f.toFun x) = f.toFun (g.toFun x)
      -- Since both fix x: f.toFun x = x and g.toFun x = x
      -- So g.toFun (f.toFun x) = g.toFun x = x
      -- and f.toFun (g.toFun x) = f.toFun x = x
      simp only [f_fix, g_fix]
  

end Support

end OrdinalHomeo