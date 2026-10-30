/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSetTheory.BasicSet
public import CharacteristicSetTheory.PseudoDivision
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Characteristic Set Method (Wu's Method)

This file implements the core algorithms of Wu's Method for solving systems of algebraic equations.

## Main Concepts

1. **Characteristic Set (CS)**: A special triangular set contained in a polynomial set `PS`
  that generates the same ideal up to saturation by initials.
2. **Zero Decomposition**:
  The process of decomposing the zero set of `PS` into the union of zero sets of triangular sets.
  `Zero(PS) = ⋃ Zero(CSᵢ/IPᵢ)` where `CSᵢ` are triangular sets and `IPᵢ` are products of initials.

## Main Algorithms

* `MvPolynomial.List.characteristicSet`: Computes a characteristic set of a list of polynomials.
* `MvPolynomial.List.zeroDecomposition`:
  Decomposes the zero set of a polynomial system into a finite set of triangular systems.

## Main Theorems

* Well-Ordering Principles:
  - `vanishingSet_diff_initialProd_subset`: `Zero(CS/IP) ⊆ Zero(PS)`
  - `vanishingSet_diff_initialProd_eq`: `Zero(CS/IP) = Zero(PS/IP)`
  - `vanishingSet_decomposition`: `Zero(PS) = Zero(CS/IP) ∪ ⋃_{CS} Zero(PS ∪ {init(p)})`
* `characteristicSet_isCharacteristicSet`: The algorithm computes a valid characteristic set
* `vanishingSet_eq_zeroDecomposition_union`: Zero Decomposition Theorem.
  The variety of the input system is exactly the union of the "quasi-varieties"
  defined by the computed triangular sets.

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]
* [Wen-Tsun Wu, *Mathematics Mechanization*][wen2000mathematics]

-/

@[expose] public section

open MvPolynomial TriangularSet

variable {R σ : Type*}

namespace MvPolynomial

/-! ### Vanishing Sets -/

section VanishingSet

variable [CommSemiring R] {α : Type*} [Membership (MvPolynomial σ R) α]
variable (K : Type*) [CommSemiring K] [Algebra R K] (p : MvPolynomial σ R) (a : α)

/-- The set of points in `K ^ σ` where all polynomials in `a` vanish.
It is the same as `zeroLocus K (Ideal.span a)` for `a : Set (MvPolynomial σ R)` -/
def vanishingSet : Set (σ → K) := {x | ∀ p ∈ a, p.aeval x = 0}

/-- The set of points where a single polynomial `p` vanishes. -/
def vanishingSet' : Set (σ → K) := {x | aeval x p = 0}

theorem vanishingSet_singleton_eq_singleVanishingSet :
    vanishingSet K ({p} : Set (MvPolynomial σ R)) = vanishingSet' K p := by
  simp only [vanishingSet, Set.mem_singleton_iff, forall_eq, vanishingSet']

end VanishingSet

variable [Field R] (K : Type*) [Field K] [Algebra R K] (PS : Set (MvPolynomial σ R))

theorem vanishingSet_eq_zeroLocus_span : vanishingSet K PS = zeroLocus K (Ideal.span PS) :=
  (zeroLocus_span PS).symm

theorem vanishingSet_eq_zeroLocus_span' {α : Type*} [Membership (MvPolynomial σ R) α] (a : α) :
    vanishingSet K a = zeroLocus K (Ideal.span {p | p ∈ a}) :=
  vanishingSet_eq_zeroLocus_span K {p | p ∈ a}

end MvPolynomial

variable [Field R] [DecidableEq R] [LinearOrder σ] {α : Type*}
variable [Membership (MvPolynomial σ R) α] (K : Type*)

/-! ### Characteristic Set Properties -/

/-- A Triangular Set `CS` is a Characteristic Set for `a` if:
1. Every element in `a` reduce to 0 modulo `CS`.
2. `Zero(a) ⊆ Zero(CS)` (geometric containment). -/
def TriangularSet.IsCharacteristicSet [CommSemiring K] [Algebra R K]
    (CS : TriangularSet σ R) (a : α) : Prop :=
  (∀ g ∈ a, (0 : MvPolynomial σ R).IsSetRemainder g CS) ∧ vanishingSet K a ⊆ vanishingSet K CS

namespace CharacteristicSet

variable [Field K] [Algebra R K] {PS : α} {CS : TriangularSet σ R}

/-- Well-Ordering Principle (1): `Zero(CS/IP) ⊆ Zero(PS)`.
If all polynomials in `PS` reduce to 0 modulo `CS`, then any zero of `CS`
that isn't a zero of `IP` must be a zero of `PS`. -/
theorem vanishingSet_diff_initialProd_subset
    (h : (∀ g ∈ PS, (0 : MvPolynomial σ R).IsSetRemainder g CS)) :
    vanishingSet K CS \ vanishingSet' K (initialProd CS.toFinset) ⊆
      vanishingSet K PS := by
  refine Set.sdiff_subset_iff.mpr (fun x hx ↦ ?_)
  simp only [vanishingSet, vanishingSet', Set.mem_ofPred_eq, Set.mem_union] at *
  simp only [or_iff_not_imp_right, not_forall, forall_exists_index, initialProd]
  intro p hp1 hp2
  rcases (h p hp1).2 with ⟨es, qs, h1, h2⟩
  rw [add_zero] at h2
  -- If x is a zero of CS but not of initials, and rem(p, CS) = 0, then p(x) must be 0.
  have : ∃ i : Fin es.length, (aeval x) (CS i).initial = 0 ∧ ¬es[i] = 0 := by
    have := congr_arg (aeval x) h2
    simpa [(forall_mem_iff_forall_index' h1.2).mp hx, hp2, Finset.prod_eq_zero_iff] using this
  rcases this with ⟨⟨i, hi1⟩, (hi2 : (aeval x) (CS i).initial = 0), _⟩
  rw [map_prod, Finset.prod_eq_zero_iff]
  exact ⟨CS i, mem_toFinset_iff.mpr <| apply_mem <| h1.1 ▸ hi1, hi2⟩

/-- Well-Ordering Principle (2): `Zero(CS/IP) = Zero(PS/IP)`. -/
theorem vanishingSet_diff_initialProd_eq (h : CS.IsCharacteristicSet K PS) :
    vanishingSet K CS \ vanishingSet' K (initialProd CS.toFinset) =
      vanishingSet K PS \ vanishingSet' K (initialProd CS.toFinset) := by
  refine Set.Subset.antisymm ?_ (Set.sdiff_subset_sdiff_left h.2)
  refine Set.subset_sdiff.mpr ⟨?_ ,Set.disjoint_sdiff_left⟩
  exact vanishingSet_diff_initialProd_subset K h.1

/-- Well-Ordering Principle (3): `Zero(PS) = Zero(CS/IP) ∪ ⋃_{CS} Zero(PS ∪ {init(p)})` -/
theorem vanishingSet_decomposition (h : CS.IsCharacteristicSet K PS) : vanishingSet K PS =
      vanishingSet K CS \ vanishingSet' K (initialProd CS.toFinset) ∪
      ⋃ p ∈ CS, vanishingSet K PS ∩ vanishingSet' K p.initial := by
  have : (⋃ p ∈ CS, vanishingSet K PS ∩ vanishingSet' K p.initial) =
      vanishingSet K PS ∩ vanishingSet' K (initialProd CS.toFinset) := Set.ext fun x ↦ by
    simp [vanishingSet, vanishingSet', initialProd, Finset.prod_eq_zero_iff]
  rw [vanishingSet_diff_initialProd_eq K h, this]
  exact (Set.sdiff_union_inter _ _).symm

end CharacteristicSet

namespace MvPolynomial

namespace List

variable (B : BasicSetSpec σ R)

/-! ### Characteristic Set Algorithm -/

-- A helper lemma: adding pseudo-remainders strictly decreases the order.
lemma characteristicSetGo_decreasing (l₀ l : List (MvPolynomial σ R))
    (BS : TriangularSet σ R) (lBS RS : List (MvPolynomial σ R))
    (hRS : RS ≠ []) (hBS : BS = B.basicSet l) (hlBS : lBS = BS.toList)
    (hRS1 : RS = ((l \ lBS).map fun p ↦ (p.setPseudo BS).remainder).filter (· ≠ 0)) :
    B.basicSet (l₀ ++ RS ++ lBS) < B.basicSet l := by
  rw [hRS1, hlBS, hBS] at hRS ⊢
  apply B.basicSet_append_toList_lt
  have ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hRS
  refine ⟨p, List.mem_append_right _ hp, of_decide_eq_true (List.mem_filter.mp hp).2, ?_⟩
  have ⟨q, _, hq2⟩ := List.mem_map.mp (List.mem_filter.mp hp).1
  exact hq2 ▸ q.setPseudo_remainder_reducedToSet _

-- Keep the nonrecursive remainder map unchanged in the generated induction principle.
set_option wf.preprocess false in
/-- The recursive algorithm for computing the Characteristic Set -/
noncomputable def characteristicSet.go [Finite σ]
    (l₀ l : List (MvPolynomial σ R)) : TriangularSet σ R :=
  let BS := B.basicSet l
  let lBS := BS.toList
  let RS : List _ := ((l \ lBS).map fun p ↦ (p.setPseudo BS).remainder).filter (· ≠ 0)
  if _h : RS = [] then BS
  else go l₀ (l₀ ++ RS ++ lBS)
  termination_by B.basicSet l
  decreasing_by
    exact characteristicSetGo_decreasing B l₀ l _ _ _ (by assumption) rfl rfl rfl

/--
Computes the Characteristic Set of a polynomial list `l`.
Algorithm:
1. Let `l₀ = l`.
2. Compute `BS = BasicSet(l)`.
3. Compute remainders `RS` of `l \ BS` with respect to `BS`.
4. If `RS` is empty, `BS` is the characteristic set.
5. If not, set `l = l₀ ++ RS ++ BS` and go to step 2.
Termination is guaranteed by the well-ordering of orders.
-/
noncomputable def characteristicSet [Finite σ] (l : List (MvPolynomial σ R)) : TriangularSet σ R :=
  characteristicSet.go B l l

variable [Finite σ] (l₀ l : List (MvPolynomial σ R))

lemma zero_isSetRemainder_characteristicSetGo : l₀ ⊆ l → ∀ p ∈ l₀,
    (0 : MvPolynomial σ R).IsSetRemainder p (characteristicSet.go B l₀ l) := by
  induction l using characteristicSet.go.induct B l₀ with
  | case1 l BS lBS RS h =>
    intro hl p hp1
    rw [characteristicSet.go, dite_eq_left h]
    apply isSetRemainder_of_eq_setPseudo_remainder
    rcases em (p ∈ lBS) with hp2 | hp2
    · exact setPseudo_remainder_eq_zero_of_mem BS (mem_toList_iff.mp hp2)
    have h : ∀ a ∈ l \ lBS, (a.setPseudo BS).remainder = 0 := by simpa [RS] using h
    exact (h p <| List.mem_diff_of_mem (hl hp1) hp2)
  | case2 l BS lBS RS h ih =>
    intro hl
    rw [characteristicSet.go, dite_eq_right h]
    exact ih (List.subset_append_of_subset_left lBS (List.subset_append_left _ _))

variable (K : Type*) [CommSemiring K] [Algebra R K] (l₀ l : List (MvPolynomial σ R))

lemma characteristicSetGo_vanishingSet_subset : vanishingSet K l₀ = vanishingSet K l →
    vanishingSet K l₀ ⊆ vanishingSet K (characteristicSet.go B l₀ l) := by
  simp only [vanishingSet, Set.ofPred_subset_ofPred]
  induction l using characteristicSet.go.induct B l₀ with
  | case1 l BS lBS RS h =>
    intro hl x hx p hp
    rw [characteristicSet.go, dite_eq_left h] at hp
    have hx : ∀ p ∈ l, aeval x p = 0 := (Set.ext_iff.mp hl x).mp hx
    exact hx p <| B.basicSet_subset l hp
  | case2 l BS lBS RS h ih =>
    intro hl
    rw [characteristicSet.go, dite_eq_right h]
    refine ih (Set.ext fun x ↦ ?_)
    simp only [Set.mem_ofPred_eq, List.append_assoc, List.mem_append]
    have hl := Set.mem_ofPred_eq ▸ Set.mem_ofPred_eq ▸ (Set.ext_iff.mp hl x)
    refine ⟨fun hx p hp ↦ ?_, fun hx p hp ↦ hx _ (Or.inl hp)⟩
    refine Or.elim hp (hx _) fun hp ↦ ?_
    have hBS : ∀ ⦃q⦄, q ∈ BS → aeval x q = 0 := fun q hq ↦ (hl.mp hx) q <| B.basicSet_subset l hq
    refine Or.elim hp (fun hp ↦ ?_) (fun hp ↦ hBS <| mem_toList_iff.mp hp)
    have ⟨⟨g, hg1, hg2⟩, hp⟩ : (∃ a ∈ l \ lBS, (a.setPseudo BS).remainder = p) ∧ ¬p = 0 :=
        by simpa [RS] using hp
    suffices heq : ∑ i : Fin (g.setPseudo BS).quotients.length,
        (aeval x) (g.setPseudo BS).quotients[i.1] * (aeval x) (BS i) = 0 by
      have := Eq.symm <| congrArg (aeval x) (hg2 ▸ g.setPseudo_equation BS)
      have hg2 : aeval x g = 0 := (hl.mp hx) _ <| (List.diff_subset _ _) hg1
      simpa [hg2, heq] using this
    refine Finset.sum_eq_zero fun ⟨i, hi⟩ _ ↦ ?_
    simp only [hBS (apply_mem <| g.length_setPseudo_quotients BS ▸ hi), mul_zero]

/-- The computed `characteristicSet` satisfies the required properties. -/
theorem characteristicSet_isCharacteristicSet :
    (l.characteristicSet B).IsCharacteristicSet K l where
  left := zero_isSetRemainder_characteristicSetGo B l l fun _ ↦ id
  right := characteristicSetGo_vanishingSet_subset B K l l rfl

lemma characteristicSetGo_le_basicSet : characteristicSet.go B l₀ l ≤ B.basicSet l := by
  induction l using characteristicSet.go.induct B l₀ with
  | case1 l BS lBS RS h => rw [characteristicSet.go, dite_eq_left h]
  | case2 l BS lBS RS h ih =>
    rw [characteristicSet.go, dite_eq_right h]
    refine le_trans ih (le_of_lt ?_)
    exact characteristicSetGo_decreasing B l₀ l _ _ _ h rfl rfl rfl

theorem characteristicSet_le_basicSet : l.characteristicSet B ≤ B.basicSet l :=
  characteristicSetGo_le_basicSet B l l

/-- The algorithm returns a basic set of one of its intermediate lists. -/
lemma characteristicSetGo_eq_basicSet :
    ∃ s, characteristicSet.go B l₀ l = B.basicSet s := by
  induction l using characteristicSet.go.induct B l₀ with
  | case1 l BS lBS RS h =>
    rw [characteristicSet.go, dite_eq_left h]
    exact ⟨l, rfl⟩
  | case2 l BS lBS RS h ih =>
    rw [characteristicSet.go, dite_eq_right h]
    exact ih

theorem characteristicSet_eq_basicSet :
    ∃ s, l.characteristicSet B = B.basicSet s :=
  characteristicSetGo_eq_basicSet B l l

theorem characteristicSet_toList_equiv :
    B.basicSet (l.characteristicSet B).toList ≈ l.characteristicSet B := by
  obtain ⟨s, hs⟩ := characteristicSet_eq_basicSet B l
  rw [hs]
  exact B.basicSet_toList_equiv s

theorem characteristicSet_toList_le :
    B.basicSet (l.characteristicSet B).toList ≤ l.characteristicSet B := by
  obtain ⟨s, hs⟩ := characteristicSet_eq_basicSet B l
  rw [hs]
  exact B.basicSet_toList_le s

theorem characteristicSet_initial_reduced (p : MvPolynomial σ R)
    (hp : p ∈ l.characteristicSet B) (hmax : p.vars.max ≠ ⊥) :
    p.initial.reducedToSet (l.characteristicSet B) := by
  obtain ⟨s, hs⟩ := characteristicSet_eq_basicSet B l
  rw [hs] at hp ⊢
  exact B.initial_reduced s p hp hmax

protected alias cs := characteristicSet
protected alias cs_isCharacteristicSet := characteristicSet_isCharacteristicSet
protected alias cs_le_basicSet := characteristicSet_le_basicSet
protected alias cs_eq_basicSet := characteristicSet_eq_basicSet
protected alias cs_toList_equiv := characteristicSet_toList_equiv
protected alias cs_toList_le := characteristicSet_toList_le
protected alias cs_initial_reduced := characteristicSet_initial_reduced

/-! ### Zero Decomposition -/

/--
Decomposes the zero set of `l` into a union of zero sets of triangular sets.
The algorithm recursively computes the characteristic set `CS`
and adds branches for the initials of `CS`.
-/
noncomputable def zeroDecomposition (l : List (MvPolynomial σ R)) : List (TriangularSet σ R) :=
  let CS := l.characteristicSet B
  -- Recurse on: Initial(p) added to the system
  let subDecomp := (CS.toList.filter fun p ↦ p.vars.max ≠ ⊥).attach.map
    fun ⟨p, _⟩ ↦ zeroDecomposition (p.initial :: CS.toList ++ l)
  CS :: subDecomp.flatten
  termination_by B.basicSet l
  decreasing_by
    -- Proof that order(p.initial :: CS ++ l) < order(l)
    change B.basicSet ([p.initial] ++ CS.toList ++ l) < B.basicSet l
    -- 1. Adding elements can only decrease order
    apply lt_of_le_of_lt (B.basicSet_ge_of_subset <| List.subset_append_left _ l)
    -- 2. Order(CS) ≤ Order(l)
    apply lt_of_lt_of_le ?_
      (le_trans (l.cs_toList_le B) (l.cs_le_basicSet B))
    -- 3. Adding an initial strictly decreases order.
    have hp : p ∈ CS ∧ ¬p.vars.max = ⊥ := by expose_names; simpa using property
    exact B.basicSet_cons_lt (initial_ne_zero (ne_zero_of_mem hp.1))
      (B.reducedToSet_basicSet (l.cs_initial_reduced B p hp.1 hp.2))

theorem eq_basicSet_of_mem_zeroDecomposition :
    ∀ CS ∈ l.zeroDecomposition B, ∃ s, CS = B.basicSet s := by
  induction l using zeroDecomposition.induct B with | case1 l CS ih =>
  intro CS' hCS'
  have hCS' : CS' = CS ∨ ∃ p, (p ∈ CS ∧ ¬p.vars.max = ⊥) ∧
      CS' ∈ (p.initial :: CS.toList ++ l).zeroDecomposition B := by
    unfold zeroDecomposition at hCS'; simpa using hCS'
  rcases hCS' with hCS' | ⟨p, ⟨hp1, hp2⟩, hp3⟩
  · exact hCS' ▸ l.cs_eq_basicSet B
  exact ih p (List.mem_filter_of_mem (mem_toList_iff.mpr hp1) (decide_eq_true hp2)) _ hp3

theorem zero_isSetRemainder_of_mem_zeroDecomposition :
    ∀ CS ∈ l.zeroDecomposition B, ∀ g ∈ l, (0 : MvPolynomial σ R).IsSetRemainder g CS := by
  induction l using zeroDecomposition.induct B with | case1 l CS ih =>
  intro CS' hCS'
  have hCS' : CS' = CS ∨ ∃ p, (p ∈ CS ∧ ¬p.vars.max = ⊥) ∧
      CS' ∈ (p.initial :: CS.toList ++ l).zeroDecomposition B := by
    unfold zeroDecomposition at hCS'; simpa using hCS'
  rcases hCS' with hCS' | ⟨p, ⟨hp1, hp2⟩, hp3⟩
  · exact hCS' ▸ zero_isSetRemainder_characteristicSetGo B l l fun _ ↦ id
  have := ih p (List.mem_filter_of_mem (mem_toList_iff.mpr hp1) (decide_eq_true hp2)) _ hp3
  intro g hg
  exact this g <| List.mem_cons.mpr <| Or.inr <| List.mem_append.mpr (Or.inr hg)

variable (K : Type*) [Field K] [Algebra R K] (l₀ l : List (MvPolynomial σ R))

/-- **Zero Decomposition Theorem**:
The vanishing set of `l` is the union of the vanishing sets of the triangular sets
in `zeroDecomposition`, excluding the zeros of their initials.
`Zero(l) = ⋃_{CS ∈ ZD(l)} Zero(CS/IP(CS))`.
-/
theorem vanishingSet_eq_zeroDecomposition_union :
    vanishingSet K l = ⋃ CS ∈ l.zeroDecomposition B,
      vanishingSet K CS \ vanishingSet' K (initialProd CS.toFinset) := by
  induction l using zeroDecomposition.induct B with | case1 l CS ih =>
  -- 1. Unfold recursion
  suffices vanishingSet K l = vanishingSet K CS \ vanishingSet' K (initialProd CS.toFinset) ∪
      ⋃ p ∈ CS.toList.filter fun p ↦ p.vars.max ≠ ⊥,
        ⋃ CS' ∈ (p.initial :: CS.toList ++ l).zeroDecomposition B,
          vanishingSet K CS' \ vanishingSet' K (initialProd CS'.toFinset) by
    rw [zeroDecomposition]; simpa using this
  have is_cs : IsCharacteristicSet K (characteristicSet B l) l := l.cs_isCharacteristicSet B K
  -- 2. Apply decomposition theorem to the recursive structure
  suffices ⋃ p ∈ CS, vanishingSet K l ∩ vanishingSet' K p.initial =
      ⋃ p ∈ CS.toList.filter fun p ↦ p.vars.max ≠ ⊥,
        vanishingSet K (p.initial :: CS.toList ++ l) by
    rw [CharacteristicSet.vanishingSet_decomposition K is_cs, ← Set.iUnion₂_congr ih, this]
  -- 3. Prove equality of the union components (ignoring constants)
  ext x
  suffices (x ∈ vanishingSet K l ∧ ∃ p ∈ CS, x ∈ vanishingSet' K p.initial) ↔
      ∃ p, (p ∈ CS ∧ ¬p.vars.max = ⊥) ∧ x ∈ vanishingSet K (p.initial :: (CS.toList ++ l)) by
    simpa using this
  simp only [vanishingSet, Set.mem_ofPred_eq, vanishingSet', List.mem_cons, List.mem_append,
    mem_toList_iff, forall_eq_or_imp]
  -- 4. Bidirectional implication
  refine ⟨fun ⟨hx, p, hp1, hp2⟩ ↦ ⟨p, ⟨hp1, ?_⟩, hp2, fun q hq ↦ ?_⟩,
    fun ⟨p, ⟨hp1, _⟩, hx1, hx2⟩ ↦ ⟨fun q hq ↦ hx2 q (Or.inr hq), p, hp1, hx1⟩⟩
  · -- Forward: if p is constant, Zero(p) is empty or total, but here p != 0 (from CS)
    contrapose! hp2
    simp [initial_of_max_vars_eq_bot (ne_zero_of_mem hp1) hp2]
  · -- Forward: x is zero of everything in CS++l
    rcases hq with hq | hq
    · -- x ∈ Zero(CS) because x ∈ Zero(l) and CS is characteristic
      have := is_cs.2
      simp only [vanishingSet, Set.ofPred_subset_ofPred] at this
      exact this x hx q hq
    -- x ∈ Zero(l)
    exact hx q hq

end List

end MvPolynomial
