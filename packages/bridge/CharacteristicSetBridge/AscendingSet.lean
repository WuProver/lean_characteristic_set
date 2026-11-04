/-
Copyright (c) 2026 The CharacteristicSet Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CharacteristicSet Authors
-/
module

public import CharacteristicSet.Computable.AscendingSet
public import CharacteristicSetBridge.Initial
public import CharacteristicSetBridge.Rank
public import CharacteristicSetBridge.Reduced
public import CharacteristicSetBridge.TriangularSet
public import CharacteristicSetTheory.AscendingSet

/-! Correctness of executable ascending-set checks and basic-set candidate preparation. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory

open scoped HexMvPolyTheory

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

private theorem basicSet_rankLE_eq (p q : MvPoly n R cmp) :
    (!(Computable.compareRank p q == .gt)) = decide (toMvPolynomial p ≤ toMvPolynomial q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
  change ¬ (Computable.compareRank p q = .gt) ↔ _
  rw [Bridge.compareRank_gt_iff, ← MvPolynomial.lt_def', MvPolynomial.not_lt_iff_ge]

private theorem basicSet_sort_map (ps : List (MvPoly n R cmp)) :
    (ps.mergeSort (fun p q => !(Computable.compareRank p q == .gt))).map toMvPolynomial =
      (ps.map toMvPolynomial).mergeSort (fun p q => decide (p ≤ q)) := by
  apply List.map_mergeSort
  intro p hp q hq
  exact basicSet_rankLE_eq p q

private theorem basicSet_zero_iff (p : MvPoly n R cmp) :
    p.termsList.isEmpty = true ↔ toMvPolynomial p = 0 := by
  rw [List.isEmpty_iff]
  constructor
  · intro h
    have hp : p = 0 := MvPoly.termsList_inj h
    simp [hp]
  · intro h
    have hp : p = 0 := toMvPolynomial_injective (by simpa using h)
    subst p
    rfl

/-- Sorting and zero removal agree as complete ordered candidate lists. -/
theorem basicSetCandidates_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.basicSetCandidates ps).map toMvPolynomial =
      ((ps.map toMvPolynomial).mergeSort (fun p q => decide (p ≤ q))).filter
        (fun p => decide (p ≠ 0)) := by
  unfold Computable.basicSetCandidates
  rw [← basicSet_sort_map]
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p hp
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_true_eq, Function.comp_apply]
  exact (Bool.eq_false_iff).trans (not_congr (basicSet_zero_iff p))

/-- The executable encoding orders absent variables below present variables. -/
theorem mainVar_lt_iff (p q : MvPoly n R cmp) :
    Computable.variableIndex (Computable.mainVar p) <
      Computable.variableIndex (Computable.mainVar q) ↔
    (toMvPolynomial p).vars.max < (toMvPolynomial q).vars.max := by
  rw [← mainVar_toMvPolynomial, ← mainVar_toMvPolynomial]
  cases Computable.mainVar p with
  | none =>
    cases Computable.mainVar q with
    | none => change 0 < 0 ↔ (⊥ : WithBot (Fin n)) < ⊥; simp
    | some j => change 0 < j.val + 1 ↔ (⊥ : WithBot (Fin n)) < j; simp
  | some i =>
    cases Computable.mainVar q with
    | none => change i.val + 1 < 0 ↔ (i : WithBot (Fin n)) < ⊥; simp
    | some j => change i.val + 1 < j.val + 1 ↔ (i : WithBot (Fin n)) < j; simp

theorem isTriangularSet_iff (ps : List (MvPoly n R cmp)) :
    Computable.isTriangularSet ps = true ↔
    ∃ S : TriangularSet (Fin n) R, ps.map toMvPolynomial = S.toList := by
  have hc : Computable.isTriangularSet ps = true ↔
      (∀ p ∈ ps.map toMvPolynomial, p ≠ 0) ∧
      (ps.map toMvPolynomial).Pairwise (fun p q => p.vars.max < q.vars.max) := by
    simp only [Computable.isTriangularSet, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', Bool.eq_false_iff, decide_eq_true_eq,
      List.pairwise_map, mainVar_lt_iff, List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    simp only [ne_eq, basicSet_zero_iff]
  rw [hc]
  constructor
  · rintro ⟨hn, ho⟩
    exact ⟨⟨ps.map toMvPolynomial, fun h => hn 0 h rfl,
      List.isChain_iff_pairwise.mpr ho⟩, rfl⟩
  · rintro ⟨S, h⟩
    rw [h]
    exact ⟨fun _ hp => S.toList_non_zero hp, S.toList_pairwise⟩

private theorem pairwise_reduced_iff (S : TriangularSet (Fin n) R) :
    S.toList.Pairwise (fun p q => q.reducedTo p) ↔ S.IsAscendingSet := by
  simp only [List.pairwise_iff_getElem, TriangularSet.IsAscendingSet]
  constructor
  · intro h i j hij hj
    exact (S.toList_getElem hj ▸ S.toList_getElem (lt_trans hij hj) ▸
      h i j (lt_trans hij hj) hj hij)
  · intro h i j hi hj hij
    rw [S.toList_getElem hi, S.toList_getElem hj]
    exact h hij hj

private theorem pairwise_initial_reduced_iff (S : TriangularSet (Fin n) R) :
    S.toList.Pairwise (fun p q => q.initial.reducedTo p) ↔ S.IsWeakAscendingSet := by
  simp only [List.pairwise_iff_getElem, TriangularSet.IsWeakAscendingSet]
  constructor
  · intro h i j hij hj
    exact (S.toList_getElem hj ▸ S.toList_getElem (lt_trans hij hj) ▸
      h i j (lt_trans hij hj) hj hij)
  · intro h i j hi hj hij
    rw [S.toList_getElem hi, S.toList_getElem hj]
    exact h hij hj

namespace Standard

theorem isAscendingSet_iff_of_toList (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    Computable.Standard.isAscendingSet ps = true ↔ S.IsAscendingSet := by
  have ht := isTriangularSet_iff ps |>.mpr ⟨S, hps⟩
  rw [Computable.Standard.isAscendingSet, Bool.and_eq_true, ht, eq_self, true_and,
    decide_eq_true_eq]
  rw [← pairwise_reduced_iff, ← hps, List.pairwise_map]
  simp only [reducedTo_iff]

end Standard

namespace Weak

theorem isAscendingSet_iff_of_toList (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    Computable.Weak.isAscendingSet ps = true ↔ S.IsWeakAscendingSet := by
  have ht := isTriangularSet_iff ps |>.mpr ⟨S, hps⟩
  rw [Computable.Weak.isAscendingSet, Bool.and_eq_true, ht, eq_self, true_and,
    decide_eq_true_eq]
  rw [← pairwise_initial_reduced_iff, ← hps, List.pairwise_map]
  simp only [reducedTo_iff, initial_toMvPolynomial]

end Weak
end CharacteristicSet.Bridge
