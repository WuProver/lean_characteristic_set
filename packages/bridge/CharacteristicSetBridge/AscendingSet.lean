/-
Copyright (c) 2026 The CharacteristicSet Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CharacteristicSet Authors
-/
module

public import CharacteristicSet.Computable.AscendingSet
public import CharacteristicSetBridge.Rank
public import CharacteristicSetBridge.Reduced
public import CharacteristicSetBridge.TriangularSet
public import CharacteristicSetTheory.AscendingSet

/-! Complete ordered output correspondence for the standard basic set. -/

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

private theorem basicSet_head_not_reduced (b : MvPolynomial (Fin n) R)
    (S : TriangularSet (Fin n) R) (hb : b ≠ 0) :
    ¬ b.reducedToSet (S.takeConcat b) := by
  intro h
  exact MvPolynomial.not_reduceTo_self hb (h b (TriangularSet.mem_takeConcat S hb))

private theorem basicSet_drop_head (b : MvPolynomial (Fin n) R)
    (tail : List (MvPolynomial (Fin n) R))
    (S : TriangularSet (Fin n) R) (hb : b ≠ 0) :
    (b :: tail).filter (fun q => decide (q.reducedToSet (S.takeConcat b))) =
      tail.filter (fun q => decide (q.reducedToSet (S.takeConcat b))) := by
  simp [basicSet_head_not_reduced b S hb]

private theorem basicSet_filter_map (ps bs : List (MvPoly n R cmp)) (S : TriangularSet (Fin n) R)
    (hbs : bs.map toMvPolynomial = S.toList) :
    (ps.filter (fun p => Computable.reducedToSet p bs)).map toMvPolynomial =
      (ps.map toMvPolynomial).filter (fun p => decide (p.reducedToSet S)) := by
  rw [List.filter_map]
  apply congrArg (List.map toMvPolynomial)
  apply congrArg (fun b => ps.filter b)
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def, decide_eq_true_eq]
  exact reducedToSet_iff_of_toList p bs S hbs

/-- The loop agrees for nonzero candidates and any represented theory accumulator. -/
theorem basicSet_go_toMvPolynomial (ps bs : List (MvPoly n R cmp)) :
    ∀ (S : TriangularSet (Fin n) R) (_hbs : bs.map toMvPolynomial = S.toList)
      (hnz : ∀ p ∈ ps.map toMvPolynomial, p ≠ 0),
    (Computable.basicSet.go ps bs).map toMvPolynomial =
      (IsAscendingSet.basicSet.go (ps.map toMvPolynomial) S hnz).toList := by
  induction ps, bs using Computable.basicSet.go.induct with
  | case1 bs =>
    intro S hbs hnz
    simpa [Computable.basicSet.go, IsAscendingSet.basicSet.go] using hbs
  | case2 bs b tail bsNext ih =>
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S hbs hnz
    have hb : toMvPolynomial b ≠ 0 := hnz _ (by simp)
    have ht := takeConcat_toMvPolynomial bs b S hbs
    have hf := basicSet_filter_map tail (Computable.takeConcat bs b)
      (S.takeConcat (toMvPolynomial b)) ht
    have hf' :
        (tail.filter (fun p => Computable.reducedToSet p
          (Computable.takeConcat bs b))).map toMvPolynomial =
        (toMvPolynomial b :: tail.map toMvPolynomial).filter
          (fun p => decide (p.reducedToSet (S.takeConcat (toMvPolynomial b)))) := by
      rw [basicSet_drop_head _ _ _ hb]
      exact hf
    rw [Computable.basicSet.go]
    simp only [List.map_cons]
    rw [IsAscendingSet.basicSet.go.eq_def]
    dsimp only
    have hnew : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p ≠ 0 := by
      intro p hp
      rw [hf] at hp
      exact hnz p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))
    have ih' : (Computable.basicSet.go
        (tail.filter (fun p => Computable.reducedToSet p (Computable.takeConcat bs b)))
        (Computable.takeConcat bs b)).map toMvPolynomial =
        (IsAscendingSet.basicSet.go
          ((tail.filter (fun p => Computable.reducedToSet p
            (Computable.takeConcat bs b))).map toMvPolynomial)
          (S.takeConcat (toMvPolynomial b)) hnew).toList := by
      simpa only [List.unattach_filter, List.unattach_attach] using
        ih (S.takeConcat (toMvPolynomial b)) ht hnew
    simpa only [hf'] using ih'

/-- Exact equality of the entire ordered basic-set output, including stable
selection among distinct polynomials of equal Wu rank. -/
theorem basicSet_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.basicSet ps).map toMvPolynomial =
      (IsAscendingSet.basicSet (ps.map toMvPolynomial)).toList := by
  have hnz : ∀ p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial, p ≠ 0 := by
    rw [basicSetCandidates_toMvPolynomial]
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  unfold Computable.basicSet
  have h := basicSet_go_toMvPolynomial (Computable.basicSetCandidates ps) [] ∅
    (by simp) hnz
  simpa only [basicSetCandidates_toMvPolynomial, IsAscendingSet.basicSet] using h

/-- The interpreted result represents a strong ascending set contained in the
input and minimal among all strong ascending sets contained in that input.
The witness is the existing theory basic set, so no second runtime type is needed. -/
theorem basicSet_spec (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.basicSet ps).map toMvPolynomial = S.toList ∧
      S.IsAscendingSet ∧
      (∀ p ∈ S, p ∈ ps.map toMvPolynomial) ∧
      (∀ T : TriangularSet (Fin n) R, T.IsAscendingSet →
        (∀ p ∈ T, p ∈ ps.map toMvPolynomial) → S ≤ T) := by
  exact ⟨IsAscendingSet.basicSet (ps.map toMvPolynomial),
    basicSet_toMvPolynomial ps,
    IsAscendingSet.basicSet_isAscendingSet _,
    fun _ hp => IsAscendingSet.basicSet_subset _ hp,
    fun _ hT hsub => IsAscendingSet.basicSet_minimal _ hT hsub⟩

omit [DecidableEq R] in
/-- Every selected Hex polynomial occurs in the original input. -/
theorem basicSet_subset (ps : List (MvPoly n R cmp)) {p : MvPoly n R cmp}
    (hp : p ∈ Computable.basicSet ps) : p ∈ ps := by
  classical
  have hmem : toMvPolynomial p ∈ (Computable.basicSet ps).map toMvPolynomial :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [basicSet_toMvPolynomial, TriangularSet.mem_toList_iff] at hmem
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp (IsAscendingSet.basicSet_subset _ hmem)
  exact toMvPolynomial_injective heq ▸ hq

end CharacteristicSet.Bridge
