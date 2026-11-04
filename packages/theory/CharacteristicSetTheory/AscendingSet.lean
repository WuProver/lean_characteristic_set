/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSetTheory.Rank

/-!
# Ascending sets

This file defines standard and weak ascending sets and proves their closure
properties under triangular-set operations. Basic-set algorithms and their
correctness proofs are provided by the computation and bridge packages.

## Main declarations

* `TriangularSet.IsAscendingSet` and `TriangularSet.IsWeakAscendingSet`: Standard and weak
  ascending-set predicates.
* `TriangularSet.isAscendingSet_takeConcat` and `TriangularSet.isWeakAscendingSet_takeConcat`:
  Prefix replacement preserves the corresponding ascending-set property.

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]
* [Wen-Tsun Wu, *Mathematics Mechanization*][wen2000mathematics]

-/

@[expose] public section

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [LinearOrder σ] [DecidableEq R]

namespace TriangularSet

/-- Definition of Standard (Ritt) Ascending Set: A Triangular Set is an Ascending Set
if every element is reduced with respect to its predecessors. -/
def IsAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).reducedTo (S i)

/-- Definition of Weak (Wu) Ascending Set: A Triangular Set is an Ascending Set
if every element's initial is reduced with respect to its predecessors. -/
def IsWeakAscendingSet (S : TriangularSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).initial.reducedTo (S i)

theorem isAscendingSet_iff {S : TriangularSet σ R} : S.IsAscendingSet ↔
    ∀ ⦃i j⦄, i < j → i < S.length → (S j).reducedTo (S i) := by
  refine ⟨fun h i j hij hi ↦ ?_, fun h _ _ hij hj ↦ h hij (lt_trans hij hj)⟩
  by_cases hj : j < S.length
  · exact h hij hj
  rw [eq_zero_iff_length_le.mp <| Nat.le_of_not_lt hj]
  exact zero_reducedTo _

theorem isWeakAscendingSet_iff {S : TriangularSet σ R} : S.IsWeakAscendingSet ↔
    ∀ ⦃i j⦄, i < j → i < S.length → (S j).initial.reducedTo (S i) := by
  refine ⟨fun h i j hij hi ↦ ?_, fun h _ _ hij hj ↦ h hij (lt_trans hij hj)⟩
  by_cases hj : j < S.length
  · exact h hij hj
  rw [eq_zero_iff_length_le.mp <| Nat.le_of_not_lt hj]
  exact zero_reducedTo _

noncomputable instance : @DecidablePred (TriangularSet σ R) IsAscendingSet := fun _ ↦
  have {S : TriangularSet σ R} :
      (∀ j < S.length, ∀ i < j, (S j).reducedTo (S i)) ↔ S.IsAscendingSet :=
    ⟨fun h i j hi hj ↦ h j hj i hi, fun h _ hj _ hi ↦ h hi hj⟩
  decidable_of_iff _ this

noncomputable instance : @DecidablePred (TriangularSet σ R) IsWeakAscendingSet := fun _ ↦
  have {S : TriangularSet σ R} :
      (∀ j < S.length, ∀ i < j, (S j).initial.reducedTo (S i)) ↔ S.IsWeakAscendingSet :=
    ⟨fun h i j hi hj ↦ h j hj i hi, fun h _ hj _ hi ↦ h hi hj⟩
  decidable_of_iff _ this

theorem isWeakAscendingSet_of_isAscendingSet {S : TriangularSet σ R} :
    IsAscendingSet S → IsWeakAscendingSet S :=  fun h _ _ hij hj ↦ initial_reducedTo (h hij hj)

theorem initial_reducedToSet_of_max_vars_ne_bot_of_isWeakAscendingSet
    {S : TriangularSet σ R} {i : ℕ} (h : S.IsWeakAscendingSet)
    (hc : (S i).vars.max ≠ ⊥) : (S i).initial.reducedToSet S := by
  intro p ⟨j, hj, hp⟩
  rw [← hp]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact initial_reducedTo (reducedTo_of_max_vars_lt (max_vars_lt_of_index_lt hj hij))
  · exact hij ▸ initial_reducedTo_self hc
  · exact (isWeakAscendingSet_iff.mp h) hij hj

theorem initial_reducedToSet_of_max_vars_ne_bot
    {S : TriangularSet σ R} {i : ℕ} (h : S.IsAscendingSet)
    (hc : (S i).vars.max ≠ ⊥) : (S i).initial.reducedToSet S :=
  initial_reducedToSet_of_max_vars_ne_bot_of_isWeakAscendingSet
    (isWeakAscendingSet_of_isAscendingSet h) hc

theorem initial_reducedToSet_of_max_vars_ne_bot_of_isWeakAscendingSet'
    {S : TriangularSet σ R} {p : MvPolynomial σ R} (h : S.IsWeakAscendingSet) :
    p ∈ S → p.vars.max ≠ ⊥ → p.initial.reducedToSet S := fun ⟨_i, _, hi⟩ hc ↦
  hi ▸ initial_reducedToSet_of_max_vars_ne_bot_of_isWeakAscendingSet h (hi ▸ hc)

theorem initial_reducedToSet_of_max_vars_ne_bot'
    {S : TriangularSet σ R} {p : MvPolynomial σ R} (h : S.IsAscendingSet) :
    p ∈ S → p.vars.max ≠ ⊥ → p.initial.reducedToSet S := fun ⟨_i, _, hi⟩ hc ↦
  hi ▸ initial_reducedToSet_of_max_vars_ne_bot h (hi ▸ hc)

theorem isAscendingSet_single (p : MvPolynomial σ R) : (single p).IsAscendingSet :=
  fun i _ hij hj ↦ False.elim <| Nat.not_lt_zero i <| lt_of_lt_of_le hij <|
    Nat.le_of_lt_succ <| lt_of_lt_of_le hj <| length_single_le_one

theorem isAscendingSet_empty : (∅ : TriangularSet σ R).IsAscendingSet :=
  (single_eq_zero_iff.mp rfl : single (0 : MvPolynomial σ R) = ∅) ▸ isAscendingSet_single 0

variable {S : TriangularSet σ R} {p : MvPolynomial σ R}

theorem isAscendingSet_take (n : ℕ) :
    S.IsAscendingSet → (S.take n).IsAscendingSet := fun hs i j hij hj ↦ by
  rw [S.length_take] at hj
  rw [take_apply' hj, take_apply' (lt_trans hij hj)]
  exact hs hij (lt_of_lt_of_le hj (Nat.min_le_right ..))

theorem isAscendingSet_drop (n : ℕ) : S.IsAscendingSet → (S.drop n).IsAscendingSet := by
  intro hs a b hij hj
  rw [drop_apply, drop_apply]
  exact hs (Nat.add_lt_add_left hij n) (Nat.add_lt_of_lt_sub' (S.length_drop _ ▸ hj))

theorem isAscendingSet_concat (h : S.CanConcat p) (hp : p.reducedToSet S) :
    S.IsAscendingSet → (S.concat p).IsAscendingSet := fun hs i j hij hj ↦ by
  have hi : i < S.length := lt_of_lt_of_le hij <| Nat.le_of_lt_add_one (S.length_concat h ▸ hj)
  simp only [length_concat, concat_apply, hi, reduceIte] at hj ⊢
  match Nat.lt_succ_iff_lt_or_eq.mp hj with
  | .inl hj => rw [ite_eq_left hj]; exact hs hij hj
  | .inr hj => simp only [hj, lt_self_iff_false, reduceIte]; exact hp _ <| apply_mem hi

theorem isAscendingSet_takeConcat (hp : p.reducedToSet S) :
    S.IsAscendingSet → (S.takeConcat p).IsAscendingSet := fun h ↦ by
  unfold takeConcat
  split_ifs with h1 hc
  repeat exact isAscendingSet_single p
  refine TriangularSet.isAscendingSet_concat _ (fun n hn ↦ ?_) <| isAscendingSet_take _ h
  apply hp
  exact TriangularSet.take_subset S _ <| mem_def.mpr hn

theorem isWeakAscendingSet_single (p : MvPolynomial σ R) : (single p).IsWeakAscendingSet :=
  fun i _ hij hj ↦ False.elim <| Nat.not_lt_zero i <| lt_of_lt_of_le hij <|
    Nat.le_of_lt_succ <| lt_of_lt_of_le hj <| length_single_le_one

theorem isWeakAscendingSet_empty : (∅ : TriangularSet σ R).IsWeakAscendingSet :=
  (single_eq_zero_iff.mp rfl : single (0 : MvPolynomial σ R) = ∅) ▸ isWeakAscendingSet_single 0

variable {S : TriangularSet σ R} {p : MvPolynomial σ R}

theorem isWeakAscendingSet_take (n : ℕ) :
    S.IsWeakAscendingSet → (S.take n).IsWeakAscendingSet := fun hs i j hij hj ↦ by
  rw [S.length_take] at hj
  rw [take_apply' hj, take_apply' (lt_trans hij hj)]
  exact hs hij (lt_of_lt_of_le hj (Nat.min_le_right ..))

theorem isWeakAscendingSet_drop (n : ℕ) : S.IsWeakAscendingSet → (S.drop n).IsWeakAscendingSet := by
  intro hs a b hij hj
  rw [drop_apply, drop_apply]
  exact hs (Nat.add_lt_add_left hij n) (Nat.add_lt_of_lt_sub' (S.length_drop _ ▸ hj))

theorem isWeakAscendingSet_concat (h : S.CanConcat p) (hp : p.initial.reducedToSet S) :
    S.IsWeakAscendingSet → (S.concat p).IsWeakAscendingSet := fun hs i j hij hj ↦ by
  have hi : i < S.length := lt_of_lt_of_le hij <| Nat.le_of_lt_add_one (S.length_concat h ▸ hj)
  simp only [length_concat, concat_apply, hi, reduceIte] at hj ⊢
  match Nat.lt_succ_iff_lt_or_eq.mp hj with
  | .inl hj => rw [ite_eq_left hj]; exact hs hij hj
  | .inr hj => simp only [hj, lt_self_iff_false, reduceIte]; exact hp _ <| apply_mem hi

theorem isWeakAscendingSet_takeConcat (hp : p.initial.reducedToSet S) :
    S.IsWeakAscendingSet → (S.takeConcat p).IsWeakAscendingSet := fun h ↦ by
  unfold takeConcat
  split_ifs with h1 hc
  repeat exact isWeakAscendingSet_single p
  refine TriangularSet.isWeakAscendingSet_concat _ (fun n hn ↦ ?_) <| isWeakAscendingSet_take _ h
  apply hp
  exact TriangularSet.take_subset S _ <| mem_def.mpr hn

end TriangularSet
