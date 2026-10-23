/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Main degree of a polynomial

`MvPolynomial.mainDegree p` is the multiset of occurrences of the maximal variable of `p`.
Its cardinality is the degree in that variable; it is empty for constants and zero.

The definition and lemmas are ported from the `Degrees` and `Variables` modules in
SnkXyx/mathlib4 at b7f37486b1c723b65299b4fd7ad635131674d9e8.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

section mainDegree

variable [LinearOrder σ] {i : σ} {p : MvPolynomial σ R}

instance decidablePredIsMaxOnDegrees : DecidablePred (IsMaxOn id (p.degrees.toFinset : Set σ)) := by
  intro i
  rw [isMaxOn_iff]
  infer_instance

/--
When `σ` is a linear order, `mainDegree p` is the multiset consisting of the maximal variable
among all variables appearing in `p`, appearing with its largest multiplicity among all monomials
in `p`.

For example, `mainDegree (x^2 * y + x * y^3)` is `{y, y, y}` when `x < y`.
-/
def mainDegree (p : MvPolynomial σ R) : Multiset σ :=
  p.degrees.filter (IsMaxOn id p.degrees.toFinset)

theorem mainDegree_def (p : MvPolynomial σ R) :
    p.mainDegree = p.degrees.filter (IsMaxOn id p.degrees.toFinset) := Eq.refl _

theorem forall_mainDegree_eq_of_forall_degrees_le (h1 : i ∈ p.degrees)
    (h2 : IsMaxOn id p.degrees.toFinset i) : ∀ j ∈ p.mainDegree, i = j := by
  intro j hj
  rw [mainDegree_def] at hj
  apply le_antisymm
  · apply (Multiset.mem_filter.mp hj).2
    exact Multiset.mem_toFinset.mpr h1
  apply h2
  apply Multiset.mem_toFinset.mpr
  exact Multiset.mem_of_mem_filter hj

theorem card_mainDegree_eq_degreeOf_of_forall_degrees_le (h1 : i ∈ p.degrees)
    (h2 : IsMaxOn id p.degrees.toFinset i) : p.mainDegree.card = p.degreeOf i := by
  have := forall_mainDegree_eq_of_forall_degrees_le h1 h2
  rw [← Multiset.count_eq_card.mpr this]
  rw [degreeOf_def, mainDegree, Multiset.count_filter, ite_eq_left h2]

@[simp]
theorem mainDegree_zero : (0 : MvPolynomial σ R).mainDegree = 0 := Eq.refl _

theorem mainDegree_C (r : R) : (C r : MvPolynomial σ R).mainDegree = 0 := by
  simp [mainDegree_def, degrees_C, Multiset.filter_zero]

@[simp]
theorem mainDegree_X [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).mainDegree = {i} := by
  simp [mainDegree_def, degrees_X, isMaxOn_iff]

end mainDegree

section MainDegree

variable [LinearOrder σ] {c : σ} {p : MvPolynomial σ R}

theorem card_mainDegree_eq_degreeOf (h : p.vars.max = c) : p.mainDegree.card = p.degreeOf c := by
  rw [vars_def] at h
  apply card_mainDegree_eq_degreeOf_of_forall_degrees_le
  · apply Multiset.mem_toFinset.mp
    exact Finset.mem_of_max h
  intro j hj
  have := Finset.le_max hj
  simp only [h, WithBot.coe_le_coe] at this
  exact this

theorem card_mainDegree_eq_zero_iff : p.mainDegree.card = 0 ↔ p.vars.max = ⊥ where
  mp h :=
    match hc : p.vars.max with
    | ⊥ => rfl
    | Option.some c => by
      absurd Finset.mem_of_max hc
      rw [card_mainDegree_eq_degreeOf hc, degreeOf] at h
      simpa only [vars_def, Multiset.mem_toFinset, Multiset.count_eq_zero] using h
  mpr h := by
    simp only [mainDegree, Multiset.card_eq_zero]
    suffices p.degrees = 0 by simp [this, Multiset.filter_zero]
    rw [vars_def] at h
    apply Multiset.toFinset_eq_empty.mp
    exact Finset.max_eq_bot.mp h

end MainDegree

end MvPolynomial
