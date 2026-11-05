/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSet.Computable.PseudoDivision
public import CharacteristicSetBridge.Initial
public import CharacteristicSetBridge.Reduced
public import CharacteristicSetTheory.PseudoDivision

/-! Direct correctness proofs for the executable pseudo-division and its internal bound. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory MvPolynomial TriangularSet
open scoped HexMvPolyTheory

section CommRing

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommRing R] [DecidableEq R]
  [NoZeroDivisors R]

/-- Every actual Hex elimination strictly decreases the selected degree. -/
theorem pseudoOf_step_degree_lt (i : Fin n) (f r : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) (hn : ¬ r.degreeOf i < f.degreeOf i) :
    (Computable.initialOf i f * r -
      (Computable.initialOf i r * MvPoly.X i ^ (r.degreeOf i - f.degreeOf i)) * f).degreeOf i <
      r.degreeOf i := by
  simpa only [degreeOf_toMvPolynomial, toMvPolynomial_sub, toMvPolynomial_mul,
    initialOf_toMvPolynomial, toMvPolynomial_pow, toMvPolynomial_X] using
    cancellation_degree_lt i (toMvPolynomial f) (toMvPolynomial r)
      (by simpa using h) (by simpa using hn)

omit [NoZeroDivisors R] in
/-- The actual loop preserves reconstruction, for every fuel value. -/
theorem pseudoOf_go_equation (i : Fin n) (g f : MvPoly n R cmp) (fuel s : ℕ)
    (q r : MvPoly n R cmp)
    (heq : (toMvPolynomial f).initialOf i ^ s * toMvPolynomial g =
      toMvPolynomial q * toMvPolynomial f + toMvPolynomial r) :
    let res := Computable.pseudoOf.go i f fuel s q r
    (toMvPolynomial f).initialOf i ^ res.exponent * toMvPolynomial g =
      toMvPolynomial res.quotient * toMvPolynomial f + toMvPolynomial res.remainder := by
  induction fuel generalizing s q r with
  | zero => exact heq
  | succ fuel ih =>
    rw [Computable.pseudoOf.go]
    split
    · exact heq
    · apply ih
      simp only [toMvPolynomial_add, toMvPolynomial_sub, toMvPolynomial_mul,
        initialOf_toMvPolynomial, toMvPolynomial_pow, toMvPolynomial_X]
      rw [pow_succ', mul_assoc, heq]
      ring

/-- Sufficient fuel reaches a remainder of smaller degree. -/
theorem pseudoOf_go_stops (i : Fin n) (f : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) (fuel s : ℕ) (q r : MvPoly n R cmp)
    (enough : r.degreeOf i < fuel) :
    (Computable.pseudoOf.go i f fuel s q r).remainder.degreeOf i < f.degreeOf i := by
  induction fuel generalizing s q r with
  | zero => omega
  | succ fuel ih =>
    rw [Computable.pseudoOf.go]
    split
    · assumption
    · apply ih
      have := pseudoOf_step_degree_lt i f r h (by assumption)
      omega

omit [NoZeroDivisors R] in
/-- Variables absent from the divisor cannot acquire a greater degree. -/
theorem pseudoOf_go_degree_le (i j : Fin n) (f : MvPoly n R cmp)
    (hi : i ≠ j) (hj : f.degreeOf j = 0) (fuel s : ℕ) (q r : MvPoly n R cmp) :
    (Computable.pseudoOf.go i f fuel s q r).remainder.degreeOf j ≤ r.degreeOf j := by
  induction fuel generalizing s q r with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [Computable.pseudoOf.go]
    split
    · exact le_rfl
    · refine le_trans (ih ..) ?_
      simp only [degreeOf_toMvPolynomial] at hj ⊢
      simp only [toMvPolynomial_sub, toMvPolynomial_mul, initialOf_toMvPolynomial,
        toMvPolynomial_pow, toMvPolynomial_X]
      apply le_trans (degreeOf_sub_le ..)
      apply max_le <;> apply le_trans (degreeOf_mul_le ..)
      · have hz : ((toMvPolynomial f).initialOf i).degreeOf j = 0 :=
          Nat.eq_zero_of_le_zero (by
            simpa only [hj] using degreeOf_initialOf_le i j (toMvPolynomial f))
        simp [hz]
      · rw [hj, add_zero]
        apply le_trans (degreeOf_mul_le ..)
        rw [degreeOf_X_pow_of_ne _ hi.symm, add_zero]
        exact degreeOf_initialOf_le i j (toMvPolynomial r)

omit [NoZeroDivisors R] in
theorem pseudoOf_equation (i : Fin n) (g f : MvPoly n R cmp) :
    Computable.initialOf i f ^ (Computable.pseudoOf i g f).exponent * g =
      (Computable.pseudoOf i g f).quotient * f + (Computable.pseudoOf i g f).remainder := by
  apply toMvPolynomial_injective
  simp only [toMvPolynomial_mul, toMvPolynomial_pow, initialOf_toMvPolynomial, toMvPolynomial_add]
  unfold Computable.pseudoOf
  split_ifs with h
  · simp only
    rw [pow_one, initialOf_eq_of_degreeOf_eq_zero (by simpa using h),
      toMvPolynomial_zero, add_zero, mul_comm]
  · exact pseudoOf_go_equation i g f _ 0 0 g (by simp)

theorem pseudoOf_remainder_degree_lt (i : Fin n) (g f : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) :
    (Computable.pseudoOf i g f).remainder.degreeOf i < f.degreeOf i := by
  rw [Computable.pseudoOf, ite_eq_right h]
  exact pseudoOf_go_stops i f h _ _ _ _ (Nat.lt_succ_self _)

end CommRing
section Field
variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Field R] [DecidableEq R]

private theorem pseudo_termsList_isEmpty_iff (p : MvPoly n R cmp) :
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

/-- Zero divisors preserve the dividend, with zero exponent and quotient. -/
theorem pseudo_zero (g : MvPoly n R cmp) :
    Computable.pseudo g 0 = ⟨0, 0, g⟩ := rfl

/-- Nonzero constants perform ordinary coefficient division. -/
theorem pseudo_C (g : MvPoly n R cmp) (c : R) (h : c ≠ 0) :
    Computable.pseudo g (MvPoly.C c) = ⟨0, MvPoly.C c⁻¹ * g, 0⟩ := by
  have hv : Computable.mainVar (MvPoly.C c : MvPoly n R cmp) = none := by
    simpa only [toMvPolynomial_C, vars_C, Finset.max_empty, WithBot.none_eq_bot] using
      mainVar_toMvPolynomial (MvPoly.C c : MvPoly n R cmp)
  unfold Computable.pseudo
  simp only [pseudo_termsList_isEmpty_iff, toMvPolynomial_C, C_ne_zero.mpr h,
    ↓reduceIte, hv, MvPoly.coeff_C, ↓reduceIte]

/-- A divisor with a main variable selects precisely the existing `pseudoOf` result. -/
theorem pseudo_of_mainVar (g f : MvPoly n R cmp) (i : Fin n)
    (h : Computable.mainVar f = some i) :
    Computable.pseudo g f = Computable.pseudoOf i g f := by
  have hn : toMvPolynomial f ≠ 0 := by
    intro hf
    have hv := mainVar_toMvPolynomial f
    rw [h, hf] at hv
    simp at hv
  unfold Computable.pseudo
  simp only [pseudo_termsList_isEmpty_iff, hn, ↓reduceIte, h]

/-- Reconstruction of the concrete result, including zero and constant divisors. -/
theorem pseudo_equation (g f : MvPoly n R cmp) :
    Computable.initial f ^ (Computable.pseudo g f).exponent * g =
      (Computable.pseudo g f).quotient * f + (Computable.pseudo g f).remainder := by
  unfold Computable.pseudo
  split_ifs with hz
  · simp
  · cases hv : Computable.mainVar f with
    | none =>
      apply toMvPolynomial_injective
      have hc : (toMvPolynomial f).vars.max = ⊥ :=
        (mainVar_toMvPolynomial f).symm.trans (by simpa only [WithBot.none_eq_bot] using hv)
      have hf := vars_eq_empty_iff_eq_C.mp (Finset.max_eq_bot.mp hc)
      have hn : (toMvPolynomial f).coeff 0 ≠ 0 := by
        intro h
        apply hz
        apply (pseudo_termsList_isEmpty_iff _).mpr
        simpa [h] using hf
      simp only [toMvPolynomial_mul, toMvPolynomial_C, pow_zero, one_mul, add_zero]
      have hcoeff : f.coeff Mono.zero = (toMvPolynomial f).coeff 0 := by
        simpa using (coeff_toMvPolynomial (Mono.zero : Mono n) f).symm
      rw [hf, hcoeff]
      rw [mul_right_comm, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]
    | some i =>
      have hi : Computable.initial f = Computable.initialOf i f := by
        simp [Computable.initial, hv, hz]
      rw [hi]
      exact pseudoOf_equation i g f

theorem pseudo_remainder_isRemainder (g f : MvPoly n R cmp) (h : f ≠ 0) :
    (toMvPolynomial (Computable.pseudo g f).remainder).IsRemainder
      (toMvPolynomial g) (toMvPolynomial f) := by
  refine ⟨?_, (Computable.pseudo g f).exponent,
    toMvPolynomial (Computable.pseudo g f).quotient, ?_⟩
  · unfold Computable.pseudo
    have hz : f.termsList.isEmpty ≠ true := by
      intro hz
      apply h
      exact toMvPolynomial_injective (by simpa using (pseudo_termsList_isEmpty_iff _).mp hz)
    simp only [hz, Bool.false_eq_true, ↓reduceIte]
    cases hv : Computable.mainVar f with
    | none => simp [toMvPolynomial_zero, zero_reducedTo]
    | some i =>
      have hc : (toMvPolynomial f).vars.max = some i := (mainVar_toMvPolynomial f).symm.trans hv
      have hd : f.degreeOf i ≠ 0 := by
        rw [degreeOf_toMvPolynomial]
        exact mem_vars_iff_degreeOf_ne_zero.mp (Finset.mem_of_max hc)
      by_cases hr : toMvPolynomial (Computable.pseudoOf i g f).remainder = 0
      · rw [hr]; exact zero_reducedTo _
      · exact (MvPolynomial.reducedTo_iff hc hr).mpr
          (by simpa using pseudoOf_remainder_degree_lt i g f hd)
  · have he := congrArg toMvPolynomial (pseudo_equation g f)
    simpa only [toMvPolynomial_mul, toMvPolynomial_pow, toMvPolynomial_add,
      initial_toMvPolynomial] using he

theorem pseudo_degree_le (g f : MvPoly n R cmp) (j : Fin n) (hj : f.degreeOf j = 0) :
    (Computable.pseudo g f).remainder.degreeOf j ≤ g.degreeOf j := by
  unfold Computable.pseudo
  split_ifs
  · exact le_rfl
  · cases hv : Computable.mainVar f with
    | none => simp
    | some i =>
      have hc : (toMvPolynomial f).vars.max = some i := (mainVar_toMvPolynomial f).symm.trans hv
      have hd : f.degreeOf i ≠ 0 := by
        rw [degreeOf_toMvPolynomial]
        exact mem_vars_iff_degreeOf_ne_zero.mp (Finset.mem_of_max hc)
      have hi : i ≠ j := by intro h; subst j; contradiction
      simp only [Computable.pseudoOf, hd, ↓reduceIte]
      exact pseudoOf_go_degree_le i j f hi hj _ _ _ _

/-- The list fold constructs a certificate without computing quotients at runtime. -/
private theorem fold_certificate (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) :
    HasPseudoCertificate (toMvPolynomial (Computable.setPseudoRem g ps))
      (toMvPolynomial g) (ps.map toMvPolynomial) := by
  induction ps with
  | nil => exact HasPseudoCertificate.nil _
  | cons f ps ih =>
    rw [Computable.setPseudoRem_cons, List.map_cons]
    apply HasPseudoCertificate.cons ih (Computable.pseudo (Computable.setPseudoRem g ps) f).exponent
      (toMvPolynomial (Computable.pseudo (Computable.setPseudoRem g ps) f).quotient)
    have he := congrArg toMvPolynomial (pseudo_equation (Computable.setPseudoRem g ps) f)
    simpa only [toMvPolynomial_mul, toMvPolynomial_pow, toMvPolynomial_add,
      initial_toMvPolynomial] using he

/-- A zero pseudo-remainder implies vanishing wherever the divisors vanish and
all their initials are nonzero. No triangularity assumption is needed. -/
theorem setPseudoRem_aeval_eq_zero (K : Type*) [Field K] [Algebra R K]
    (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) (x : Fin n → K)
    (hr : Computable.setPseudoRem g ps = 0)
    (hz : ∀ p ∈ ps, MvPolynomial.aeval x (toMvPolynomial p) = 0)
    (hi : ∀ p ∈ ps, MvPolynomial.aeval x (toMvPolynomial p).initial ≠ 0) :
    MvPolynomial.aeval x (toMvPolynomial g) = 0 := by
  obtain ⟨es, qs, he⟩ := fold_certificate g ps
  have he := congrArg (MvPolynomial.aeval x) he
  simp only [map_mul, map_prod, map_pow, map_add, map_sum, hr,
    toMvPolynomial_zero, map_zero] at he
  have hs : (∑ i : Fin (ps.map toMvPolynomial).length,
      MvPolynomial.aeval x (qs i) *
        MvPolynomial.aeval x (ps.map toMvPolynomial)[i.val]) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp (List.getElem_mem i.isLt)
    rw [← heq, hz p hp, mul_zero]
  rw [hs, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (Finset.prod_ne_zero_iff.mpr fun i _ =>
    pow_ne_zero _ (by
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp (List.getElem_mem i.isLt)
      rw [← heq]
      exact hi p hp))

private theorem fold_reduced (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (hn : ∀ f ∈ ps, f ≠ 0)
    (hc : (ps.map toMvPolynomial).Pairwise (fun p q => p.vars.max < q.vars.max)) :
    ∀ p ∈ ps, (toMvPolynomial (Computable.setPseudoRem g ps)).reducedTo (toMvPolynomial p) := by
  induction ps with
  | nil => simp
  | cons f ps ih =>
    intro p hp
    rw [Computable.setPseudoRem_cons]
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      exact pseudo_remainder_isRemainder _ f (hn f (by simp)) |>.1
    · have ih := ih (fun p hp => hn p (by simp [hp])) (by simpa using hc.of_cons) p hp
      by_cases hr :
          toMvPolynomial (Computable.pseudo (Computable.setPseudoRem g ps) f).remainder = 0
      · rw [hr]; exact zero_reducedTo _
      · have ht : toMvPolynomial (Computable.setPseudoRem g ps) ≠ 0 := by
          intro hz
          have he := pseudo_remainder_isRemainder (Computable.setPseudoRem g ps) f (hn f (by simp))
          exact hr (isRemainder_eq_zero_of_dvd he (by rw [hz]; exact dvd_zero _))
        have hv := max_vars_ne_bot_of_reducedTo ht ih
        obtain ⟨j, hj⟩ := WithBot.ne_bot_iff_exists.mp hv
        apply (MvPolynomial.reducedTo_iff hj.symm hr).mpr
        apply lt_of_le_of_lt
          (show _ ≤ (toMvPolynomial (Computable.setPseudoRem g ps)).degreeOf j from ?_)
          ((MvPolynomial.reducedTo_iff hj.symm ht).mp ih)
        simp only [← degreeOf_toMvPolynomial]
        apply (show (Computable.pseudo (Computable.setPseudoRem g ps) f).remainder.degreeOf j ≤
          (Computable.setPseudoRem g ps).degreeOf j from pseudo_degree_le _ _ j ?_)
        rw [degreeOf_toMvPolynomial]
        apply (iff_not_comm.mpr mem_vars_iff_degreeOf_ne_zero).mpr
        apply Finset.notMem_of_max_lt_coe
        have hh := (List.pairwise_cons.mp hc).1 (toMvPolynomial p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
        simpa [← hj] using hh

theorem setPseudoRem_isSetRemainder (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    (toMvPolynomial (Computable.setPseudoRem g ps)).IsSetRemainder (toMvPolynomial g) S := by
  refine ⟨?_, hps ▸ fold_certificate g ps⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hps.symm ▸ mem_toList_iff.mpr hp)
  apply fold_reduced g ps ?_ (hps.symm ▸ S.toList_pairwise) q hq
  intro f hf hz
  have := S.toList_non_zero (hps ▸ List.mem_map.mpr ⟨f, hf, rfl⟩)
  exact this (by simp [hz])

/-- The concrete result is reduced with respect to the represented triangular set. -/
theorem setPseudoRem_reducedToSet (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    (toMvPolynomial (Computable.setPseudoRem g ps)).reducedToSet S :=
  (setPseudoRem_isSetRemainder g ps S hps).1

theorem setPseudoRem_reducedToSet_eq_true (g : MvPoly n R cmp)
    (ps : List (MvPoly n R cmp)) (S : TriangularSet (Fin n) R)
    (hps : ps.map toMvPolynomial = S.toList) :
    Computable.reducedToSet (Computable.setPseudoRem g ps) ps = true :=
  (reducedToSet_iff_of_toList _ ps S hps).mpr (setPseudoRem_reducedToSet g ps S hps)

/-- Interpret the executable remainder as an implementation of the theory interface. -/
noncomputable def setRemainderSpec : PseudoDivisionSpec (Fin n) R where
  remainder g S := toMvPolynomial (Computable.setPseudoRem (ofMvPolynomial (cmp := cmp) g)
    (S.toList.map (ofMvPolynomial (cmp := cmp))))
  isSetRemainder g S := by
    simpa [List.map_map, Function.comp_def] using
      setPseudoRem_isSetRemainder (ofMvPolynomial (cmp := cmp) g)
        (S.toList.map (ofMvPolynomial (cmp := cmp))) S (by simp [List.map_map, Function.comp_def])

theorem setPseudoRem_eq_remainder (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    toMvPolynomial (Computable.setPseudoRem g ps) =
      (setRemainderSpec (cmp := cmp)).remainder (toMvPolynomial g) S := by
  simp [setRemainderSpec, ← hps, List.map_map, Function.comp_def]

end Field
end CharacteristicSet.Bridge
