/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSetTheory.Reduced
public import Mathlib.Algebra.BigOperators.Fin

/-! Mathematical pseudo-division certificates, independent of an elimination algorithm. -/

@[expose] public section
namespace MvPolynomial
variable {R σ : Type*} [CommRing R]

section Cancellation
variable [NoZeroDivisors R]
theorem cancellation_degree_lt (i : σ) (f r : MvPolynomial σ R)
    (h : f.degreeOf i ≠ 0) (hn : ¬ r.degreeOf i < f.degreeOf i) :
    (f.initialOf i * r -
      (r.initialOf i * X i ^ (r.degreeOf i - f.degreeOf i)) * f).degreeOf i <
      r.degreeOf i := by
  let I := f.initialOf i
  let term := r.initialOf i * X i ^ (r.degreeOf i - f.degreeOf i)
  change (I * r - term * f).degreeOf i < r.degreeOf i
  suffices (I * r - term * f).degreeOf i ≤ r.degreeOf i - 1 by
    exact (Nat.le_sub_one_iff_lt (lt_of_lt_of_le
      (Nat.ne_zero_iff_zero_lt.mp h) (Nat.not_lt.mp hn))).mp this
  have Id : I.degreeOf i = 0 := by rw [degreeOf_initialOf_self]
  have hmul : (I * r).degreeOf i - 1 ≤ r.degreeOf i - 1 := by
    apply Nat.sub_le_sub_right
    rw [← zero_add (r.degreeOf i), ← Id]
    exact degreeOf_mul_le ..
  refine le_trans ?_ hmul
  apply degreeOf_sub_lt_of_initialOf_eq
  repeat1' rw [mul_assoc, mul_comm _ f, ← mul_assoc]
  · rw [initialOf_mul_X_self_pow, initialOf_mul_eq, initialOf_mul_eq]
    rw [initialOf_initialOf_self, initialOf_initialOf_self, mul_comm]
  have f_ne : f ≠ 0 := ne_zero_of_degreeOf_ne_zero h
  have I_ne : I ≠ 0 := initialOf_ne_zero i f_ne
  have r_ne : r ≠ 0 := by
    contrapose! hn
    rw [hn, degreeOf_zero]
    exact Nat.zero_lt_of_ne_zero h
  have Ir_ne : r.initialOf i ≠ 0 := initialOf_ne_zero i r_ne
  rw [degreeOf_mul_X_self_pow_eq_add_of_ne_zero _ _ (mul_ne_zero_iff.mpr ⟨Ir_ne, f_ne⟩)]
  rw [degreeOf_mul_eq I_ne r_ne, degreeOf_mul_eq Ir_ne f_ne]
  simpa [I] using (Nat.add_sub_of_le <| Nat.le_of_not_lt hn).symm

end Cancellation

variable [DecidableEq R] [LinearOrder σ]

/-- A remainder `r` of `g` by `f` is a polynomial which is reduced with respect to `f` and
suffices `f.initial ^ s * g = q * f + r` for some `s : ℕ` and `q : MvPolynomial σ R`. -/
def IsRemainder (r g f : MvPolynomial σ R) : Prop :=
  r.reducedTo f ∧ ∃ (s : ℕ) (q : MvPolynomial σ R), f.initial ^ s * g = q * f + r

theorem isRemainder_def (r g f : MvPolynomial σ R) : r.IsRemainder g f ↔
    r.reducedTo f ∧ ∃ (s : ℕ) (q : MvPolynomial σ R), f.initial ^ s * g = q * f + r := Iff.rfl

theorem isRemainder_eq_zero_of_dvd [NoZeroDivisors R] {r g f : MvPolynomial σ R}
    (hr : r.IsRemainder g f) (h : f ∣ g) : r = 0 := by
  obtain ⟨s, q, he⟩ := hr.2
  have hd : f ∣ r := (dvd_add_right (dvd_mul_left f q)).mp (he ▸ dvd_mul_of_dvd_right h _)
  by_contra hn
  obtain ⟨j, hj⟩ := WithBot.ne_bot_iff_exists.mp (max_vars_ne_bot_of_reducedTo hn hr.1)
  have hlt := (reducedTo_iff hj.symm hn).mp hr.1
  obtain ⟨c, hc⟩ := hd
  have hf : f ≠ 0 := left_ne_zero_of_mul (hc ▸ hn)
  have hh : c ≠ 0 := right_ne_zero_of_mul (hc ▸ hn)
  rw [hc, degreeOf_mul_eq hf hh] at hlt
  omega

/-- An algebraic certificate for division by an ordered list. -/
def HasPseudoCertificate (r g : MvPolynomial σ R) (ps : List (MvPolynomial σ R)) : Prop :=
  ∃ (es : Fin ps.length → ℕ) (qs : Fin ps.length → MvPolynomial σ R),
    (∏ i, ps[i.val].initial ^ es i) * g = (∑ i, qs i * ps[i.val]) + r

/-- A reduced remainder with a pseudo-division certificate. -/
def IsSetRemainder (r g : MvPolynomial σ R) (S : TriangularSet σ R) : Prop :=
  r.reducedToSet S ∧ HasPseudoCertificate r g S.toList

theorem HasPseudoCertificate.nil (g : MvPolynomial σ R) : HasPseudoCertificate g g [] := by
  exact ⟨Fin.elim0, Fin.elim0, by simp⟩

/-- Compose certificates; this constructs witnesses in Prop, not a second algorithm. -/
theorem HasPseudoCertificate.cons {g t r f : MvPolynomial σ R} {ps : List (MvPolynomial σ R)}
    (ht : HasPseudoCertificate t g ps) (s : ℕ) (q : MvPolynomial σ R)
    (hr : f.initial ^ s * t = q * f + r) : HasPseudoCertificate r g (f :: ps) := by
  obtain ⟨es, qs, heq⟩ := ht
  refine ⟨Fin.cons s es, Fin.cons q (fun i => qs i * f.initial ^ s), ?_⟩
  simp only [List.length_cons, Fin.prod_univ_succ, Fin.sum_univ_succ,
    Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
    List.getElem_cons_succ,
    Fin.cons_zero, Fin.cons_succ]
  calc
    _ = f.initial ^ s * ((∑ i, qs i * ps[i.val]) + t) := by rw [mul_assoc, heq]
    _ = q * f + (∑ i, (qs i * f.initial ^ s) * ps[i.val]) + r := by
      rw [mul_add, hr, Finset.mul_sum]
      have hs : (∑ i : Fin ps.length, f.initial ^ s * (qs i * ps[i.val])) =
          ∑ i : Fin ps.length, (qs i * f.initial ^ s) * ps[i.val] :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      rw [hs]; ring

/-- A member has a legal zero remainder, independently of any chosen algorithm. -/
theorem zero_isSetRemainder_of_mem {S : TriangularSet σ R} {p : MvPolynomial σ R}
    (hp : p ∈ S) : (0 : MvPolynomial σ R).IsSetRemainder p S := by
  obtain ⟨i, hi, hp⟩ := hp
  refine ⟨zero_reducedToSet, (fun _ => 0),
    (fun j => if j = ⟨i, hi⟩ then 1 else 0), ?_⟩
  simp only [pow_zero, Finset.prod_const_one, one_mul, add_zero]
  calc
    p = S.toList[i] := by simpa [TriangularSet.toList_getElem] using hp.symm
    _ = ∑ j : Fin S.toList.length, (if j = ⟨i, hi⟩ then 1 else 0) * S.toList[j.val] := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl

/-- The only operation required by the characteristic-set theory. -/
structure PseudoDivisionSpec (σ R : Type*) [CommRing R] [DecidableEq R] [LinearOrder σ] where
  remainder : MvPolynomial σ R → TriangularSet σ R → MvPolynomial σ R
  isSetRemainder : ∀ g S, (remainder g S).IsSetRemainder g S

end MvPolynomial
