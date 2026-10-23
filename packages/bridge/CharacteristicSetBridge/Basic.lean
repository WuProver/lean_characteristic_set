module

public import CharacteristicSet.Computable.Basic
public import CharacteristicSetTheory.MainDegree
public import HexMvPolyTheory.Correspondence

/-! Correctness of the executable main variable and main degree. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory
open scoped HexMvPolyTheory

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

theorem vars_toMvPolynomial (p : MvPoly n R cmp) :
    (toMvPolynomial p).vars = p.vars.toFinset := by
  ext i
  simp [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]

private theorem list_max (xs : List (Fin n)) :
    (xs.max? : WithBot (Fin n)) = xs.toFinset.max := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.max?_cons, List.toFinset_cons, Finset.max_insert, ← ih]
    cases xs.max? with
    | none =>
      change (a : WithBot (Fin n)) = max (a : WithBot (Fin n)) ⊥
      symm
      apply max_eq_left
      exact bot_le
    | some b => exact (WithBot.coe_max a b).symm

/-- `Option.none` is exactly the bottom value used by the specification. -/
theorem mainVar_toMvPolynomial (p : MvPoly n R cmp) :
    (Computable.mainVar p : WithBot (Fin n)) = (toMvPolynomial p).vars.max := by
  rw [Computable.mainVar, vars_toMvPolynomial, list_max]

theorem mainDegree_toMvPolynomial (p : MvPoly n R cmp) :
    Computable.mainDegree p = (toMvPolynomial p).mainDegree.card := by
  cases h : Computable.mainVar p with
  | none =>
    rw [Computable.mainDegree_of_none h]
    exact ((MvPolynomial.card_mainDegree_eq_zero_iff).mpr
      ((mainVar_toMvPolynomial p).symm.trans h)).symm
  | some i =>
    rw [Computable.mainDegree_of_mainVar h, degreeOf_toMvPolynomial]
    exact (MvPolynomial.card_mainDegree_eq_degreeOf
      ((mainVar_toMvPolynomial p).symm.trans h)).symm

end CharacteristicSet.Bridge
