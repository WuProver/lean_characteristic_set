module

public import CharacteristicSet.Computable.Initial
public import CharacteristicSet.Bridge.Basic
public import CharacteristicSet.Initial

/-! Correctness of executable initial coefficients. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory
open scoped BigOperators HexMvPolyTheory

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

@[simp] theorem monoEquiv_set_zero (i : Fin n) (m : Mono n) :
    monoEquiv (m.set i 0) = (monoEquiv m).erase i := by
  ext j
  simp only [Finsupp.erase_apply, monoEquiv_apply]
  change (m.set i.val 0)[j.val] = if j = i then 0 else m[j.val]
  rw [Vector.getElem_set i.isLt j.isLt]
  by_cases h : i = j <;> simp_all [Fin.ext_iff, eq_comm]

/-- The executable coefficient extraction agrees with the existing initial. -/
theorem initialOf_toMvPolynomial (i : Fin n) (p : MvPoly n R cmp) :
    toMvPolynomial (Computable.initialOf i p) = (toMvPolynomial p).initialOf i := by
  rw [Computable.initialOf, toMvPolynomial_ofTerms]
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  rw [List.map_map]
  rw [← List.sum_toFinset _ ((p.monomials_nodup).filter _)]
  rw [List.toFinset_filter, Finset.sum_filter]
  rw [MvPolynomial.initialOf_def, support_toMvPolynomial, Finset.sum_filter,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m _
  simp [monoEquiv_apply, degreeOf_toMvPolynomial]

private theorem termsList_isEmpty_iff (p : MvPoly n R cmp) :
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

theorem initial_toMvPolynomial (p : MvPoly n R cmp) :
    toMvPolynomial (Computable.initial p) = (toMvPolynomial p).initial := by
  unfold Computable.initial MvPolynomial.initial
  simp only [termsList_isEmpty_iff]
  split_ifs with h
  · simp
  · rw [← mainVar_toMvPolynomial]
    cases Computable.mainVar p with
    | none => simp
    | some i => simpa using initialOf_toMvPolynomial i p

end CharacteristicSet.Bridge
