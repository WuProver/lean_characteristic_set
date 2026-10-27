module

public import CharacteristicSet.Computable.TriangularSet
public import CharacteristicSetBridge.Basic
public import CharacteristicSetTheory.TriangularSet
public import Mathlib.Data.List.TakeWhile

/-! Exact list semantics of triangular-set prefix replacement. -/

public section

open MvPolynomial

private theorem takeWhile_cut {α : Type*} (xs : List α) (b : α → Bool) (k : Nat)
    (hk : k ≤ xs.length)
    (hb : ∀ j (hj : j < xs.length), j < k → b xs[j] = true)
    (he : ∀ h : k < xs.length, b xs[k] = false) :
    xs.takeWhile b = xs.take k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      have h : b x = false := he (by simp)
      simp [h]
  | succ k ih =>
    cases xs with
    | nil => simp at hk
    | cons x xs =>
      have hbx : b x = true := hb 0 (by simp) (by omega)
      simp only [List.takeWhile_cons, hbx, ↓reduceIte, List.take_succ_cons]
      congr 1
      apply ih xs (by simpa using hk)
      · intro j hj hjk
        exact hb (j+1) (by simpa using hj) (by omega)
      · intro h
        exact he (by simpa using h)

namespace CharacteristicSet.Bridge

variable {n : Nat} {R : Type*} [CommSemiring R] [DecidableEq R]

/-- The theory's cut point retains exactly the prefix of smaller main variables. -/
theorem takeConcat_toList_formula (S : TriangularSet (Fin n) R) (p : MvPolynomial (Fin n) R) :
    (S.takeConcat p).toList =
      if p = 0 then [] else
      S.toList.takeWhile (fun q => decide (q.vars.max < p.vars.max)) ++ [p] := by
  by_cases hp : p = 0
  · subst p
    simp [TriangularSet.takeConcat_zero_eq_empty]
  rw [ite_eq_right hp]
  unfold TriangularSet.takeConcat
  split_ifs with hs hc
  · simp [hs, TriangularSet.single, hp, TriangularSet.single']
  · have hnonempty : 0 < S.toList.length := TriangularSet.length_gt_zero_iff.mpr hs
    have ht : S.toList.takeWhile (fun q => decide (q.vars.max < p.vars.max)) = [] := by
      apply List.takeWhile_eq_nil_iff.mpr
      intro h
      have heq : S.toList.get ⟨0, h⟩ = S 0 := TriangularSet.toList_getElem h
      rw [heq]
      simp only [decide_eq_true_eq]
      exact not_lt_of_ge hc
    simp [ht, TriangularSet.single, hp, TriangularSet.single']
  · let k := Nat.find (TriangularSet.exists_index_max_vars_between_of_max_vars_first_lt
        (S := S) (p := p) (lt_of_not_ge hc))
    have hk := Nat.find_spec (TriangularSet.exists_index_max_vars_between_of_max_vars_first_lt
        (S := S) (p := p) (lt_of_not_ge hc))
    change k ≤ S.length ∧ (S (k-1)).vars.max < p.vars.max ∧
      (p.vars.max ≤ (S k).vars.max ∨ k = S.length) at hk
    dsimp only
    simp only [TriangularSet.toList_concat, TriangularSet.toList_take, List.concat_eq_append]
    change S.toList.take k ++ [p] = _
    congr 1
    symm
    apply takeWhile_cut S.toList _ k hk.1
    · intro j hj hjk
      rw [TriangularSet.toList_getElem hj]
      apply decide_eq_true
      have hle : j ≤ k-1 := by omega
      have hkpos : 0 < k := by omega
      have hlast : k - 1 < S.length :=
        lt_of_lt_of_le (Nat.sub_one_lt (Nat.ne_of_gt hkpos)) hk.1
      exact lt_of_le_of_lt (S.max_vars_le_of_index_le hle hlast) hk.2.1
    · intro h
      rw [TriangularSet.toList_getElem h]
      apply decide_eq_false
      have hlt : k < S.length := h
      have hle : p.vars.max ≤ (S k).vars.max := hk.2.2.resolve_right (Nat.ne_of_lt hlt)
      exact not_lt_of_ge hle

end CharacteristicSet.Bridge


namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory
open scoped HexMvPolyTheory

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

private theorem takeConcat_termsList_isEmpty_iff (p : MvPoly n R cmp) :
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

/-- Full output agreement for any ordinary list representing a theory triangular
set, including a possible nonzero constant prefix and the trivial semiring. -/
theorem takeConcat_toMvPolynomial (ps : List (MvPoly n R cmp)) (p : MvPoly n R cmp)
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    (Computable.takeConcat ps p).map toMvPolynomial =
      (S.takeConcat (toMvPolynomial p)).toList := by
  rw [takeConcat_toList_formula]
  unfold Computable.takeConcat
  simp only [takeConcat_termsList_isEmpty_iff]
  split_ifs with hp
  · rfl
  · simp only [List.map_append, List.map_cons, List.map_nil]
    congr 1
    rw [← hps]
    rw [List.takeWhile_map]
    apply congrArg (List.map toMvPolynomial)
    apply congrArg (fun b => ps.takeWhile b)
    funext q
    dsimp only [Function.comp_def]
    rw [← mainVar_toMvPolynomial, ← mainVar_toMvPolynomial]
    cases Computable.mainVar q with
    | none =>
      cases Computable.mainVar p with
      | none =>
        change false = decide ((⊥ : WithBot (Fin n)) < ⊥)
        simp
      | some j =>
        change true = decide ((⊥ : WithBot (Fin n)) < (j : WithBot (Fin n)))
        simp
    | some i =>
      cases Computable.mainVar p with
      | none =>
        change false = decide ((i : WithBot (Fin n)) < ⊥)
        simp
      | some j =>
        change decide (i < j) = decide ((i : WithBot (Fin n)) < (j : WithBot (Fin n)))
        simp

end CharacteristicSet.Bridge
