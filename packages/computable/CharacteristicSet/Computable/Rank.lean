module

public import CharacteristicSet.Computable.Basic

/-! Wu ranks and an explicit lexicographic comparator on Hex polynomials. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]

/-- Wu rank, with `none` below every variable. -/
def rank (p : MvPoly n R cmp) : Option (Fin n) × Nat := (mainVar p, mainDegree p)

/-- A numerical encoding of the main variable; zero represents `none`. -/
def variableIndex (i : Option (Fin n)) : Nat := i.elim 0 (fun j => j.val + 1)

/-- Explicit lexicographic comparison, first variable, then degree. -/
def compareRank (p q : MvPoly n R cmp) : Ordering :=
  (compare (variableIndex (mainVar p)) (variableIndex (mainVar q))).then
    (compare (mainDegree p) (mainDegree q))

theorem compareRank_self (p : MvPoly n R cmp) : compareRank p p = .eq := by
  simp [compareRank]

theorem variableIndex_injective {i j : Option (Fin n)} :
    variableIndex i = variableIndex j → i = j := by
  cases i <;> cases j <;> simp [variableIndex, Fin.ext_iff]

theorem compareRank_eq_iff (p q : MvPoly n R cmp) :
    compareRank p q = .eq ↔ rank p = rank q := by
  simp [compareRank, Ordering.then_eq_eq, rank, Prod.mk.injEq,
    show ∀ i j : Option (Fin n),
      variableIndex i = variableIndex j ↔ i = j from
        fun _ _ => ⟨variableIndex_injective, congrArg variableIndex⟩]

theorem compareRank_lt_iff (p q : MvPoly n R cmp) :
    compareRank p q = .lt ↔
      variableIndex (mainVar p) < variableIndex (mainVar q) ∨
      variableIndex (mainVar p) = variableIndex (mainVar q) ∧ mainDegree p < mainDegree q := by
  simp [compareRank, Ordering.then_eq_lt, Nat.compare_eq_lt]

theorem compareRank_gt_iff (p q : MvPoly n R cmp) :
    compareRank p q = .gt ↔ compareRank q p = .lt := by
  unfold compareRank
  rw [Ordering.then_eq_gt, Ordering.then_eq_lt]
  simp only [Nat.compare_eq_lt, Nat.compare_eq_gt, Nat.compare_eq_eq]
  omega

theorem compareRank_lt_trans {p q r : MvPoly n R cmp}
    (hpq : compareRank p q = .lt) (hqr : compareRank q r = .lt) :
    compareRank p r = .lt := by
  rw [compareRank_lt_iff] at *
  omega

end CharacteristicSet.Computable
