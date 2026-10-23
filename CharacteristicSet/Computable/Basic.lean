module

public import HexMvPoly.Query

/-! Executable main variable and numerical main degree on Hex polynomials. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]

/-- Greatest occurring variable in the natural order, independently of `cmp`. -/
abbrev mainVar (p : MvPoly n R cmp) : Option (Fin n) := p.vars.max?

/-- Numerical degree in the main variable; zero for constants. -/
def mainDegree (p : MvPoly n R cmp) : Nat :=
  (mainVar p).elim 0 (fun i => p.degreeOf i)

theorem mainVar_eq_none_iff (p : MvPoly n R cmp) :
    mainVar p = none ↔ p.vars = [] := List.max?_eq_none_iff

theorem mainVar_eq_some_iff (p : MvPoly n R cmp) (i : Fin n) :
    mainVar p = some i ↔ i ∈ p.vars ∧ ∀ j ∈ p.vars, j ≤ i :=
  List.max?_eq_some_iff

theorem mainDegree_of_mainVar {p : MvPoly n R cmp} {i : Fin n}
    (h : mainVar p = some i) : mainDegree p = p.degreeOf i := by
  simp [mainDegree, h]

theorem mainDegree_of_none {p : MvPoly n R cmp}
    (h : mainVar p = none) : mainDegree p = 0 := by
  simp [mainDegree, h]

end CharacteristicSet.Computable
