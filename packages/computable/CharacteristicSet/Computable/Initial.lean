module

public import CharacteristicSet.Computable.Basic

/-! Executable initial coefficients, preserving the number and indexing of variables. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Zero R] [BEq R] [LawfulBEq R] [Add R]

/-- Keep terms of maximal `i`-degree and erase their `i` coordinate.
`ofTerms` maintains Hex's canonical representation. -/
def initialOf (i : Fin n) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  let d := p.degreeOf i
  MvPoly.ofTerms ((p.monomials.filter (fun m => m[i] == d)).map
    (fun m => (m.set i 0, p.coeff m)))

/-- Zero has initial zero, nonzero constants have initial one. -/
def initial [One R] (p : MvPoly n R cmp) : MvPoly n R cmp :=
  if p.termsList.isEmpty then 0 else
    (mainVar p).elim (MvPoly.C 1) (fun i => initialOf i p)

end CharacteristicSet.Computable
