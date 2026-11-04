module

public import CharacteristicSet.Computable.Basic

/-! Executable reduction checks against a polynomial or an ordered divisor list. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]

/-- Zero is reduced to every divisor. Otherwise compare degrees in the divisor's
main variable; a constant divisor, including zero, rejects every nonzero input. -/
def reducedTo (q p : MvPoly n R cmp) : Bool :=
  if q.termsList.isEmpty then true else
    match mainVar p with
    | none => false
    | some i => decide (q.degreeOf i < p.degreeOf i)

/-- Check every divisor in order, stopping at the first failure. No sorting,
deduplication or removal of zero or constant divisors is performed. -/
def reducedToSet (q : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) : Bool :=
  ps.all (reducedTo q)

@[simp] theorem reducedTo_zero (p : MvPoly n R cmp) : reducedTo 0 p = true := rfl

@[simp] theorem reducedToSet_nil (q : MvPoly n R cmp) : reducedToSet q [] = true := rfl

@[simp] theorem reducedToSet_cons (q p : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) :
    reducedToSet q (p :: ps) = (reducedTo q p && reducedToSet q ps) := rfl

@[simp] theorem reducedToSet_zero (ps : List (MvPoly n R cmp)) :
    reducedToSet 0 ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

end CharacteristicSet.Computable
