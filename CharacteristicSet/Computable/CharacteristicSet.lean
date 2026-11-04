module

public import CharacteristicSet.Computable.AscendingSet
public import CharacteristicSet.Computable.PseudoDivision

/-! Executable characteristic sets. Termination and correctness are proved separately in the bridge. -/

@[expose] public section
namespace CharacteristicSet.Computable
open Hex
universe u
variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Zero R] [One R] [Add R] [Mul R] [Neg R] [Inv R] [DecidableEq R]

/-- One Wu iteration: either return the basic set or continue with the original
input, nonzero remainders, and basic set, in that order. -/
def characteristicSet.step (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (original current : List (MvPoly n R cmp)) :
    Sum (List (MvPoly n R cmp)) (List (MvPoly n R cmp)) :=
  let bs := basic current
  let rs := ((bs.foldl List.erase current).map (fun p => setPseudoRem p bs)).filter
    (fun p => !p.termsList.isEmpty)
  if rs = [] then .inl bs else .inr (original ++ rs ++ bs)

/-- The single recursive executor shared by the two basic-set choices.
`partial_fixpoint` exposes its equations without imposing a termination premise
on callers. The bridge proves that every run over a field terminates. -/
def characteristicSet.go (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (original current : List (MvPoly n R cmp)) :
    List (MvPoly n R cmp) :=
  match _h : characteristicSet.step basic original current with
  | .inl result => result
  | .inr next => characteristicSet.go basic original next
partial_fixpoint

/-- Stop equation for the executor. -/
theorem characteristicSet.go_done
    (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (original current result : List (MvPoly n R cmp))
    (h : characteristicSet.step basic original current = .inl result) :
    characteristicSet.go basic original current = result := by
  rw [characteristicSet.go, h]

/-- Continuation equation for the executor. -/
theorem characteristicSet.go_next
    (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (original current next : List (MvPoly n R cmp))
    (h : characteristicSet.step basic original current = .inr next) :
    characteristicSet.go basic original current = characteristicSet.go basic original next := by
  rw [characteristicSet.go, h]

/-- Compute a characteristic set using the supplied basic-set algorithm. -/
def characteristicSet (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (ps : List (MvPoly n R cmp)) :
    List (MvPoly n R cmp) := characteristicSet.go basic ps ps

namespace Standard
/-- Characteristic set using standard basic sets. -/
def characteristicSet
    (ps : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  Computable.characteristicSet basicSet ps
end Standard

namespace Weak
/-- Characteristic set using weak basic sets. -/
def characteristicSet
    (ps : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  Computable.characteristicSet basicSet ps
end Weak
end CharacteristicSet.Computable
