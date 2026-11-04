module

public import CharacteristicSet.Computable.CharacteristicSet

/-! Executable zero decomposition by branching on the initials of a characteristic set. -/

@[expose] public section
namespace CharacteristicSet.Computable
open Hex
universe u
variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Zero R] [One R] [Add R] [Mul R] [Neg R] [Inv R] [DecidableEq R]

/-- Internal recursive executor. The bridge proves that every run over a field
returns `some`; callers need no termination proof or iteration limit. -/
def zeroDecomposition.run (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (ps : List (MvPoly n R cmp)) : Option (List (List (MvPoly n R cmp))) := do
  let cs := characteristicSet basic ps
  let children ← (cs.filter (fun p => (mainVar p).isSome)).mapM
    (fun p => zeroDecomposition.run basic (initial p :: cs ++ ps))
  pure (cs :: children.flatten)
partial_fixpoint

/-- Characteristic set followed by the decompositions of its nonconstant initial branches. -/
def zeroDecomposition (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
    (ps : List (MvPoly n R cmp)) : List (List (MvPoly n R cmp)) :=
  (zeroDecomposition.run basic ps).getD []

namespace Standard
/-- Zero decomposition using standard characteristic sets. -/
def zeroDecomposition (ps : List (MvPoly n R cmp)) : List (List (MvPoly n R cmp)) :=
  Computable.zeroDecomposition basicSet ps
end Standard
namespace Weak
/-- Zero decomposition using weak characteristic sets. -/
def zeroDecomposition (ps : List (MvPoly n R cmp)) : List (List (MvPoly n R cmp)) :=
  Computable.zeroDecomposition basicSet ps
end Weak
end CharacteristicSet.Computable
