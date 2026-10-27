module

public import CharacteristicSet.Computable.Rank
public import CharacteristicSet.Computable.Reduced
public import CharacteristicSet.Computable.TriangularSet

/-! The executable standard (strong ascending) basic-set algorithm. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]

/-- Stable non-strict Wu-rank sorting followed by canonical zero removal.
Equal ranks retain their input order, including distinct polynomials. -/
def basicSetCandidates (ps : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  (ps.mergeSort (fun p q => !(compareRank p q == .gt))).filter
    (fun p => !p.termsList.isEmpty)

/-- Internal loop on ordinary lists. The public entry supplies nonzero candidates
and an empty accumulator; arbitrary internal states need not be ascending sets. -/
def basicSet.go (ps bs : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  match ps with
  | [] => bs
  | b :: tail =>
    let bs' := takeConcat bs b
    go (tail.filter (fun p => reducedToSet p bs')) bs'
termination_by ps.length
decreasing_by
  have h := List.length_filter_le (fun p => reducedToSet p.val (takeConcat bs b)) tail.attach
  simpa only [List.length_unattach, List.length_attach, List.length_cons] using Nat.lt_succ_of_le h

/-- Compute the standard basic set of any polynomial list. Sort stably by Wu
rank, discard zeros, then repeatedly select the first remaining polynomial,
replace the accumulator prefix, and retain candidates reduced to that list. -/
def basicSet (ps : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  basicSet.go (basicSetCandidates ps) []

end CharacteristicSet.Computable
