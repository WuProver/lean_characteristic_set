module

public import CharacteristicSet.Computable.Initial
public import CharacteristicSet.Computable.Rank
public import CharacteristicSet.Computable.Reduced
public import CharacteristicSet.Computable.TriangularSet

/-! Executable standard and weak ascending-set checks and basic-set algorithms. -/

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

/-- Check the full triangular structure, including nonzero elements. -/
def isTriangularSet (ps : List (MvPoly n R cmp)) : Bool :=
  ps.all (fun p => !p.termsList.isEmpty) &&
    decide (ps.Pairwise (fun p q => variableIndex (mainVar p) < variableIndex (mainVar q)))

namespace Standard

abbrev basicSet := @CharacteristicSet.Computable.basicSet
abbrev basicSet.go := @CharacteristicSet.Computable.basicSet.go

/-- Every element is reduced to every predecessor, in a triangular list. -/
def isAscendingSet (ps : List (MvPoly n R cmp)) : Bool :=
  isTriangularSet ps && decide (ps.Pairwise (fun p q => reducedTo q p = true))

end Standard

namespace Weak

variable [BEq R] [LawfulBEq R] [Add R] [One R]

/-- Initial reduction does not imply triangularity, so both are checked. -/
def isAscendingSet (ps : List (MvPoly n R cmp)) : Bool :=
  isTriangularSet ps && decide (ps.Pairwise (fun p q => reducedTo (initial q) p = true))

/-- Retain only candidates extending the main-variable order with reduced initial. -/
def accepts (b : MvPoly n R cmp) (bs : List (MvPoly n R cmp))
    (p : MvPoly n R cmp) : Bool :=
  decide (variableIndex (mainVar b) < variableIndex (mainVar p)) &&
    reducedToSet (initial p) bs

/-- Internal weak loop; public inputs ensure the accumulator can be extended. -/
def basicSet.go (ps bs : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  match ps with
  | [] => bs
  | b :: tail =>
    let bs' := bs ++ [b]
    go (tail.filter (accepts b bs')) bs'
termination_by ps.length
decreasing_by
  have h := List.length_filter_le (fun p => accepts b (bs ++ [b]) p.val) tail.attach
  simpa only [List.length_unattach, List.length_attach, List.length_cons] using Nat.lt_succ_of_le h

/-- Stable weak basic set with explicit increasing-main-variable filtering. -/
def basicSet (ps : List (MvPoly n R cmp)) : List (MvPoly n R cmp) :=
  basicSet.go (basicSetCandidates ps) []

end Weak

end CharacteristicSet.Computable
