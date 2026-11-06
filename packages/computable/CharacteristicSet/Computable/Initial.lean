module

import HexBasic.Fold
public import CharacteristicSet.Computable.Basic

/-! Standard initial-coefficient definitions with verified `Internal` implementations.
The equivalence proofs unfold term storage; `csimp` selects the optimized versions
for native execution. Both definitions preserve variable number and indexing. -/

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

/- Representation-dependent proofs: `initialOf_eq_internal` unfolds `foldTerms`
to Std.ExtTreeMap.foldl. `initial_eq_internal` identifies the cached tree size
with the emptiness of its term list. No raw tree construction or balance invariant
is used in these production implementations. -/

/-- Extract maximal-degree terms directly, retaining their stored coefficients.
The first traversal determines the degree; the second builds only the retained terms. -/
def initialOfInternal (i : Fin n) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  let d := p.degreeOf i
  p.foldTerms (fun acc m c =>
    if m[i] == d then acc.addMonomial (m.set i 0) c else acc) 0

/-- Compile coefficient extraction to two direct term traversals. -/
@[csimp] theorem initialOf_eq_internal : @initialOf = @initialOfInternal := by
  funext n R cmp _ _ _ _ _ _ i p
  unfold initialOf initialOfInternal MvPoly.ofTerms MvPoly.foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  change _ = p.termsList.foldl _ _
  unfold MvPoly.monomials
  dsimp only
  rw [List.filter_map, List.map_map, List.foldl_map, List.foldl_filter]
  apply List.foldl_congr
  intro acc term hterm
  dsimp only [Function.comp_def]
  rw [MvPoly.coeff_eq_of_mem_terms p hterm]

/-- Use the cached term count to recognize zero without constructing a term list. -/
def initialInternal [One R] (p : MvPoly n R cmp) : MvPoly n R cmp :=
  if p.termCount == 0 then 0 else
    (mainVarInternal p).elim (MvPoly.C 1) (fun i => initialOfInternal i p)

/-- Compile the zero check to the cached term count. -/
@[csimp] theorem initial_eq_internal : @initial = @initialInternal := by
  funext n R cmp _ _ _ _ _ _ _ p
  unfold initial initialInternal
  rw [← mainVar_eq_internal, ← initialOf_eq_internal]
  have hempty : p.termsList.isEmpty = (p.termCount == 0) := by
    exact Std.ExtTreeMap.isEmpty_toList.trans Std.ExtTreeMap.isEmpty_eq_size_beq_zero
  rw [hempty]

end CharacteristicSet.Computable
