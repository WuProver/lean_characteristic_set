module

public import CharacteristicSet.Computable.Basic

/-! Executable prefix replacement on ordinary polynomial lists. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]

/-- Zero clears the list. Otherwise keep the consecutive prefix with strictly
smaller main variable and append `p`. Constants have no main variable, below
every variable. No ordering or triangularity of the input is assumed. -/
def takeConcat (ps : List (MvPoly n R cmp)) (p : MvPoly n R cmp) :
    List (MvPoly n R cmp) :=
  if p.termsList.isEmpty then [] else
    let v := mainVar p
    ps.takeWhile (fun q => match mainVar q, v with
      | none, some _ => true
      | some i, some j => decide (i < j)
      | _, _ => false) ++ [p]

@[simp] theorem takeConcat_zero (ps : List (MvPoly n R cmp)) :
    takeConcat ps 0 = [] := rfl

@[simp] theorem takeConcat_nil (p : MvPoly n R cmp) :
    takeConcat [] p = if p.termsList.isEmpty then [] else [p] := by
  simp [takeConcat]

/-- A nonzero inserted polynomial belongs to the complete output list. -/
theorem mem_takeConcat (ps : List (MvPoly n R cmp)) {p : MvPoly n R cmp}
    (hp : p ≠ 0) : p ∈ takeConcat ps p := by
  have h : p.termsList.isEmpty = false := by
    cases he : p.termsList with
    | nil => exact False.elim (hp (MvPoly.termsList_inj he))
    | cons a as => rfl
  simp [takeConcat, h]

/-- Every output polynomial other than the inserted one comes from the input. -/
theorem mem_of_mem_takeConcat {ps : List (MvPoly n R cmp)} {p q : MvPoly n R cmp}
    (hq : q ∈ takeConcat ps p) (hne : q ≠ p) : q ∈ ps := by
  unfold takeConcat at hq
  split at hq
  · simp at hq
  · have hmem := List.mem_append.mp hq
    cases hmem with
    | inl h => exact List.takeWhile_subset _ h
    | inr h => exact False.elim (hne (List.mem_singleton.mp h))

end CharacteristicSet.Computable
