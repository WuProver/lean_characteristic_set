module

public import CharacteristicSetBridge.BasicSetCorrectness
public import CharacteristicSetTheory.BasicSet

/-! Basic-set interfaces whose data is computed by the Hex algorithms.
Correctness follows directly from invariants and rank minimality of the executable loops. -/

public section
namespace CharacteristicSet.Bridge
open Hex HexMvPolyTheory TriangularSet MvPolynomial
open scoped HexMvPolyTheory
variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

namespace Standard
variable (cmp) (l : List (MvPolynomial (Fin n) R))
private theorem basicSet_toList_equiv :
    basicSet (cmp := cmp) (basicSet (cmp := cmp) l).toList ≈ basicSet (cmp := cmp) l := by
  apply TriangularSet.equiv_of_le_of_ge
  · exact basicSet_minimal (cmp := cmp) _ (basicSet_isAscendingSet (cmp := cmp) l)
      (fun _ hp ↦ mem_toList_iff.mpr hp)
  · exact basicSet_minimal (cmp := cmp) l (basicSet_isAscendingSet (cmp := cmp) _)
      (fun _ hp ↦ basicSet_subset (cmp := cmp) l
        (mem_toList_iff.mp (basicSet_subset (cmp := cmp) _ hp)))

private theorem basicSet_ge_of_subset {l₁ l₂ : List (MvPolynomial (Fin n) R)}
    (h : l₁ ⊆ l₂) : basicSet (cmp := cmp) l₂ ≤ basicSet (cmp := cmp) l₁ :=
  basicSet_minimal (cmp := cmp) l₂ (basicSet_isAscendingSet (cmp := cmp) l₁)
    (fun _ hp ↦ h (basicSet_subset (cmp := cmp) l₁ hp))

private theorem basicSet_append_lt_of_exists_reducedToSet
    {l1 l2 : List (MvPolynomial (Fin n) R)}
    (h : ∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet (basicSet (cmp := cmp) l1)) :
    basicSet (cmp := cmp) (l2 ++ l1) < basicSet (cmp := cmp) l1 := by
  obtain ⟨p, hp1, hp2, hp3⟩ := h
  let S := (basicSet (cmp := cmp) l1).takeConcat p
  have hS1 : S.IsAscendingSet := isAscendingSet_takeConcat
    hp3 (basicSet_isAscendingSet (cmp := cmp) l1)
  have hS2 : S < basicSet (cmp := cmp) l1 := takeConcat_lt_of_reducedToSet hp2 hp3
  refine lt_of_le_of_lt (basicSet_minimal (cmp := cmp) _ hS1 fun q hq ↦ ?_) hS2
  refine List.mem_append.mpr <| or_iff_not_imp_left.mpr fun hmem ↦ ?_
  apply basicSet_subset (cmp := cmp) l1
  exact takeConcat_subset q hq (ne_of_mem_of_not_mem hp1 hmem).symm

/-- The standard basic set algorithm implements the basic set interface. -/
noncomputable def basicSetSpec : BasicSetSpec (Fin n) R where
  basicSet := basicSet (cmp := cmp)
  basicSet_subset := basicSet_subset (cmp := cmp)
  basicSet_toList_equiv := by exact basicSet_toList_equiv cmp
  basicSet_append_lt := by exact basicSet_append_lt_of_exists_reducedToSet cmp
  basicSet_ge_of_subset := by exact basicSet_ge_of_subset cmp
  initial_reduced := fun l _ hp hmax ↦
    initial_reducedToSet_of_max_vars_ne_bot' (basicSet_isAscendingSet (cmp := cmp) l) hp hmax

/-- On Hex inputs, the new specification returns the exact executable output. -/
theorem basicSetSpec_toList (ps : List (MvPoly n R cmp)) :
    ((basicSetSpec cmp).basicSet (ps.map toMvPolynomial)).toList =
      (Computable.Standard.basicSet ps).map toMvPolynomial := by
  change (Computable.Standard.basicSet
    ((ps.map toMvPolynomial).map (ofMvPolynomial (cmp := cmp)))).map toMvPolynomial = _
  simp [List.map_map, Function.comp_def]

end Standard

namespace Weak
variable (cmp) (l : List (MvPolynomial (Fin n) R))
private theorem basicSet_toList_equiv :
    basicSet (cmp := cmp) (basicSet (cmp := cmp) l).toList ≈ basicSet (cmp := cmp) l := by
  apply TriangularSet.equiv_of_le_of_ge
  · exact basicSet_minimal (cmp := cmp) _ (basicSet_isAscendingSet (cmp := cmp) l)
      (fun _ hp ↦ mem_toList_iff.mpr hp)
  · exact basicSet_minimal (cmp := cmp) l (basicSet_isAscendingSet (cmp := cmp) _)
      (fun _ hp ↦ basicSet_subset (cmp := cmp) l
        (mem_toList_iff.mp (basicSet_subset (cmp := cmp) _ hp)))

private theorem basicSet_ge_of_subset {l₁ l₂ : List (MvPolynomial (Fin n) R)}
    (h : l₁ ⊆ l₂) : basicSet (cmp := cmp) l₂ ≤ basicSet (cmp := cmp) l₁ :=
  basicSet_minimal (cmp := cmp) l₂ (basicSet_isAscendingSet (cmp := cmp) l₁)
    (fun _ hp ↦ h (basicSet_subset (cmp := cmp) l₁ hp))

private theorem basicSet_append_lt_of_exists_reducedToSet
    {l1 l2 : List (MvPolynomial (Fin n) R)}
    (h : ∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet (basicSet (cmp := cmp) l1)) :
    basicSet (cmp := cmp) (l2 ++ l1) < basicSet (cmp := cmp) l1 := by
  obtain ⟨p, hp1, hp2, hp3⟩ := h
  let S := (basicSet (cmp := cmp) l1).takeConcat p
  have hS1 : S.IsWeakAscendingSet := isWeakAscendingSet_takeConcat
    (initial_reducedToSet hp3) (basicSet_isAscendingSet (cmp := cmp) l1)
  have hS2 : S < basicSet (cmp := cmp) l1 := takeConcat_lt_of_reducedToSet hp2 hp3
  refine lt_of_le_of_lt (basicSet_minimal (cmp := cmp) _ hS1 fun q hq ↦ ?_) hS2
  refine List.mem_append.mpr <| or_iff_not_imp_left.mpr fun hmem ↦ ?_
  apply basicSet_subset (cmp := cmp) l1
  exact takeConcat_subset q hq (ne_of_mem_of_not_mem hp1 hmem).symm

/-- The weak basic set algorithm implements the basic set interface. -/
noncomputable def basicSetSpec : BasicSetSpec (Fin n) R where
  basicSet := basicSet (cmp := cmp)
  basicSet_subset := basicSet_subset (cmp := cmp)
  basicSet_toList_equiv := by exact basicSet_toList_equiv cmp
  basicSet_append_lt := by exact basicSet_append_lt_of_exists_reducedToSet cmp
  basicSet_ge_of_subset := by exact basicSet_ge_of_subset cmp
  initial_reduced := fun l _ hp hmax ↦
    initial_reducedToSet_of_max_vars_ne_bot_of_isWeakAscendingSet'
      (basicSet_isAscendingSet (cmp := cmp) l) hp hmax

/-- On Hex inputs, the new specification returns the exact executable output. -/
theorem basicSetSpec_toList (ps : List (MvPoly n R cmp)) :
    ((basicSetSpec cmp).basicSet (ps.map toMvPolynomial)).toList =
      (Computable.Weak.basicSet ps).map toMvPolynomial := by
  change (Computable.Weak.basicSet
    ((ps.map toMvPolynomial).map (ofMvPolynomial (cmp := cmp)))).map toMvPolynomial = _
  simp [List.map_map, Function.comp_def]

end Weak
end CharacteristicSet.Bridge
