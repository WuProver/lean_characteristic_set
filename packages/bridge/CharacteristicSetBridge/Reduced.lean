module

public import CharacteristicSet.Computable.Reduced
public import CharacteristicSetBridge.Basic
public import CharacteristicSetTheory.Reduced

/-! Correctness of executable reduction checks, including represented triangular sets. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory
open scoped HexMvPolyTheory

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

private theorem reduced_termsList_isEmpty_iff (p : MvPoly n R cmp) :
    p.termsList.isEmpty = true ↔ toMvPolynomial p = 0 := by
  rw [List.isEmpty_iff]
  constructor
  · intro h
    have hp : p = 0 := MvPoly.termsList_inj h
    simp [hp]
  · intro h
    have hp : p = 0 := toMvPolynomial_injective (by simpa using h)
    subst p
    rfl

/-- Exact agreement with reduction in the divisor's main variable, over any
commutative semiring, including the trivial one. -/
theorem reducedTo_iff (q p : MvPoly n R cmp) :
    Computable.reducedTo q p = true ↔
      (toMvPolynomial q).reducedTo (toMvPolynomial p) := by
  unfold Computable.reducedTo MvPolynomial.reducedTo
  simp only [reduced_termsList_isEmpty_iff]
  split_ifs with hq
  · simp
  · rw [← mainVar_toMvPolynomial]
    cases Computable.mainVar p with
    | none => simp
    | some i => simp

/-- Plain lists correspond to the universal theory relation without any
triangularity, ordering or distinctness assumption. -/
theorem reducedToSet_iff (q : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) :
    Computable.reducedToSet q ps = true ↔
      (toMvPolynomial q).reducedToSet (ps.map toMvPolynomial) := by
  simp only [Computable.reducedToSet, List.all_eq_true, MvPolynomial.reducedToSet, List.mem_map]
  constructor
  · intro h p hp
    rcases hp with ⟨f, hf, rfl⟩
    exact (reducedTo_iff q f).mp (h f hf)
  · intro h f hf
    exact (reducedTo_iff q f).mpr (h _ ⟨f, hf, rfl⟩)

/-- Checking a list representing a triangular set is precisely reduction to that set. -/
theorem reducedToSet_iff_of_toList (q : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    Computable.reducedToSet q ps = true ↔ (toMvPolynomial q).reducedToSet S := by
  rw [reducedToSet_iff, hps]
  simp only [MvPolynomial.reducedToSet, TriangularSet.mem_toList_iff]

end CharacteristicSet.Bridge
