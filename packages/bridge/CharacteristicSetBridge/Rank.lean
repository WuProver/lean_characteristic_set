module

public import CharacteristicSet.Computable.Rank
public import CharacteristicSetBridge.Basic
public import CharacteristicSetTheory.Rank

/-! Correspondence of executable ranks and their comparisons with Wu rank. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory
open scoped HexMvPolyTheory

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

/-- The interpretation equips the computed pair with the specification's lex order. -/
theorem rank_toMvPolynomial (p : MvPoly n R cmp) :
    (toMvPolynomial p).rank =
      toLex ((Computable.mainVar p : WithBot (Fin n)), Computable.mainDegree p) := by
  change ((toMvPolynomial p).vars.max, (toMvPolynomial p).mainDegree.card) =
    ((Computable.mainVar p : WithBot (Fin n)), Computable.mainDegree p)
  rw [mainVar_toMvPolynomial, mainDegree_toMvPolynomial]
  rfl

private theorem variableIndex_lt (i j : Option (Fin n)) :
    Computable.variableIndex i < Computable.variableIndex j ↔
      @LT.lt (WithBot (Fin n)) WithBot.instPreorder.toLT i j := by
  cases i with
  | none =>
    cases j with
    | none =>
      change 0 < 0 ↔ (⊥ : WithBot (Fin n)) < ⊥
      simp
    | some j =>
      change 0 < j.val + 1 ↔ (⊥ : WithBot (Fin n)) < (j : WithBot (Fin n))
      simp
  | some i =>
    cases j with
    | none =>
      change i.val + 1 < 0 ↔ (i : WithBot (Fin n)) < ⊥
      simp
    | some j =>
      change i.val + 1 < j.val + 1 ↔ (i : WithBot (Fin n)) < (j : WithBot (Fin n))
      rw [WithBot.coe_lt_coe]
      exact Nat.add_lt_add_iff_right

theorem compareRank_lt_iff (p q : MvPoly n R cmp) :
    Computable.compareRank p q = .lt ↔ (toMvPolynomial p).rank < (toMvPolynomial q).rank := by
  rw [← MvPolynomial.lt_def', MvPolynomial.lt_def,
    ← mainVar_toMvPolynomial, ← mainVar_toMvPolynomial,
    ← mainDegree_toMvPolynomial, ← mainDegree_toMvPolynomial,
    Computable.compareRank_lt_iff]
  exact or_congr (variableIndex_lt _ _) (and_congr
    ⟨Computable.variableIndex_injective, congrArg Computable.variableIndex⟩ Iff.rfl)

theorem compareRank_eq_iff (p q : MvPoly n R cmp) :
    Computable.compareRank p q = .eq ↔ (toMvPolynomial p).rank = (toMvPolynomial q).rank := by
  rw [Computable.compareRank_eq_iff, MvPolynomial.rank_eq_iff]
  simp only [Computable.rank, Prod.mk.injEq, ← mainVar_toMvPolynomial,
    ← mainDegree_toMvPolynomial]
  rfl

theorem compareRank_gt_iff (p q : MvPoly n R cmp) :
    Computable.compareRank p q = .gt ↔ (toMvPolynomial q).rank < (toMvPolynomial p).rank := by
  rw [Computable.compareRank_gt_iff, compareRank_lt_iff]

end CharacteristicSet.Bridge
