/-
Copyright (c) 2026 The CharacteristicSet Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The CharacteristicSet Authors
-/
module

public import CharacteristicSet.Computable.CharacteristicSet
public import CharacteristicSetBridge.BasicSet
public import CharacteristicSetBridge.PseudoDivision
public import CharacteristicSetTheory.CharacteristicSet

/-! Termination and exact interpretation of the executable characteristic-set loop. -/

public section
namespace CharacteristicSet.Bridge
open Hex HexMvPolyTheory MvPolynomial TriangularSet
open scoped HexMvPolyTheory
variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Field R] [DecidableEq R]

private theorem zero_iff (p : MvPoly n R cmp) :
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

private theorem remainders_map (ps bs : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hbs : bs.map toMvPolynomial = S.toList) :
    ((((bs.foldl List.erase ps).map (fun p => Computable.setPseudoRem p bs)).filter
      (fun p => !p.termsList.isEmpty)).map toMvPolynomial) =
    (((ps.map toMvPolynomial) \ S.toList).map
      (fun p => (p.setPseudo S).remainder)).filter (· ≠ 0) := by
  have hd : (bs.foldl List.erase ps).map toMvPolynomial =
      (ps.map toMvPolynomial) \ S.toList := by
    rw [← List.diff_eq_foldl, List.map_diff toMvPolynomial_injective, hbs]
    rfl
  have hz : (fun p : MvPoly n R cmp => !p.termsList.isEmpty) =
      (fun p => decide (toMvPolynomial p ≠ 0)) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_true_eq, ne_eq]
    exact Bool.eq_false_iff.trans (not_congr (zero_iff p))
  rw [hz]
  rw [show (fun p : MvPoly n R cmp => decide (toMvPolynomial p ≠ 0)) =
    (fun p => decide (p ≠ 0)) ∘ toMvPolynomial from rfl, ← List.filter_map, List.map_map]
  have hm : (fun p : MvPoly n R cmp => toMvPolynomial (Computable.setPseudoRem p bs)) =
      (fun p => (toMvPolynomial p).setPseudo S |>.remainder) := by
    funext p
    exact setPseudoRem_eq_setPseudo_remainder p bs S hbs
  change List.filter _ (List.map (fun p => toMvPolynomial (Computable.setPseudoRem p bs)) _) = _
  rw [hm]
  congr 1
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (fun p => (p.setPseudo S).remainder)) hd

section Generic
variable (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
  (B : BasicSetSpec (Fin n) R)
  (hB : ∀ ps, (B.basicSet (ps.map toMvPolynomial)).toList = (basic ps).map toMvPolynomial)

include hB in
private theorem step_decreasing (original current next : List (MvPoly n R cmp))
    (h : Computable.characteristicSet.step basic original current = .inr next) :
    B.basicSet (next.map toMvPolynomial) < B.basicSet (current.map toMvPolynomial) := by
  unfold Computable.characteristicSet.step at h
  dsimp only at h
  split_ifs at h with hs
  cases h
  rw [List.map_append, List.map_append]
  rw [remainders_map _ _ (B.basicSet (current.map toMvPolynomial)) (hB current).symm,
    ← hB current]
  apply MvPolynomial.List.characteristicSetGo_decreasing B
    (original.map toMvPolynomial) (current.map toMvPolynomial) _ _ _ _ rfl rfl rfl
  intro he
  apply hs
  have hm := remainders_map current (basic current)
    (B.basicSet (current.map toMvPolynomial)) (hB current).symm
  rw [he] at hm
  exact List.map_eq_nil_iff.mp hm

include hB in
private theorem terminates (original : List (MvPoly n R cmp)) :
    WellFounded (fun next current =>
      Computable.characteristicSet.step basic original current = .inr next) := Subrelation.wf
    (fun h => step_decreasing basic B hB original _ _ h)
    (InvImage.wf (fun ps : List (MvPoly n R cmp) =>
      B.basicSet (ps.map toMvPolynomial)) wellFounded_lt)

include hB in
private theorem go_map
    (original current : List (MvPoly n R cmp)) :
    (Computable.characteristicSet.go basic original current).map toMvPolynomial =
      (MvPolynomial.List.characteristicSet.go B
        (original.map toMvPolynomial) (current.map toMvPolynomial)).toList := by
  induction current using
      (InvImage.wf (fun ps : List (MvPoly n R cmp) =>
        B.basicSet (ps.map toMvPolynomial)) wellFounded_lt).induction with
  | h current ih =>
    let bs := basic current
    let rs := ((bs.foldl List.erase current).map
      (fun p => Computable.setPseudoRem p bs)).filter (fun p => !p.termsList.isEmpty)
    let S := B.basicSet (current.map toMvPolynomial)
    let rems := (((current.map toMvPolynomial) \ S.toList).map
      (fun p => (p.setPseudo S).remainder)).filter (· ≠ 0)
    have hm : rs.map toMvPolynomial = rems := remainders_map current bs S (hB current).symm
    have hn : rs = [] ↔ rems = [] := by rw [← hm, List.map_eq_nil_iff]
    by_cases hr : rs = []
    · have ht := hn.mp hr
      have hs : Computable.characteristicSet.step basic original current = .inl bs := by
        unfold Computable.characteristicSet.step
        change (if rs = [] then Sum.inl bs else Sum.inr _) = _
        rw [ite_eq_left hr]
      rw [Computable.characteristicSet.go_done basic original current bs hs,
        MvPolynomial.List.characteristicSet.go]
      dsimp only [rems, S] at ht
      rw [dite_eq_left ht]
      exact (hB current).symm
    · have ht := (not_congr hn).mp hr
      have hs : Computable.characteristicSet.step basic original current =
          .inr (original ++ rs ++ bs) := by
        unfold Computable.characteristicSet.step
        change (if rs = [] then Sum.inl bs else Sum.inr _) = _
        rw [ite_eq_right hr]
      have hd := step_decreasing basic B hB original current _ hs
      rw [Computable.characteristicSet.go_next basic original current _ hs]
      conv_rhs => rw [MvPolynomial.List.characteristicSet.go]
      dsimp only [rems, S] at ht
      rw [dite_eq_right ht, ih _ hd]
      simp only [List.map_append, hm]
      rw [show bs.map toMvPolynomial = S.toList from (hB current).symm]

end Generic

namespace Standard
/-- Every run over a field terminates by strict descent of basic-set rank. -/
theorem characteristicSet_terminates (original : List (MvPoly n R cmp)) :
    WellFounded (fun next current =>
      Computable.characteristicSet.step Computable.Standard.basicSet
        original current = .inr next) :=
  terminates _ (basicSetSpec cmp) (basicSetSpec_toList cmp) original

/-- Exact ordered output, with the same coefficients as the theory algorithm. -/
theorem characteristicSet_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.Standard.characteristicSet ps).map toMvPolynomial =
      (MvPolynomial.List.characteristicSet (basicSetSpec cmp)
        (ps.map toMvPolynomial)).toList :=
  go_map _ (basicSetSpec cmp) (basicSetSpec_toList cmp) ps ps

private theorem theory_characteristicSet_ascending (ps : List (MvPoly n R cmp)) :
    (MvPolynomial.List.characteristicSet (basicSetSpec cmp)
      (ps.map toMvPolynomial)).IsAscendingSet := by
  obtain ⟨l, hl⟩ := MvPolynomial.List.characteristicSet_eq_basicSet
    (basicSetSpec cmp) (ps.map toMvPolynomial)
  rw [hl]
  exact basicSetSpec_isAscendingSet cmp l

/-- The executable result passes its corresponding ascending-set check. -/
theorem characteristicSet_check (ps : List (MvPoly n R cmp)) :
    Computable.Standard.isAscendingSet (Computable.Standard.characteristicSet ps) = true :=
  (isAscendingSet_iff_of_toList _ _ (characteristicSet_toMvPolynomial ps)).mpr
    (theory_characteristicSet_ascending ps)

/-- The actual output represents an ascending characteristic set: every input
has zero set remainder and every input zero is an output zero. -/
theorem characteristicSet_correct (K : Type*) [CommSemiring K] [Algebra R K]
    (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.Standard.characteristicSet ps).map toMvPolynomial = S.toList ∧
      S.IsAscendingSet ∧ S.IsCharacteristicSet K (ps.map toMvPolynomial) :=
  ⟨_, characteristicSet_toMvPolynomial ps, theory_characteristicSet_ascending ps,
    MvPolynomial.List.characteristicSet_isCharacteristicSet
      (basicSetSpec cmp) K (ps.map toMvPolynomial)⟩

end Standard

namespace Weak
/-- Every run over a field terminates by strict descent of basic-set rank. -/
theorem characteristicSet_terminates (original : List (MvPoly n R cmp)) :
    WellFounded (fun next current =>
      Computable.characteristicSet.step Computable.Weak.basicSet
        original current = .inr next) :=
  terminates _ (basicSetSpec cmp) (basicSetSpec_toList cmp) original

/-- Exact ordered output, with the same coefficients as the theory algorithm. -/
theorem characteristicSet_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.Weak.characteristicSet ps).map toMvPolynomial =
      (MvPolynomial.List.characteristicSet (basicSetSpec cmp)
        (ps.map toMvPolynomial)).toList :=
  go_map _ (basicSetSpec cmp) (basicSetSpec_toList cmp) ps ps

private theorem theory_characteristicSet_ascending (ps : List (MvPoly n R cmp)) :
    (MvPolynomial.List.characteristicSet (basicSetSpec cmp)
      (ps.map toMvPolynomial)).IsWeakAscendingSet := by
  obtain ⟨l, hl⟩ := MvPolynomial.List.characteristicSet_eq_basicSet
    (basicSetSpec cmp) (ps.map toMvPolynomial)
  rw [hl]
  exact basicSetSpec_isAscendingSet cmp l

/-- The executable result passes its corresponding ascending-set check. -/
theorem characteristicSet_check (ps : List (MvPoly n R cmp)) :
    Computable.Weak.isAscendingSet (Computable.Weak.characteristicSet ps) = true :=
  (isAscendingSet_iff_of_toList _ _ (characteristicSet_toMvPolynomial ps)).mpr
    (theory_characteristicSet_ascending ps)

/-- The actual output represents an ascending characteristic set: every input
has zero set remainder and every input zero is an output zero. -/
theorem characteristicSet_correct (K : Type*) [CommSemiring K] [Algebra R K]
    (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.Weak.characteristicSet ps).map toMvPolynomial = S.toList ∧
      S.IsWeakAscendingSet ∧ S.IsCharacteristicSet K (ps.map toMvPolynomial) :=
  ⟨_, characteristicSet_toMvPolynomial ps, theory_characteristicSet_ascending ps,
    MvPolynomial.List.characteristicSet_isCharacteristicSet
      (basicSetSpec cmp) K (ps.map toMvPolynomial)⟩

end Weak
end CharacteristicSet.Bridge
