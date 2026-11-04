/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSet.Computable.ZeroDecomposition
public import CharacteristicSetBridge.CharacteristicSet

/-! Termination and direct correctness of executable zero decomposition. -/

public section
namespace CharacteristicSet.Bridge
open Hex HexMvPolyTheory MvPolynomial TriangularSet
open scoped HexMvPolyTheory
variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Field R] [DecidableEq R]

private theorem mapM_some {α β : Type*} (xs : List α) (f : α → Option β) (g : α → β)
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, h x (by simp), ih (by simp_all)]

private theorem iUnion_map {α β γ : Type*} (xs : List α) (f : α → β) (g : β → Set γ) :
    (⋃ y ∈ xs.map f, g y) = ⋃ x ∈ xs, g (f x) := by
  ext z
  simp

private theorem nonconstant_iff (p : MvPoly n R cmp) :
    (Computable.mainVar p).isSome = true ↔ (toMvPolynomial p).vars.max ≠ ⊥ := by
  rw [← mainVar_toMvPolynomial]
  cases Computable.mainVar p <;> change _ ↔ _ ≠ (none : Option (Fin n)) <;> simp

section Generic
variable (basic : List (MvPoly n R cmp) → List (MvPoly n R cmp))
  (B : BasicSetSpec (Fin n) R) (D : PseudoDivisionSpec (Fin n) R)
  (hCS : ∀ ps : List (MvPoly n R cmp), (Computable.characteristicSet basic ps).map toMvPolynomial =
    (MvPolynomial.List.characteristicSet B D (ps.map toMvPolynomial)).toList)

include hCS in
private theorem branch_decreasing (ps : List (MvPoly n R cmp))
    (p : MvPoly n R cmp)
    (hp : p ∈ (Computable.characteristicSet basic ps).filter
      (fun p => (Computable.mainVar p).isSome)) :
    B.basicSet ((Computable.initial p :: Computable.characteristicSet basic ps ++ ps).map
      toMvPolynomial) < B.basicSet (ps.map toMvPolynomial) := by
  let l := ps.map toMvPolynomial
  let CS := l.characteristicSet B D
  have hp' : toMvPolynomial p ∈ CS := mem_toList_iff.mp
    ((hCS ps) ▸ List.mem_map_of_mem (List.mem_filter.mp hp).1)
  have hm := (nonconstant_iff p).mp (List.mem_filter.mp hp).2
  rw [List.map_append, List.map_cons, initial_toMvPolynomial, hCS ps]
  apply lt_of_le_of_lt (B.basicSet_ge_of_subset (List.subset_append_left _ l))
  apply lt_of_lt_of_le ?_ (le_trans (l.cs_toList_le B D) (l.cs_le_basicSet B D))
  exact B.basicSet_cons_lt (initial_ne_zero (ne_zero_of_mem hp'))
    (B.reducedToSet_basicSet (l.cs_initial_reduced B D _ hp' hm))

include hCS in
/-- Initial branching terminates by the same rank descent as the theory algorithm. -/
theorem zeroDecomposition_terminates : WellFounded (fun (next ps : List (MvPoly n R cmp)) =>
    ∃ p ∈ (Computable.characteristicSet basic ps).filter
      (fun p => (Computable.mainVar p).isSome),
      next = Computable.initial p :: Computable.characteristicSet basic ps ++ ps) := by
  apply Subrelation.wf (r := fun next ps =>
    B.basicSet (next.map toMvPolynomial) < B.basicSet (ps.map toMvPolynomial))
  · rintro next ps ⟨p, hp, rfl⟩
    exact branch_decreasing basic B D hCS ps p hp
  · exact InvImage.wf (fun ps : List (MvPoly n R cmp) =>
      B.basicSet (ps.map toMvPolynomial)) wellFounded_lt

include hCS in
private theorem run_map (ps : List (MvPoly n R cmp)) :
    Computable.zeroDecomposition.run basic ps = some (Computable.zeroDecomposition basic ps) ∧
    (Computable.zeroDecomposition basic ps).map (List.map toMvPolynomial) =
      (MvPolynomial.List.zeroDecomposition B D (ps.map toMvPolynomial)).map
        TriangularSet.toList := by
  induction ps using (zeroDecomposition_terminates basic B D hCS).induction with
  | h ps ih =>
    let cs := Computable.characteristicSet basic ps
    let xs := cs.filter (fun p => (Computable.mainVar p).isSome)
    let child := fun p => Computable.initial p :: cs ++ ps
    have hi : ∀ p ∈ xs, Computable.zeroDecomposition.run basic (child p) =
        some (Computable.zeroDecomposition basic (child p)) :=
      fun p hp => (ih _ ⟨p, hp, rfl⟩).1
    have he : Computable.zeroDecomposition basic ps =
        cs :: xs.flatMap (fun p => Computable.zeroDecomposition basic (child p)) := by
      unfold Computable.zeroDecomposition
      rw [Computable.zeroDecomposition.run, mapM_some xs _ _ hi]
      rfl
    refine ⟨?_, ?_⟩
    · rw [Computable.zeroDecomposition.run, mapM_some xs _ _ hi, he]
      rfl
    · let S := MvPolynomial.List.characteristicSet B D (ps.map toMvPolynomial)
      have hout : cs.map toMvPolynomial = S.toList := hCS ps
      have hm : xs.map toMvPolynomial = S.toList.filter (fun p => p.vars.max ≠ ⊥) := by
        rw [← hout, List.filter_map]
        congr 1
        apply List.filter_congr
        intro p hp
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, decide_eq_true_eq, nonconstant_iff]
      rw [he, List.map_cons, hout]
      conv_rhs => rw [MvPolynomial.List.zeroDecomposition]
      simp only [List.map_cons]
      congr 1
      simp only [List.map_flatMap, List.map_flatten, List.map_map]
      simp only [Function.comp_def]
      change xs.flatMap _ =
        ((S.toList.filter (fun p => p.vars.max ≠ ⊥)).attach.map
          (fun p => List.map TriangularSet.toList
            (MvPolynomial.List.zeroDecomposition B D
              (p.val.initial :: S.toList ++ ps.map toMvPolynomial)))).flatten
      rw [List.attach_map_val (f := fun p : MvPolynomial (Fin n) R =>
        List.map TriangularSet.toList (MvPolynomial.List.zeroDecomposition B D
          (p.initial :: S.toList ++ ps.map toMvPolynomial)))]
      rw [← hm, List.map_map, ← List.flatMap_def]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro p hp
      simpa only [child, List.map_append, List.map_cons, initial_toMvPolynomial, hCS ps,
        Function.comp_apply] using (ih _ ⟨p, hp, rfl⟩).2

include hCS in
/-- Interpretation commutes with zero decomposition, preserving component and polynomial order. -/
theorem zeroDecomposition_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.zeroDecomposition basic ps).map (List.map toMvPolynomial) =
      (MvPolynomial.List.zeroDecomposition B D (ps.map toMvPolynomial)).map
        TriangularSet.toList := (run_map basic B D hCS ps).2

include hCS in
/-- The internal executor always returns a result over a field. -/
theorem zeroDecomposition_run_eq_some (ps : List (MvPoly n R cmp)) :
    Computable.zeroDecomposition.run basic ps = some (Computable.zeroDecomposition basic ps) :=
  (run_map basic B D hCS ps).1
include hCS in
/-- The zero-set equality follows by transporting the theory theorem along interpretation. -/
theorem zeroDecomposition_correct (K : Type*) [Field K] [Algebra R K]
    (ps : List (MvPoly n R cmp)) :
    vanishingSet K (ps.map toMvPolynomial) =
      ⋃ cs ∈ Computable.zeroDecomposition basic ps,
        vanishingSet K (cs.map toMvPolynomial) \
          vanishingSet' K (initialProd (cs.map toMvPolynomial).toFinset) := by
  have he := congrArg (fun ls : List (List (MvPolynomial (Fin n) R)) =>
    ⋃ qs ∈ ls, vanishingSet K qs \ vanishingSet' K (initialProd qs.toFinset))
    (zeroDecomposition_toMvPolynomial basic B D hCS ps)
  have ht := MvPolynomial.List.vanishingSet_eq_zeroDecomposition_union B D K
    (ps.map toMvPolynomial)
  refine ht.trans ?_
  have hf (S : TriangularSet (Fin n) R) : S.toList.toFinset = S.toFinset := by
    ext p
    simp [mem_toList_iff]
  have hv (S : TriangularSet (Fin n) R) : vanishingSet K S.toList = vanishingSet K S := by
    ext x
    simp only [vanishingSet, Set.mem_ofPred_eq, mem_toList_iff]
  rw [iUnion_map, iUnion_map] at he
  simpa only [hv, hf] using he.symm

end Generic

namespace Standard
/-- Interpretation commutes with the executable zero decomposition. -/
theorem zeroDecomposition_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.Standard.zeroDecomposition ps).map (List.map toMvPolynomial) =
      (MvPolynomial.List.zeroDecomposition (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
        (ps.map toMvPolynomial)).map TriangularSet.toList :=
  Bridge.zeroDecomposition_toMvPolynomial _ (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
    characteristicSet_toMvPolynomial ps

/-- Every recursive initial branch terminates over a field. -/
theorem zeroDecomposition_terminates : WellFounded (fun (next ps : List (MvPoly n R cmp)) =>
    ∃ p ∈ (Computable.Standard.characteristicSet ps).filter
      (fun p => (Computable.mainVar p).isSome),
      next = Computable.initial p :: Computable.Standard.characteristicSet ps ++ ps) :=
  Bridge.zeroDecomposition_terminates _ (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
    characteristicSet_toMvPolynomial
/-- The actual output decomposes exactly the input zero set. -/
theorem zeroDecomposition_correct (K : Type*) [Field K] [Algebra R K]
    (ps : List (MvPoly n R cmp)) :
    vanishingSet K (ps.map toMvPolynomial) =
      ⋃ cs ∈ Computable.Standard.zeroDecomposition ps,
        vanishingSet K (cs.map toMvPolynomial) \
          vanishingSet' K (initialProd (cs.map toMvPolynomial).toFinset) :=
  Bridge.zeroDecomposition_correct _ (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
    characteristicSet_toMvPolynomial K ps

end Standard

namespace Weak
/-- Interpretation commutes with the executable zero decomposition. -/
theorem zeroDecomposition_toMvPolynomial (ps : List (MvPoly n R cmp)) :
    (Computable.Weak.zeroDecomposition ps).map (List.map toMvPolynomial) =
      (MvPolynomial.List.zeroDecomposition (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
        (ps.map toMvPolynomial)).map TriangularSet.toList :=
  Bridge.zeroDecomposition_toMvPolynomial _ (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
    characteristicSet_toMvPolynomial ps

/-- Every recursive initial branch terminates over a field. -/
theorem zeroDecomposition_terminates : WellFounded (fun (next ps : List (MvPoly n R cmp)) =>
    ∃ p ∈ (Computable.Weak.characteristicSet ps).filter
      (fun p => (Computable.mainVar p).isSome),
      next = Computable.initial p :: Computable.Weak.characteristicSet ps ++ ps) :=
  Bridge.zeroDecomposition_terminates _ (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
    characteristicSet_toMvPolynomial
/-- The actual output decomposes exactly the input zero set. -/
theorem zeroDecomposition_correct (K : Type*) [Field K] [Algebra R K]
    (ps : List (MvPoly n R cmp)) :
    vanishingSet K (ps.map toMvPolynomial) =
      ⋃ cs ∈ Computable.Weak.zeroDecomposition ps,
        vanishingSet K (cs.map toMvPolynomial) \
          vanishingSet' K (initialProd (cs.map toMvPolynomial).toFinset) :=
  Bridge.zeroDecomposition_correct _ (basicSetSpec cmp) (setRemainderSpec (cmp := cmp))
    characteristicSet_toMvPolynomial K ps

end Weak

end CharacteristicSet.Bridge
