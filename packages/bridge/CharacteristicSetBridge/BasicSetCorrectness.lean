module

public import CharacteristicSetBridge.AscendingSet

/-! Correctness of the executable basic-set loops.

The standard and weak proofs follow the original theory separately: structure and
input containment, rank decrease, then greedy minimality by comparing prefixes.
`basicSet` only interprets the executable output as a triangular set. The spec
consequences are derived in `BasicSet`, as in the original theory.
-/

public section
namespace CharacteristicSet.Bridge
open Hex HexMvPolyTheory MvPolynomial TriangularSet
open scoped HexMvPolyTheory
variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommSemiring R] [DecidableEq R]

private theorem standard_filter (ps bs : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hbs : bs.map toMvPolynomial = S.toList) :
    (ps.filter (fun p => Computable.reducedToSet p bs)).map toMvPolynomial =
      (ps.map toMvPolynomial).filter (fun p => decide (p.reducedToSet S)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact reducedToSet_iff_of_toList p bs S hbs

private theorem weak_filter (ps bs : List (MvPoly n R cmp)) (b : MvPoly n R cmp)
    (S : TriangularSet (Fin n) R) (hbs : bs.map toMvPolynomial = S.toList) :
    (ps.filter (Computable.Weak.accepts b bs)).map toMvPolynomial =
      (ps.map toMvPolynomial).filter (fun p => decide
        ((toMvPolynomial b).vars.max < p.vars.max ∧ p.initial.reducedToSet S)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  apply Bool.eq_iff_iff.mpr
  simp only [Computable.Weak.accepts, Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  rw [mainVar_lt_iff, reducedToSet_iff_of_toList _ _ S hbs, initial_toMvPolynomial]

private theorem candidates_mem (ps : List (MvPoly n R cmp)) (p : MvPolynomial (Fin n) R) :
    p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial ↔
      p ∈ ps.map toMvPolynomial ∧ p ≠ 0 := by
  rw [basicSetCandidates_toMvPolynomial]
  simp

private theorem candidates_sorted (ps : List (MvPoly n R cmp)) :
    ((Computable.basicSetCandidates ps).map toMvPolynomial).Pairwise (· ≤ ·) := by
  rw [basicSetCandidates_toMvPolynomial]
  exact List.Pairwise.filter _ ((ps.map toMvPolynomial).pairwise_mergeSort' (· ≤ ·))

namespace Standard

/-- The executable loop preserves ascending structure and input containment,
independently of the rank-minimality argument. -/
private theorem go_structure (ps bs : List (MvPoly n R cmp)) :
    ∀ (S : TriangularSet (Fin n) R), bs.map toMvPolynomial = S.toList →
    (∀ p ∈ ps.map toMvPolynomial, p ≠ 0) →
    (∀ p ∈ ps.map toMvPolynomial, p.reducedToSet S) → S.IsAscendingSet →
    ∃ T : TriangularSet (Fin n) R,
      (Computable.Standard.basicSet.go ps bs).map toMvPolynomial = T.toList ∧
      T.IsAscendingSet ∧ (∀ p ∈ T, p ∈ S ∨ p ∈ ps.map toMvPolynomial) := by
  induction ps, bs using Computable.basicSet.go.induct with
  | case1 bs =>
    intro S hbs _ _ hS
    exact ⟨S, by simpa [Computable.Standard.basicSet.go, Computable.basicSet.go] using hbs,
      hS, fun _ hp => Or.inl hp⟩
  | case2 bs b tail bsNext ih =>
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S hbs hnz hred hS
    let B := toMvPolynomial b
    let S' := S.takeConcat B
    have hr : B.reducedToSet S := hred B (by simp [B])
    have ht := takeConcat_toMvPolynomial bs b S hbs
    have hf := standard_filter tail (Computable.takeConcat bs b) S' ht
    have hn : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p ≠ 0 := by
      intro p hp
      rw [hf] at hp
      exact hnz p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))
    have hr' : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p.reducedToSet S' := by
      intro p hp
      rw [hf] at hp
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    obtain ⟨T, ho, ha, hm⟩ := ih S' ht hn hr' (isAscendingSet_takeConcat hr hS)
    refine ⟨T, ?_, ha, ?_⟩
    · simpa only [Computable.Standard.basicSet.go, Computable.basicSet.go] using ho
    intro p hp
    rcases hm p hp with hp | hp
    · by_cases he : p = B
      · exact Or.inr (by simp [he, B])
      · exact Or.inl (takeConcat_subset p hp he)
    · rw [hf] at hp
      exact Or.inr (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))

/-- Rank decrease does not require an ascending accumulator. -/
private theorem go_le (ps bs : List (MvPoly n R cmp)) :
    ∀ (S U : TriangularSet (Fin n) R), bs.map toMvPolynomial = S.toList →
    (∀ p ∈ ps.map toMvPolynomial, p ≠ 0) →
    (∀ p ∈ ps.map toMvPolynomial, p.reducedToSet S) →
    (Computable.Standard.basicSet.go ps bs).map toMvPolynomial = U.toList → U ≤ S := by
  induction ps, bs using Computable.basicSet.go.induct with
  | case1 bs =>
    intro S U hbs _ _ ho
    simp only [Computable.Standard.basicSet.go, Computable.basicSet.go] at ho
    exact le_of_eq (toList_eq_iff_eq.mp (ho.symm.trans hbs))
  | case2 bs b tail bsNext ih =>
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S U hbs hnz hred ho
    let B := toMvPolynomial b
    let S' := S.takeConcat B
    have hb : B ≠ 0 := hnz B (by simp [B])
    have hr : B.reducedToSet S := hred B (by simp [B])
    have ht := takeConcat_toMvPolynomial bs b S hbs
    have hf := standard_filter tail (Computable.takeConcat bs b) S' ht
    have hn : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p ≠ 0 := by
      intro p hp
      rw [hf] at hp
      exact hnz p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))
    have hr' : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p.reducedToSet S' := by
      intro p hp
      rw [hf] at hp
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    have hle := ih S' U ht hn hr'
      (by simpa only [Computable.Standard.basicSet.go, Computable.basicSet.go] using ho)
    exact le_trans hle (le_of_lt (takeConcat_lt_of_reducedToSet hb hr))

/-- Greedy rank minimality, proved by induction on the executable loop itself. -/
private theorem go_minimal (ps bs : List (MvPoly n R cmp)) :
    ∀ (S : TriangularSet (Fin n) R), bs.map toMvPolynomial = S.toList →
    (∀ p ∈ ps.map toMvPolynomial, p ≠ 0) →
    (∀ p ∈ ps.map toMvPolynomial, S.CanConcat p) →
    (∀ p ∈ ps.map toMvPolynomial, p.reducedToSet S) →
    (ps.map toMvPolynomial).Pairwise (· ≤ ·) →
    ∀ T : TriangularSet (Fin n) R, T.IsAscendingSet →
    (S.length ≤ T.length ∧ ∀ i < S.length, S i ≈ T i) →
    (∀ p ∈ T, (∀ i < S.length, ¬ S i ≈ p) → p ∈ ps.map toMvPolynomial) →
    ∀ U : TriangularSet (Fin n) R,
    (Computable.Standard.basicSet.go ps bs).map toMvPolynomial = U.toList → U ≤ T := by
  induction ps, bs using Computable.basicSet.go.induct with
  | case1 bs =>
    intro S hbs _ _ _ _ T _ _ hmem U ho
    simp only [Computable.Standard.basicSet.go, Computable.basicSet.go] at ho
    have he : U = S := toList_eq_iff_eq.mp (ho.symm.trans hbs)
    rw [he]
    apply ge_of_forall_equiv
    intro i hi
    simpa using hmem _ (apply_mem hi)
  | case2 bs b tail bsNext ih =>
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S hbs hnz hcan hred hsort T hT ⟨hlen, hequiv⟩ hmem U ho
    let B := toMvPolynomial b
    let S' := S.takeConcat B
    have hb : S.CanConcat B := hcan B (by simp [B])
    have heq : S' = S.concat B := takeConcat_eq_concat_of_canConcat hb
    have hBmin : ∀ ⦃q⦄, q ∈ (b :: tail).map toMvPolynomial → B ≤ q :=
      fun _ => List.Pairwise.rel_head hsort
    have hr : B.reducedToSet S := hred B (by simp [B])
    by_cases hL : T.length = S.length
    · have he : S ≈ T := equiv_iff'.mpr ⟨hL.symm, hequiv⟩
      exact le_trans (go_le _ _ S U hbs hnz hred ho) (equiv_def''.mp he).1
    have hL : S.length < T.length := Nat.lt_of_le_of_ne hlen (Ne.symm hL)
    have hBq : B ≤ T S.length := by
      apply hBmin
      apply hmem _ (apply_mem hL)
      intro i hi
      apply not_antisymmRel_of_lt
      rw [AntisymmRel.lt_congr_left (hequiv i hi)]
      exact apply_lt_of_index_lt hL hi
    have ht := takeConcat_toMvPolynomial bs b S hbs
    have hf := standard_filter tail (Computable.takeConcat bs b) S' ht
    have hn : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p ≠ 0 := by
      intro p hp
      rw [hf] at hp
      exact hnz p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))
    have hr' : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, p.reducedToSet S' := by
      intro p hp
      rw [hf] at hp
      exact of_decide_eq_true (List.mem_filter.mp hp).2
    have ho' : (Computable.Standard.basicSet.go
        (tail.filter (fun p => Computable.reducedToSet p (Computable.takeConcat bs b)))
        (Computable.takeConcat bs b)).map toMvPolynomial = U.toList := by
      simpa only [Computable.Standard.basicSet.go, Computable.basicSet.go] using ho
    rcases le_iff_lt_or_equiv.mp hBq with hlt | he
    · have hlt' : S' < T := by
        rw [heq]
        apply TriangularSet.lt_def.mpr
        refine Or.inl ⟨S.length, S.length_concat _ ▸ lt_add_one _, ?_, fun i hi => ?_⟩
        · simpa [concat_apply] using hlt
        rw [concat_apply, ite_eq_left hi]
        exact hequiv i hi
      exact le_trans (go_le _ _ S' U ht hn hr' ho') (le_of_lt hlt')
    have hc : ∀ p ∈ (tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial, S'.CanConcat p := by
      intro p hp
      have hp0 := hn p hp
      have hpr := hr' p hp
      rw [hf] at hp
      refine ⟨hp0, fun _ => ?_⟩
      have h := hpr B (by rw [heq]; exact mem_concat hb)
      rw [heq]
      simp only [concat_apply, length_concat, add_tsub_cancel_right,
        lt_self_iff_false, ↓reduceIte]
      exact max_vars_lt_of_reducedTo_of_le hp0
        (hBmin (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))) h
    have hsrt : ((tail.filter (fun p => Computable.reducedToSet p
        (Computable.takeConcat bs b))).map toMvPolynomial).Pairwise (· ≤ ·) := by
      rw [hf]
      exact List.Pairwise.filter _ (List.Pairwise.of_cons hsort)
    refine ih S' ht hn hc hr' hsrt T hT ⟨?_, ?_⟩ ?_ U ho'
    · rw [heq, length_concat]
      exact hL
    · intro i hi
      simp only [heq, length_concat, concat_apply] at hi ⊢
      split_ifs with hi1 hi2
      · exact hequiv i hi1
      · exact hi2 ▸ he
      · omega
    intro p hp hp2
    have hp2' : ¬ B ≈ p ∧ ∀ i < S.length, ¬ S i ≈ p := by
      simp only [heq, length_concat, concat_apply] at hp2
      constructor
      · simpa using hp2 S.length (lt_add_one _)
      · intro i hi
        simpa [hi] using hp2 i (Nat.lt_add_right 1 hi)
    rw [hf, List.mem_filter, decide_eq_true_eq]
    have hpmem := hmem p hp hp2'.2
    have htail : p ∈ tail.map toMvPolynomial := by
      rcases List.mem_cons.mp hpmem with heq | hm
      · exact False.elim (hp2'.1 (heq ▸ refl _))
      · exact hm
    refine ⟨htail, MvPolynomial.reducedToSet_iff.mpr fun i hi => ?_⟩
    rcases hp with ⟨k, hk1, hk2⟩
    have hk3 : S.length < k := by
      by_contra hn
      rcases lt_or_eq_of_le (le_of_not_gt hn) with hki | hki
      · exact hp2'.2 k hki (hk2 ▸ hequiv k hki)
      · exact hp2'.1 (by rw [← hk2, hki]; exact he)
    rw [← hk2, heq, concat_apply]
    split_ifs with hi1 hi2
    · exact (reducedTo_congr_right (hequiv i hi1)).mpr (hT (lt_trans hi1 hk3) hk1)
    · exact (reducedTo_congr_right he).mpr (hT hk3 hk1)
    · rw [heq, length_concat] at hi
      omega

private theorem output_structure (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.Standard.basicSet ps).map toMvPolynomial = S.toList ∧
      S.IsAscendingSet ∧ (∀ p ∈ S, p ∈ ps.map toMvPolynomial) := by
  have hn : ∀ p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial, p ≠ 0 :=
    fun p hp => ((candidates_mem ps p).mp hp).2
  obtain ⟨S, ho, ha, hm⟩ := go_structure (Computable.basicSetCandidates ps) [] ∅
    (by simp) hn (fun _ _ p hp => False.elim (notMem_empty p hp)) isAscendingSet_empty
  refine ⟨S, ho, ha, ?_⟩
  · intro p hp
    rcases hm p hp with hp | hp
    · exact False.elim (notMem_empty p hp)
    · exact ((candidates_mem ps p).mp hp).1

/-- Interpret the executable algorithm, adding only proofs of triangularity. -/
@[expose] noncomputable def basicSet (l : List (MvPolynomial (Fin n) R)) :
    TriangularSet (Fin n) R where
  toList := (Computable.Standard.basicSet
    (l.map (ofMvPolynomial (cmp := cmp)))).map toMvPolynomial
  zero_notMem' := by
    obtain ⟨S, ho, _⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
    rw [ho]
    exact S.zero_notMem_toList
  isChain_max_vars' := by
    obtain ⟨S, ho, _⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
    rw [ho]
    exact S.toList_isChain

theorem basicSet_isAscendingSet (l : List (MvPolynomial (Fin n) R)) :
    (basicSet (cmp := cmp) l).IsAscendingSet := by
  obtain ⟨S, ho, ha, _⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
  have he : basicSet (cmp := cmp) l = S := toList_eq_iff_eq.mp ho
  exact he ▸ ha

theorem basicSet_subset (l : List (MvPolynomial (Fin n) R)) :
    ∀ ⦃p⦄, p ∈ basicSet (cmp := cmp) l → p ∈ l := by
  obtain ⟨S, ho, _, hs⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
  have he : basicSet (cmp := cmp) l = S := toList_eq_iff_eq.mp ho
  simpa [he, List.map_map, Function.comp_def] using hs

/-- Rank minimality follows the original theory's greedy prefix comparison. -/
theorem basicSet_minimal (l : List (MvPolynomial (Fin n) R))
    {S : TriangularSet (Fin n) R} (hS : S.IsAscendingSet)
    (hsub : ∀ ⦃p⦄, p ∈ S → p ∈ l) : basicSet (cmp := cmp) l ≤ S := by
  let ps := l.map (ofMvPolynomial (cmp := cmp))
  have hn : ∀ p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial, p ≠ 0 :=
    fun p hp => ((candidates_mem ps p).mp hp).2
  apply go_minimal (Computable.basicSetCandidates ps) [] ∅ (by simp) hn
    (fun p hp => empty_canConcat (hn p hp))
    (fun _ _ p hp => False.elim (notMem_empty p hp)) (candidates_sorted ps)
    S hS (by simp) _ (basicSet (cmp := cmp) l) rfl
  intro p hp _
  exact (candidates_mem ps p).mpr ⟨by simpa [ps, List.map_map, Function.comp_def] using hsub hp,
    ne_zero_of_mem hp⟩

/-- The executable output is an ascending subset of the input and is rank-minimal
among all standard ascending subsets of that input. -/
theorem output_spec (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.Standard.basicSet ps).map toMvPolynomial = S.toList ∧
      S.IsAscendingSet ∧ (∀ p ∈ S, p ∈ ps.map toMvPolynomial) ∧
      (∀ T : TriangularSet (Fin n) R, T.IsAscendingSet →
        (∀ p ∈ T, p ∈ ps.map toMvPolynomial) → S ≤ T) := by
  let S := basicSet (cmp := cmp) (ps.map toMvPolynomial)
  have ho : (Computable.Standard.basicSet ps).map toMvPolynomial = S.toList := by
    simp [S, basicSet, List.map_map, Function.comp_def]
  exact ⟨S, ho, basicSet_isAscendingSet _,
    fun _ hp => basicSet_subset _ hp, fun T hT hs => basicSet_minimal _ hT (fun _ hp => hs _ hp)⟩

omit [DecidableEq R] in
/-- Every output passes the standard executable ascending-set check. -/
theorem basicSet_check (ps : List (MvPoly n R cmp)) :
    Computable.Standard.isAscendingSet (Computable.Standard.basicSet ps) = true := by
  classical
  obtain ⟨S, ho, ha, _⟩ := output_structure ps
  exact (isAscendingSet_iff_of_toList _ S ho).mpr ha

end Standard

namespace Weak

/-- Direct invariant proof for the weak executable loop, including the explicit
main-variable condition needed to extend a triangular accumulator. -/
private theorem go_structure (ps bs : List (MvPoly n R cmp)) :
    ∀ (S : TriangularSet (Fin n) R), bs.map toMvPolynomial = S.toList →
    (∀ p ∈ ps.map toMvPolynomial, p ≠ 0) →
    (∀ p ∈ ps.map toMvPolynomial, S.CanConcat p) →
    (∀ p ∈ ps.map toMvPolynomial, p.initial.reducedToSet S) → S.IsWeakAscendingSet →
    ∃ T : TriangularSet (Fin n) R,
      (Computable.Weak.basicSet.go ps bs).map toMvPolynomial = T.toList ∧
      T.IsWeakAscendingSet ∧ (∀ p ∈ T, p ∈ S ∨ p ∈ ps.map toMvPolynomial) := by
  induction ps, bs using Computable.Weak.basicSet.go.induct with
  | case1 bs =>
    intro S hbs _ _ _ hS
    exact ⟨S, by simpa [Computable.Weak.basicSet.go] using hbs,
      hS, fun _ hp => Or.inl hp⟩
  | case2 bs b tail bsNext ih =>
    dsimp only [bsNext] at ih
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S hbs hnz hcan hred hS
    let B := toMvPolynomial b
    have hb : S.CanConcat B := hcan B (by simp [B])
    let S' := S.concat B
    have hr : B.initial.reducedToSet S := hred B (by simp [B])
    have ht : (bs ++ [b]).map toMvPolynomial = S'.toList := by
      simp [S', B, List.map_append, hbs, toList_concat hb, List.concat_eq_append]
    have hf := weak_filter tail (bs ++ [b]) b S' ht
    have hn : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        p ≠ 0 := by
      intro p hp
      rw [hf] at hp
      exact hnz p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))
    have hc : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        S'.CanConcat p := by
      intro p hp
      have hp0 := hn p hp
      rw [hf] at hp
      have hlt := (of_decide_eq_true (List.mem_filter.mp hp).2).1
      exact ⟨hp0, fun _ => by simpa [S', length_concat, concat_apply] using hlt⟩
    have hr' : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        p.initial.reducedToSet S' := by
      intro p hp
      rw [hf] at hp
      exact (of_decide_eq_true (List.mem_filter.mp hp).2).2
    obtain ⟨T, ho, ha, hm⟩ := ih S' ht hn hc hr' (isWeakAscendingSet_concat hb hr hS)
    refine ⟨T, ?_, ha, ?_⟩
    · simpa only [Computable.Weak.basicSet.go] using ho
    intro p hp
    rcases hm p hp with hp | hp
    · rcases (mem_concat_iff hb).mp hp with he | hp
      · exact Or.inr (by simp [he, B])
      · exact Or.inl hp
    · rw [hf] at hp
      exact Or.inr (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))

/-- Rank decrease does not require an ascending accumulator. -/
private theorem go_le (ps bs : List (MvPoly n R cmp)) :
    ∀ (S U : TriangularSet (Fin n) R), bs.map toMvPolynomial = S.toList →
    (∀ p ∈ ps.map toMvPolynomial, S.CanConcat p) →
    (Computable.Weak.basicSet.go ps bs).map toMvPolynomial = U.toList → U ≤ S := by
  induction ps, bs using Computable.Weak.basicSet.go.induct with
  | case1 bs =>
    intro S U hbs _ ho
    simp only [Computable.Weak.basicSet.go] at ho
    exact le_of_eq (toList_eq_iff_eq.mp (ho.symm.trans hbs))
  | case2 bs b tail bsNext ih =>
    dsimp only [bsNext] at ih
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S U hbs hcan ho
    let B := toMvPolynomial b
    have hb : S.CanConcat B := hcan B (by simp [B])
    let S' := S.concat B
    have ht : (bs ++ [b]).map toMvPolynomial = S'.toList := by
      simp [S', B, List.map_append, hbs, toList_concat hb, List.concat_eq_append]
    have hf := weak_filter tail (bs ++ [b]) b S' ht
    have hc : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        S'.CanConcat p := by
      intro p hp
      rw [hf] at hp
      have hlt := (of_decide_eq_true (List.mem_filter.mp hp).2).1
      have hp0 := (hcan p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))).1
      exact ⟨hp0, fun _ => by simpa [S', length_concat, concat_apply] using hlt⟩
    have hle := ih S' U ht hc (by simpa only [Computable.Weak.basicSet.go] using ho)
    exact le_trans hle (le_of_lt (concat_lt hb))

/-- Greedy rank minimality, proved by induction on the executable loop itself. -/
private theorem go_minimal (ps bs : List (MvPoly n R cmp)) :
    ∀ (S : TriangularSet (Fin n) R), bs.map toMvPolynomial = S.toList →
    (∀ p ∈ ps.map toMvPolynomial, p ≠ 0) →
    (∀ p ∈ ps.map toMvPolynomial, S.CanConcat p) →
    (∀ p ∈ ps.map toMvPolynomial, p.initial.reducedToSet S) →
    (ps.map toMvPolynomial).Pairwise (· ≤ ·) →
    ∀ T : TriangularSet (Fin n) R, T.IsWeakAscendingSet →
    (S.length ≤ T.length ∧ ∀ i < S.length, S i ≈ T i) →
    (∀ p ∈ T, (∀ i < S.length, ¬ S i ≈ p) → p ∈ ps.map toMvPolynomial) →
    ∀ U : TriangularSet (Fin n) R,
    (Computable.Weak.basicSet.go ps bs).map toMvPolynomial = U.toList → U ≤ T := by
  induction ps, bs using Computable.Weak.basicSet.go.induct with
  | case1 bs =>
    intro S hbs _ _ _ _ T _ _ hmem U ho
    simp only [Computable.Weak.basicSet.go] at ho
    have he : U = S := toList_eq_iff_eq.mp (ho.symm.trans hbs)
    rw [he]
    apply ge_of_forall_equiv
    intro i hi
    simpa using hmem _ (apply_mem hi)
  | case2 bs b tail bsNext ih =>
    dsimp only [bsNext] at ih
    simp only [List.unattach_filter, List.unattach_attach] at ih
    intro S hbs hnz hcan hred hsort T hT ⟨hlen, hequiv⟩ hmem U ho
    let B := toMvPolynomial b
    have hb : S.CanConcat B := hcan B (by simp [B])
    let S' := S.concat B
    have heq : S' = S.concat B := rfl
    have hBmin : ∀ ⦃q⦄, q ∈ (b :: tail).map toMvPolynomial → B ≤ q :=
      fun _ => List.Pairwise.rel_head hsort
    by_cases hL : T.length = S.length
    · have he : S ≈ T := equiv_iff'.mpr ⟨hL.symm, hequiv⟩
      exact le_trans (go_le _ _ S U hbs hcan ho) (equiv_def''.mp he).1
    have hL : S.length < T.length := Nat.lt_of_le_of_ne hlen (Ne.symm hL)
    have hBq : B ≤ T S.length := by
      apply hBmin
      apply hmem _ (apply_mem hL)
      intro i hi
      apply not_antisymmRel_of_lt
      rw [AntisymmRel.lt_congr_left (hequiv i hi)]
      exact apply_lt_of_index_lt hL hi
    have ht : (bs ++ [b]).map toMvPolynomial = S'.toList := by
      simp [S', B, List.map_append, hbs, toList_concat hb, List.concat_eq_append]
    have hf := weak_filter tail (bs ++ [b]) b S' ht
    have hn : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        p ≠ 0 := by
      intro p hp
      rw [hf] at hp
      exact hnz p (List.mem_cons_of_mem _ (List.mem_of_mem_filter hp))
    have hr' : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        p.initial.reducedToSet S' := by
      intro p hp
      rw [hf] at hp
      exact (of_decide_eq_true (List.mem_filter.mp hp).2).2
    have ho' : (Computable.Weak.basicSet.go
        (tail.filter (Computable.Weak.accepts b (bs ++ [b])))
        (bs ++ [b])).map toMvPolynomial = U.toList := by
      simpa only [Computable.Weak.basicSet.go] using ho
    have hc : ∀ p ∈ (tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map toMvPolynomial,
        S'.CanConcat p := by
      intro p hp
      have hp0 := hn p hp
      rw [hf] at hp
      have hlt := (of_decide_eq_true (List.mem_filter.mp hp).2).1
      exact ⟨hp0, fun _ => by simpa [S', length_concat, concat_apply] using hlt⟩
    rcases le_iff_lt_or_equiv.mp hBq with hlt | he
    · have hlt' : S' < T := by
        rw [heq]
        apply TriangularSet.lt_def.mpr
        refine Or.inl ⟨S.length, S.length_concat _ ▸ lt_add_one _, ?_, fun i hi => ?_⟩
        · simpa [concat_apply] using hlt
        rw [concat_apply, ite_eq_left hi]
        exact hequiv i hi
      exact le_trans (go_le _ _ S' U ht hc ho') (le_of_lt hlt')
    have hsrt : ((tail.filter (Computable.Weak.accepts b (bs ++ [b]))).map
        toMvPolynomial).Pairwise (· ≤ ·) := by
      rw [hf]
      exact List.Pairwise.filter _ (List.Pairwise.of_cons hsort)
    refine ih S' ht hn hc hr' hsrt T hT ⟨?_, ?_⟩ ?_ U ho'
    · rw [heq, length_concat]
      exact hL
    · intro i hi
      simp only [heq, length_concat, concat_apply] at hi ⊢
      split_ifs with hi1 hi2
      · exact hequiv i hi1
      · exact hi2 ▸ he
      · omega
    intro p hp hp2
    have hp2' : ¬ B ≈ p ∧ ∀ i < S.length, ¬ S i ≈ p := by
      simp only [heq, length_concat, concat_apply] at hp2
      constructor
      · simpa using hp2 S.length (lt_add_one _)
      · intro i hi
        simpa [hi] using hp2 i (Nat.lt_add_right 1 hi)
    rw [hf, List.mem_filter, decide_eq_true_eq]
    have hpmem := hmem p hp hp2'.2
    have htail : p ∈ tail.map toMvPolynomial := by
      rcases List.mem_cons.mp hpmem with heq | hm
      · exact False.elim (hp2'.1 (heq ▸ refl _))
      · exact hm
    rcases hp with ⟨k, hk1, hk2⟩
    have hk3 : S.length < k := by
      by_contra hn
      rcases lt_or_eq_of_le (le_of_not_gt hn) with hki | hki
      · exact hp2'.2 k hki (hk2 ▸ hequiv k hki)
      · exact hp2'.1 (by rw [← hk2, hki]; exact he)
    refine ⟨htail, ?_, MvPolynomial.reducedToSet_iff.mpr fun i hi => ?_⟩
    · rw [(equiv_iff.mp he).1, ← hk2]
      exact max_vars_lt_of_index_lt hk1 hk3
    rw [← hk2, heq, concat_apply]
    split_ifs with hi1 hi2
    · exact (reducedTo_congr_right (hequiv i hi1)).mpr (hT (lt_trans hi1 hk3) hk1)
    · exact (reducedTo_congr_right he).mpr (hT hk3 hk1)
    · rw [heq, length_concat] at hi
      omega

private theorem output_structure (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.Weak.basicSet ps).map toMvPolynomial = S.toList ∧
      S.IsWeakAscendingSet ∧ (∀ p ∈ S, p ∈ ps.map toMvPolynomial) := by
  have hn : ∀ p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial, p ≠ 0 :=
    fun p hp => ((candidates_mem ps p).mp hp).2
  have hc : ∀ p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial,
      (∅ : TriangularSet (Fin n) R).CanConcat p := fun p hp => empty_canConcat (hn p hp)
  obtain ⟨S, ho, ha, hm⟩ := go_structure (Computable.basicSetCandidates ps) [] ∅
    (by simp) hn hc (fun _ _ p hp => False.elim (notMem_empty p hp)) isWeakAscendingSet_empty
  refine ⟨S, ho, ha, ?_⟩
  · intro p hp
    rcases hm p hp with hp | hp
    · exact False.elim (notMem_empty p hp)
    · exact ((candidates_mem ps p).mp hp).1

/-- Interpret the executable algorithm, adding only proofs of triangularity. -/
@[expose] noncomputable def basicSet (l : List (MvPolynomial (Fin n) R)) :
    TriangularSet (Fin n) R where
  toList := (Computable.Weak.basicSet
    (l.map (ofMvPolynomial (cmp := cmp)))).map toMvPolynomial
  zero_notMem' := by
    obtain ⟨S, ho, _⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
    rw [ho]
    exact S.zero_notMem_toList
  isChain_max_vars' := by
    obtain ⟨S, ho, _⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
    rw [ho]
    exact S.toList_isChain

theorem basicSet_isAscendingSet (l : List (MvPolynomial (Fin n) R)) :
    (basicSet (cmp := cmp) l).IsWeakAscendingSet := by
  obtain ⟨S, ho, ha, _⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
  have he : basicSet (cmp := cmp) l = S := toList_eq_iff_eq.mp ho
  exact he ▸ ha

theorem basicSet_subset (l : List (MvPolynomial (Fin n) R)) :
    ∀ ⦃p⦄, p ∈ basicSet (cmp := cmp) l → p ∈ l := by
  obtain ⟨S, ho, _, hs⟩ := output_structure (l.map (ofMvPolynomial (cmp := cmp)))
  have he : basicSet (cmp := cmp) l = S := toList_eq_iff_eq.mp ho
  simpa [he, List.map_map, Function.comp_def] using hs

/-- Rank minimality follows the original theory's greedy prefix comparison. -/
theorem basicSet_minimal (l : List (MvPolynomial (Fin n) R))
    {S : TriangularSet (Fin n) R} (hS : S.IsWeakAscendingSet)
    (hsub : ∀ ⦃p⦄, p ∈ S → p ∈ l) : basicSet (cmp := cmp) l ≤ S := by
  let ps := l.map (ofMvPolynomial (cmp := cmp))
  have hn : ∀ p ∈ (Computable.basicSetCandidates ps).map toMvPolynomial, p ≠ 0 :=
    fun p hp => ((candidates_mem ps p).mp hp).2
  apply go_minimal (Computable.basicSetCandidates ps) [] ∅ (by simp) hn
    (fun p hp => empty_canConcat (hn p hp))
    (fun _ _ p hp => False.elim (notMem_empty p hp)) (candidates_sorted ps)
    S hS (by simp) _ (basicSet (cmp := cmp) l) rfl
  intro p hp _
  exact (candidates_mem ps p).mpr ⟨by simpa [ps, List.map_map, Function.comp_def] using hsub hp,
    ne_zero_of_mem hp⟩

/-- The executable output is a weak ascending subset of the input and is
rank-minimal among all weak ascending subsets of that input. -/
theorem output_spec (ps : List (MvPoly n R cmp)) :
    ∃ S : TriangularSet (Fin n) R,
      (Computable.Weak.basicSet ps).map toMvPolynomial = S.toList ∧
      S.IsWeakAscendingSet ∧ (∀ p ∈ S, p ∈ ps.map toMvPolynomial) ∧
      (∀ T : TriangularSet (Fin n) R, T.IsWeakAscendingSet →
        (∀ p ∈ T, p ∈ ps.map toMvPolynomial) → S ≤ T) := by
  let S := basicSet (cmp := cmp) (ps.map toMvPolynomial)
  have ho : (Computable.Weak.basicSet ps).map toMvPolynomial = S.toList := by
    simp [S, basicSet, List.map_map, Function.comp_def]
  exact ⟨S, ho, basicSet_isAscendingSet _,
    fun _ hp => basicSet_subset _ hp, fun T hT hs => basicSet_minimal _ hT (fun _ hp => hs _ hp)⟩

/-- Every output passes the weak executable ascending-set check. -/
theorem basicSet_check (ps : List (MvPoly n R cmp)) :
    Computable.Weak.isAscendingSet (Computable.Weak.basicSet ps) = true := by
  obtain ⟨S, ho, ha, _⟩ := output_structure ps
  exact (isAscendingSet_iff_of_toList _ S ho).mpr ha

end Weak

/-- Compatibility name for the standard output specification. -/
abbrev basicSet_spec := @Standard.output_spec

omit [DecidableEq R] in
/-- Every selected Hex polynomial occurs in the original input. -/
theorem basicSet_subset (ps : List (MvPoly n R cmp)) {p : MvPoly n R cmp}
    (hp : p ∈ Computable.basicSet ps) : p ∈ ps := by
  classical
  obtain ⟨S, ho, _, hsub⟩ := Standard.output_structure ps
  have hm : toMvPolynomial p ∈ S := by
    rw [← mem_toList_iff, ← ho]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨q, hq, he⟩ := List.mem_map.mp (hsub _ hm)
  exact toMvPolynomial_injective he ▸ hq

end CharacteristicSet.Bridge
