module

public import HexMvPoly.Query

/-! Proof-facing main-variable and main-degree queries, with verified fast implementations
selected by `csimp` for native execution. -/

@[expose] public section

namespace CharacteristicSet.Computable

open Hex

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Zero R]

/-- Greatest occurring variable in the natural order, independently of `cmp`. -/
def mainVar (p : MvPoly n R cmp) : Option (Fin n) := p.vars.max?

/-- Numerical degree in the main variable; zero for constants. -/
def mainDegree (p : MvPoly n R cmp) : Nat :=
  (mainVar p).elim 0 (fun i => p.degreeOf i)

/-- Proof-facing equation; native compilation uses `mainVarFast` via `csimp`. -/
theorem mainVar_def (p : MvPoly n R cmp) : mainVar p = p.vars.max? := rfl

/-- Proof-facing equation; native compilation uses `mainDegreeFast` via `csimp`. -/
theorem mainDegree_def (p : MvPoly n R cmp) :
    mainDegree p = (mainVar p).elim 0 (fun i => p.degreeOf i) := rfl

theorem mainVar_eq_none_iff (p : MvPoly n R cmp) :
    mainVar p = none ↔ p.vars = [] := List.max?_eq_none_iff

theorem mainVar_eq_some_iff (p : MvPoly n R cmp) (i : Fin n) :
    mainVar p = some i ↔ i ∈ p.vars ∧ ∀ j ∈ p.vars, j ≤ i :=
  List.max?_eq_some_iff

theorem mainDegree_of_mainVar {p : MvPoly n R cmp} {i : Fin n}
    (h : mainVar p = some i) : mainDegree p = p.degreeOf i := by
  simp [mainDegree_def, h]

theorem mainDegree_of_none {p : MvPoly n R cmp}
    (h : mainVar p = none) : mainDegree p = 0 := by
  simp [mainDegree_def, h]

/-- Search descending coordinates strictly above the running main variable.
`lower` is zero when no variable has been found, or the previous variable plus one. -/
def mainVarFast.scanAbove (m : Mono n) (lower : Nat) :
    (k : Nat) → k ≤ n → Option (Fin n)
  | 0, _ => none
  | k + 1, _ =>
    if lower ≤ k then
      let i : Fin n := ⟨k, by omega⟩
      if m[i] == 0 then mainVarFast.scanAbove m lower k (by omega) else some i
    else none

/-- Update the running main variable with one supported monomial. -/
def mainVarFast.step (current : Option (Fin n)) (m : Mono n) : Option (Fin n) :=
  match mainVarFast.scanAbove m (current.elim 0 (fun i => i.val + 1)) n (Nat.le_refl n) with
  | some i => some i
  | none => current

/-- Fast main-variable query: scan terms directly, checking only coordinates above
the running main variable. -/
def mainVarFast (p : MvPoly n R cmp) : Option (Fin n) :=
  p.foldTerms (fun current m _ => mainVarFast.step current m) none

/-- Update the running main variable and its degree with one supported monomial. -/
def mainDegreeFast.step (state : Option (Fin n) × Nat) (m : Mono n) :
    Option (Fin n) × Nat :=
  let (current, degree) := state
  match mainVarFast.scanAbove m (current.elim 0 (fun i => i.val + 1)) n (Nat.le_refl n) with
  | some i => (some i, m[i])
  | none => (current, current.elim 0 (fun i => max degree m[i]))

/-- Fast main-degree query: one term traversal tracks the main variable and its degree together. -/
def mainDegreeFast (p : MvPoly n R cmp) : Nat :=
  (p.foldTerms (fun state m _ => mainDegreeFast.step state m) (none, 0)).2

open mainVarFast (scanAbove)
open mainDegreeFast (step)

private theorem scanAbove_none (m : Mono n) (lower k : Nat) (hk : k ≤ n) :
    scanAbove m lower k hk = none ↔
      ∀ i : Fin n, lower ≤ i.val → i.val < k → m[i.val] = 0 := by
  induction k with
  | zero => simp [scanAbove]
  | succ k ih =>
    simp only [scanAbove]
    split
    next hl =>
      split
      next hz =>
        rw [ih]
        constructor
        · intro h i hi hik
          by_cases he : i.val = k
          · have he' : i = (⟨k, by omega⟩ : Fin n) := Fin.ext he
            simpa [he'] using (beq_iff_eq.mp hz)
          · exact h i hi (by omega)
        · intro h i hi hik
          exact h i hi (by omega)
      next hz =>
        constructor
        · intro h; contradiction
        · intro h
          have := h ⟨k, by omega⟩ hl (Nat.lt_succ_self k)
          simp_all
    next hl =>
      constructor
      · intro _ i hi hik; omega
      · intro _; rfl

private theorem scanAbove_some (m : Mono n) (lower k : Nat) (hk : k ≤ n)
    {i : Fin n} (h : scanAbove m lower k hk = some i) :
    lower ≤ i.val ∧ i.val < k ∧ m[i.val] ≠ 0 ∧
      ∀ j : Fin n, i.val < j.val → j.val < k → m[j.val] = 0 := by
  induction k with
  | zero => simp [scanAbove] at h
  | succ k ih =>
    simp only [scanAbove] at h
    split at h
    next hl =>
      split at h
      next hz =>
        obtain ⟨hlo, hlt, hnz, hupper⟩ := ih (by omega) h
        refine ⟨hlo, by omega, hnz, ?_⟩
        intro j hij hjk
        by_cases he : j.val = k
        · have he' : j = (⟨k, by omega⟩ : Fin n) := Fin.ext he
          simpa [he'] using (beq_iff_eq.mp hz)
        · exact hupper j hij (by omega)
      next hz =>
        cases Option.some.inj h
        refine ⟨hl, Nat.lt_succ_self k, ?_, ?_⟩
        · simpa using hz
        · intro j hj hjk
          change k < j.val at hj
          omega
    next hl => simp at h

private def top (d : Mono n) : Option (Fin n) := d.support.max?

private theorem top_none (d : Mono n) : top d = none ↔ ∀ i : Fin n, d[i.val] = 0 := by
  simp [top, List.max?_eq_none_iff, Mono.support, List.filter_eq_nil_iff]

private theorem top_some (d : Mono n) (i : Fin n) :
    top d = some i ↔ d[i.val] ≠ 0 ∧ ∀ j : Fin n, i < j → d[j.val] = 0 := by
  simp only [top, List.max?_eq_some_iff, Mono.support, List.mem_filter,
    List.mem_finRange, true_and, bne_iff_ne]
  constructor
  · rintro ⟨hi, hupper⟩
    exact ⟨hi, fun j hij => by
      by_cases hj : d[j.val] = 0
      · exact hj
      · have := hupper j hj
        omega⟩
  · rintro ⟨hi, hupper⟩
    exact ⟨hi, fun j hj => by
      by_cases hji : j ≤ i
      · exact hji
      · exact False.elim (hj (hupper j (by omega)))⟩

private def profile (d : Mono n) : Option (Fin n) × Nat :=
  (top d, (top d).elim 0 (fun i => d[i]))

private theorem lcm_get (d m : Mono n) (i : Nat) (hi : i < n) :
    (Mono.lcm d m)[i] = max d[i] m[i] := Mono.getElem_lcm d m ⟨i, hi⟩

private theorem profile_step (d m : Mono n) :
    step (profile d) m = profile (Mono.lcm d m) := by
  cases hd : top d with
  | none =>
    have hd0 := (top_none d).mp hd
    cases hs : scanAbove m 0 n (Nat.le_refl n) with
    | none =>
      have hm0 := (scanAbove_none m 0 n (Nat.le_refl n)).mp hs
      have ht : top (Mono.lcm d m) = none := (top_none _).mpr fun i => by
        simp [lcm_get, hd0 i, hm0 i (Nat.zero_le _) i.isLt]
      simp [step, profile, hd, hs, ht]
    | some i =>
      obtain ⟨_, _, hi, hupper⟩ := scanAbove_some m 0 n (Nat.le_refl n) hs
      have ht : top (Mono.lcm d m) = some i := (top_some _ i).mpr ⟨by
        simpa [lcm_get, hd0 i] using hi, fun j hij => by
        simp [lcm_get, hd0 j, hupper j hij j.isLt]⟩
      simp [step, profile, hd, hs, ht, lcm_get, hd0 i]
  | some i =>
    obtain ⟨hi, hupper⟩ := (top_some d i).mp hd
    cases hs : scanAbove m (i.val + 1) n (Nat.le_refl n) with
    | none =>
      have hm0 := (scanAbove_none m (i.val + 1) n (Nat.le_refl n)).mp hs
      have ht : top (Mono.lcm d m) = some i := (top_some _ i).mpr ⟨by
        simp only [lcm_get]
        omega, fun j hij => by
          simp [lcm_get, hupper j hij, hm0 j (by omega) j.isLt]⟩
      simp [step, profile, hd, hs, ht, lcm_get]
    | some j =>
      obtain ⟨hij, _, hj, hjupper⟩ :=
        scanAbove_some m (i.val + 1) n (Nat.le_refl n) hs
      have hdj : d[j.val] = 0 := hupper j (by omega)
      have ht : top (Mono.lcm d m) = some j := (top_some _ j).mpr ⟨by
        simpa [lcm_get, hdj] using hj, fun k hjk => by
        simp [lcm_get, hupper k (by omega), hjupper k hjk k.isLt]⟩
      simp [step, profile, hd, hs, ht, lcm_get, hdj]

private theorem profile_zero : profile (Mono.zero : Mono n) = (none, 0) := by
  have ht : top (Mono.zero : Mono n) = none := (top_none _).mpr Mono.getElem_zero
  simp [profile, ht]

private theorem fold_profile (p : MvPoly n R cmp) :
    p.foldTerms (fun state m _ => step state m) (none, 0) = profile p.degrees := by
  rw [MvPoly.degrees_eq]
  unfold MvPoly.foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Std.ExtTreeMap.foldl_eq_foldl_toList]
  rw [← profile_zero]
  exact List.foldl_hom profile (fun d term => profile_step d term.1)

private theorem step_fst (state : Option (Fin n) × Nat) (m : Mono n) :
    mainVarFast.step state.1 m = (step state m).1 := by
  rcases state with ⟨current, degree⟩
  cases h : scanAbove m (current.elim 0 (fun i => i.val + 1)) n (Nat.le_refl n) <;>
    simp [mainVarFast.step, step, h]

/-- Compile the proof-facing main-variable definition to the direct scan. -/
@[csimp] theorem mainVar_eq_fast : @mainVar = @mainVarFast := by
  funext n R cmp _ _ _ p
  symm
  have hproj : p.foldTerms (fun current m _ => mainVarFast.step current m) none =
      (p.foldTerms (fun state m _ => step state m) (none, 0)).1 := by
    unfold MvPoly.foldTerms
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList, Std.ExtTreeMap.foldl_eq_foldl_toList]
    exact List.foldl_hom (Prod.fst : Option (Fin n) × Nat → Option (Fin n))
      (g₁ := fun state (term : Mono n × R) => step state term.1)
      (g₂ := fun current (term : Mono n × R) => mainVarFast.step current term.1)
      (init := (none, 0)) (l := p.termsInternal.toList)
      (fun state (term : Mono n × R) => step_fst state term.1)
  rw [mainVarFast, hproj, fold_profile]
  change p.degrees.support.max? = p.vars.max?
  rw [MvPoly.vars_eq]

/-- Compile the proof-facing main-degree definition to the fused traversal. -/
@[csimp] theorem mainDegree_eq_fast : @mainDegree = @mainDegreeFast := by
  funext n R cmp _ _ _ p
  symm
  rw [mainDegreeFast, fold_profile]
  unfold mainDegree mainVar profile top
  rw [MvPoly.vars_eq]
  cases p.degrees.support.max? with
  | none => rfl
  | some i => exact MvPoly.getElem_degrees p i

end CharacteristicSet.Computable
