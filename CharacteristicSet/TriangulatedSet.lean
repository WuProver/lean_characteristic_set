import CharacteristicSet.Basic
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Fintype.WithTopBot

open scoped MvPolynomial

/-!
# Triangulated Set

This file defines the structure of a **Triangulated Set** of multivariate polynomials.
A Triangulated Set is a finite ordered sequence of non-zero polynomials `[P₁, P₂, ..., Pₘ]`
such that their main variables (main variables) are strictly increasing:
`mainVariable(P₁) < mainVariable(P₂) < ... < mainVariable(Pₘ)`.

## Main Definitions

* `TriangulatedSet`: The structure definition.
  It bundles the length, the sequence function,
  and the proofs of non-zero elements and ascending main variables.
* `TriangulatedSet.rank`: A lexicographic rank assigned to each triangulated set,
  used to prove termination of algorithms (like Wu's Method).
* `TriangulatedSet.toFinset` / `toList`: Viewing the sequence as a set or list of polynomials.

## Main Results

* `TriangulatedSet.instWellFoundedLT`: Proof that triangulated sets are well-founded
  under the rank ordering (assuming finite variables).
  This guarantees termination of characteristic set algorithms.
* `TriangulatedSet.takeConcat_lt_of_reducedToSet`: Appending a reduced element
  strictly decreases the rank, used to prove termination of basic set algorithms.

-/

/-- A Triangulated Set is a finite sequence of polynomials
with strictly increasing main variables. -/
structure TriangulatedSet (σ R : Type*) [CommSemiring R] [LinearOrder σ] where
  /-- The number of polynomials in the set. -/
  length' : ℕ
  /-- The sequence of polynomials, indexed by `ℕ`. -/
  seq : ℕ → R[σ]
  /-- Elements within the length bound are non-zero. -/
  elements_ne_zero : ∀ n, n < length' ↔ seq n ≠ 0
  /-- The main variables of the polynomials are strictly increasing. -/
  ascending_mainVariable : ∀ n < length' - 1, (seq n).mainVariable < (seq (n + 1)).mainVariable

namespace TriangulatedSet

variable {R σ : Type*} [CommSemiring R] [LinearOrder σ]

-- Enable treating a TriangulatedSet as a function `ℕ → R[σ]`
instance instFunLike : FunLike (TriangulatedSet σ R) ℕ R[σ] :=
  ⟨fun S ↦ S.seq, by
    rintro ⟨S, f, hf⟩ ⟨T, g, hg⟩ (hfg : f = g)
    congr
    rewrite [hfg] at hf
    have (n : ℕ) : ¬n < S ↔ ¬n < T := not_iff_not.mpr (Iff.trans (hf n) (hg n).symm)
    simp only [not_lt] at this
    exact le_antisymm ((this T).mpr <| le_refl T) <| (this S).mp <| le_refl S⟩

/-- The length of the triangulated set. -/
def length (S : TriangulatedSet σ R) : ℕ := S.length'

variable {S T : TriangulatedSet σ R} {p : R[σ]} {m n : ℕ}

@[ext]
theorem ext (h : ∀ i, S i = T i) : S = T := DFunLike.ext _ _ h

theorem elements_ne_zero_iff : n < S.length ↔ S n ≠ 0 := S.elements_ne_zero n

theorem elements_eq_zero_iff : S.length ≤ n ↔ S n = 0 :=
  not_iff_not.mp <| Iff.trans Nat.not_le elements_ne_zero_iff

theorem ext' (h1 : S.length = T.length) (h2 : ∀ i < S.length, S i = T i) : S = T := ext fun i ↦ by
  if h : i < S.length then exact h2 i h
  else
    have h := le_of_not_gt h
    rw [elements_eq_zero_iff.mp h, elements_eq_zero_iff.mp <| h1 ▸ h]

@[simp] theorem apply_length_eq_zero : S S.length = 0 := elements_eq_zero_iff.mp (le_refl _)

theorem mainVariable_lt_mainVariable_next :
    n < S.length - 1 → (S n).mainVariable < (S (n + 1)).mainVariable := S.ascending_mainVariable n

theorem mainVariable_lt_mainVariable_next' :
    n + 1 < S.length → (S n).mainVariable < (S (n + 1)).mainVariable :=
  fun h ↦ mainVariable_lt_mainVariable_next <| Nat.lt_sub_of_add_lt h

theorem mainVariable_lt_mainVariable_next'' :
    0 < n → n < S.length → (S (n - 1)).mainVariable < (S n).mainVariable := fun h1 h2 ↦
  have : n - 1 < S.length - 1 := Nat.sub_lt_sub_right h1 h2
  Nat.sub_add_cancel h1 ▸ mainVariable_lt_mainVariable_next this

theorem mainVariable_lt_of_index_lt :
    m < n → n < S.length → (S m).mainVariable < (S n).mainVariable := fun hmn h ↦ by
  induction n with
  | zero => exact absurd hmn <| Nat.not_lt_zero m
  | succ n hn => match Nat.lt_succ_iff_lt_or_eq.mp hmn with
    | Or.inl hmn =>
      exact lt_trans (hn hmn (Nat.lt_of_succ_lt h)) <| mainVariable_lt_mainVariable_next' h
    | Or.inr hmn => rewrite [hmn]; exact mainVariable_lt_mainVariable_next' h

theorem false_of_mainVariable_ge_of_index_lt :
    m < n → n < S.length → (S n).mainVariable ≤ (S m).mainVariable → False :=
  fun h1 h2 h3 ↦ absurd h3 <| not_le_of_gt <| mainVariable_lt_of_index_lt h1 h2

theorem mainVariable_le_of_index_le :
    m ≤ n → n < S.length → (S m).mainVariable ≤ (S n).mainVariable := fun hmn h ↦
  Or.elim (lt_or_eq_of_le hmn)
    (fun hmn ↦ le_of_lt <| mainVariable_lt_of_index_lt hmn h)
    (fun hmn ↦ by simp only [hmn, le_refl])

theorem le_of_index_le : m ≤ n → n < S.length → S m ≤ S n := fun hmn h ↦
  Or.elim (lt_or_eq_of_le hmn)
    (fun hmn ↦ le_of_lt <| MvPolynomial.lt_of_mainVariable_lt <| mainVariable_lt_of_index_lt hmn h)
    (fun hmn ↦ by simp only [hmn, le_refl])

theorem index_eq_of_mainVariable_eq :
    m < S.length → n < S.length → (S m).mainVariable = (S n).mainVariable → m = n :=
  fun hm hn hc ↦ Decidable.byContradiction fun con ↦ by
    match Nat.lt_or_gt_of_ne con with
    | Or.inl con => exact absurd hc <| ne_of_lt <| mainVariable_lt_of_index_lt con hn
    | Or.inr con => exact absurd hc.symm <| ne_of_lt <| mainVariable_lt_of_index_lt con hm

theorem index_eq_of_apply_eq : m < S.length → n < S.length → S m = S n → m = n :=
  fun hm hn hc ↦ index_eq_of_mainVariable_eq hm hn (congrArg MvPolynomial.mainVariable hc)

theorem apply_lt_of_index_lt : m < n → n < S.length → S m < S n :=
  fun hmn h ↦ MvPolynomial.lt_of_mainVariable_lt <| mainVariable_lt_of_index_lt hmn h

theorem index_lt_of_apply_lt (h : m < S.length) : S m < S n → m < n := fun hs ↦
  Decidable.byContradiction fun hmn ↦ False.elim <| match Nat.eq_or_lt_of_not_lt hmn with
    | Or.inl hmn => Eq.not_lt (congrArg S hmn) hs
    | Or.inr hmn => (MvPolynomial.not_lt_iff_ge.mpr <| le_of_lt hs) (apply_lt_of_index_lt hmn h)

theorem index_eq_zero_of_mainVariable_eq_bot :
    n < S.length → (S n).mainVariable = ⊥ → n = 0 := fun h1 h2 ↦
  Decidable.byContradiction fun hn ↦
    WithBot.not_lt_bot _ (h2 ▸ mainVariable_lt_mainVariable_next'' (Nat.zero_lt_of_ne_zero hn) h1)

theorem exists_index_mainVar_between_of_mainVar_first_lt
    (h : (S 0).mainVariable < p.mainVariable) : ∃ k ≤ S.length,
    (S (k - 1)).mainVariable < p.mainVariable ∧
    (p.mainVariable ≤ (S k).mainVariable ∨ k = S.length) := by
  by_contra con
  simp only [not_exists, not_and, not_or, not_le] at con
  have : ∀ k ≤ S.length, (S k).mainVariable < p.mainVariable := fun k hk ↦ by
    induction k with
    | zero => exact h
    | succ k hk' => exact (con (k + 1) hk <| hk' <| Nat.le_of_succ_le hk).1
  have con := con S.length <| le_refl S.length
  have := this (S.length - 1) <| Nat.sub_le S.length 1
  exact (con this).2 rfl

/-! ### Set-like behavior -/

instance instSetLike : SetLike (TriangulatedSet σ R) R[σ] where
  coe := fun S ↦ {p | ∃ n < S.length, S n = p}
  coe_injective' := by
    intro S T (h : (fun p ↦ ∃ n < S.length, S n = p) = fun p ↦ ∃ n < T.length, T n = p)
    have h (p) : (∃ n, S n = p) ↔ ∃ n, T n = p := by
      have (S : TriangulatedSet σ R) : (∃ n, S n = p) ↔ p = 0 ∨ ∃ n < S.length, S n = p :=
        ⟨fun ⟨n, hn⟩ ↦ or_iff_not_imp_left.mpr fun hp ↦ ⟨n, elements_ne_zero_iff.mpr (hn ▸ hp), hn⟩,
          fun hp ↦ Or.elim hp (fun hp ↦ ⟨S.length, hp ▸ apply_length_eq_zero⟩)
            (fun hp ↦ ⟨Exists.choose hp, (Exists.choose_spec hp).2⟩)⟩
      rw [this S, this T, Eq.to_iff (funext_iff.mp h p)]
    refine ext fun i ↦ ?_
    induction i using Nat.strong_induction_on with | h i hi =>
    have {S T : TriangulatedSet σ R} (h : ∀ p, (∃ n, S n = p) ↔ ∃ n, T n = p)
        (hi : ∀ m < i, S m = T m) : S i = 0 → T i = 0 := fun hs ↦ by
      by_contra ht
      have ⟨j ,hj⟩ := (h (T i)).mpr <| Exists.intro i rfl
      have h1 : i < T.length:= elements_ne_zero_iff.mpr ht
      rewrite [← hj] at ht
      have h2 : j < i := lt_of_lt_of_le (elements_ne_zero_iff.mpr ht) <| elements_eq_zero_iff.mpr hs
      rewrite [hi j h2] at hj
      exact False.elim <| Eq.not_lt hj <| apply_lt_of_index_lt h2 h1
    have : S i = 0 ↔ T i = 0 :=
      ⟨this h hi, this (fun p ↦ (h p).symm) (fun i hi' ↦ (hi i hi').symm)⟩
    by_cases hst : S i = 0 ∨ T i = 0
    · rewrite [this, or_self] at hst
      rw [hst, this, hst]
    rewrite [not_or] at hst
    have ⟨h1, h2⟩ := And.intro (elements_ne_zero_iff.mpr hst.1) (elements_ne_zero_iff.mpr hst.2)
    have ⟨j ,hj⟩ := (h (S i)).mp <| Exists.intro i rfl
    by_cases hij : j ≤ i
    · match Nat.eq_or_lt_of_le hij with
      | .inl hij => exact (hij ▸ hj).symm
      | .inr hij =>
        absurd (apply_lt_of_index_lt hij h1)
        exact hj.symm ▸ (Eq.not_lt <| hi j hij)
    have ⟨k ,hk⟩ := (h (T i)).mpr <| Exists.intro i rfl
    have : j < T.length := elements_ne_zero_iff.mpr <| ne_of_eq_of_ne hj hst.1
    have : T i < T j := apply_lt_of_index_lt (not_le.mp hij) this
    have hs : S k < S i := by rewrite [← hk, hj] at this; exact this
    have : k < S.length := elements_ne_zero_iff.mpr <| ne_of_eq_of_ne hk hst.2
    have klti : k < i := index_lt_of_apply_lt this hs
    have : T k = T i := (hi k klti).symm.trans hk
    exact absurd this <| ne_of_lt <| apply_lt_of_index_lt klti h2

theorem mem_def : p ∈ S ↔ ∃ n < S.length, S n = p := Eq.to_iff rfl

@[simp] theorem zero_notMem (S : TriangulatedSet σ R) : 0 ∉ S := fun h ↦
  have := Exists.choose_spec (mem_def.mp h)
  absurd this.2 <| elements_ne_zero_iff.mp this.1

theorem ne_zero_of_mem : p ∈ S → p ≠ 0 := fun h1 h2 ↦ (h2 ▸ zero_notMem S) h1

theorem apply_mem {n : ℕ} : n < S.length → S n ∈ S := fun h ↦ ⟨n, h, rfl⟩

theorem forall_mem_iff_forall_index {S : TriangulatedSet σ R} {a : R[σ] → Prop} :
    (∀ p ∈ S, a p) ↔ ∀ i < S.length, a (S i) := Set.forall_mem_image

theorem forall_mem_iff_forall_index' {S : TriangulatedSet σ R} {a : R[σ] → Prop} {n : ℕ}
    (h : n = S.length) : (∀ p ∈ S, a p) ↔ ∀ i : Fin n, a (S i) :=
  Iff.trans forall_mem_iff_forall_index (by rw [Fin.forall_iff, h])

theorem exists_mem_iff_exists_index {S : TriangulatedSet σ R} {a : R[σ] → Prop} :
    (∃ p ∈ S, a p) ↔ ∃ i < S.length, a (S i) := Set.exists_mem_image

theorem exists_mem_iff_exists_index' {S : TriangulatedSet σ R} {a : R[σ] → Prop} {n : ℕ}
    (h : n = S.length) : (∃ p ∈ S, a p) ↔ ∃ i : Fin n, a (S i) :=
  Iff.trans exists_mem_iff_exists_index (by simp only [Fin.exists_iff, h, exists_prop])

instance : HasSubset (TriangulatedSet σ R) where
  Subset S T := ∀ ⦃x⦄, x ∈ S → x ∈ T

instance : HasSSubset (TriangulatedSet σ R) where
  SSubset S T := S ⊆ T ∧ ¬T ⊆ S

@[simp] theorem Subset.refl (S : TriangulatedSet σ R) : S ⊆ S := fun _ ↦ id

theorem Subset.trans {U : TriangulatedSet σ R} : S ⊆ T → T ⊆ U → S ⊆ U :=
  fun h₁ h₂ _ m => h₂ (h₁ m)

theorem subset_def : S ⊆ T ↔ ∀ ⦃x⦄, x ∈ S → x ∈ T := Iff.rfl

theorem mem_of_subset (p : R[σ]) (h : S ⊆ T) : p ∈ S → p ∈ T := @h _

theorem ssubset_def : S ⊂ T ↔ S ⊆ T ∧ ¬T ⊆ S := Iff.rfl

def toFinset (S : TriangulatedSet σ R) : Finset R[σ] := (@Finset.univ (Fin S.length) _).map
  ⟨fun i ↦ S i.1, fun ⟨_, hi⟩ ⟨_, hj⟩ hij ↦ (Fin.mk.injEq ..) ▸ index_eq_of_apply_eq hi hj hij⟩

@[simp] theorem card_toFinset (S : TriangulatedSet σ R) : S.toFinset.card = S.length := by
  simp only [toFinset, Finset.card_map, Finset.card_univ, Fintype.card_fin]

@[simp] theorem mem_toFinset_iff : p ∈ S.toFinset ↔ p ∈ S := by
  refine Iff.trans ?_ SetLike.mem_coe
  simp [toFinset, Finset.map, SetLike.coe, Fin.exists_iff]

@[simp] theorem toFinset_eq_iff_eq : S.toFinset = T.toFinset ↔ S = T := by
  refine ⟨fun h ↦ SetLike.ext fun p ↦ ?_, congrArg _⟩
  rewrite [← mem_toFinset_iff, ← mem_toFinset_iff]
  exact Eq.to_iff (congrFun (congrArg Membership.mem h) p)

theorem toFinset_eq_coe_set (S : TriangulatedSet σ R) : S.toFinset = (S : Set R[σ]) :=
  Set.ext fun _ ↦ ⟨SetLike.mem_coe.mpr ∘ mem_toFinset_iff.mp, mem_toFinset_iff.mpr⟩

theorem length_le_of_subset : S ⊆ T → S.length ≤ T.length := fun h ↦ by
  rewrite [← card_toFinset, ← card_toFinset]
  exact Finset.card_le_card <| Finset.coe_subset.mp (by simpa [toFinset_eq_coe_set] using h)

theorem length_lt_of_ssubset : S ⊂ T → S.length < T.length := fun h ↦ by
  rewrite [← card_toFinset, ← card_toFinset]
  exact Finset.card_lt_card <| Finset.coe_ssubset.mp (by simpa [toFinset_eq_coe_set] using h)

def toList (S : TriangulatedSet σ R) : List R[σ] := List.ofFn fun i : Fin S.length ↦ S i.1

@[simp] theorem length_toList (S : TriangulatedSet σ R) : S.toList.length = S.length := by
  simp only [toList, List.length_ofFn]

@[simp] theorem mem_toList_iff : p ∈ S.toList ↔ p ∈ S := by
  refine Iff.trans ?_ SetLike.mem_coe
  simp [toList, SetLike.coe, Fin.exists_iff]

@[simp] theorem toList_eq_iff_eq : S.toList = T.toList ↔ S = T := by
  refine ⟨fun h ↦ SetLike.ext fun p ↦ ?_, congrArg _⟩
  simpa [← mem_toList_iff] using Eq.to_iff (congrFun (congrArg Membership.mem h) p)

theorem toList_getElem {n : ℕ} (h : n < S.toList.length) : S.toList[n] = S n := by
  simp only [toList, List.getElem_ofFn]

theorem toList_non_zero : ∀ ⦃p⦄, p ∈ S.toList → p ≠ 0 :=
  fun _ hp ↦ ne_zero_of_mem <| mem_toList_iff.mp hp

theorem toList_pairwise : S.toList.Pairwise fun p q ↦ p.mainVariable < q.mainVariable :=
  List.pairwise_ofFn.mpr fun _ ⟨_, hn⟩ hmn ↦ mainVariable_lt_of_index_lt hmn hn

instance [DecidableEq R[σ]] : DecidableEq (TriangulatedSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ toList_eq_iff_eq

private noncomputable def empty : TriangulatedSet σ R where
  length' := 0
  seq := 0
  elements_ne_zero := fun n ↦ ⟨fun h ↦ absurd h <| Nat.not_lt_zero n, absurd rfl⟩
  ascending_mainVariable := fun _ hn ↦ absurd hn <| of_decide_eq_false rfl

noncomputable instance : EmptyCollection (TriangulatedSet σ R) := ⟨empty⟩

noncomputable instance : Inhabited (TriangulatedSet σ R) := ⟨∅⟩

theorem empty_eq_default : (∅ : TriangulatedSet σ R) = default := rfl

@[simp] theorem length_empty : (∅ : TriangulatedSet σ R).length = 0 := rfl

@[simp] theorem empty_apply : (∅ : TriangulatedSet σ R) n = 0 := rfl

theorem length_eq_zero_iff : S.length = 0 ↔ S = ∅ :=
  ⟨fun h ↦ ext fun i ↦ elements_eq_zero_iff.mp <| h ▸ Nat.zero_le i, fun h ↦ h ▸ length_empty⟩

theorem length_gt_zero_iff : 0 < S.length ↔ S ≠ ∅ :=
  iff_not_comm.mp <| Iff.trans length_eq_zero_iff.symm
    ⟨fun h ↦ h ▸ Nat.not_add_one_le_zero 0, Nat.eq_zero_of_not_pos⟩

theorem length_ge_one_iff : 1 ≤ S.length ↔ S ≠ ∅ := length_gt_zero_iff

theorem notMem_empty (p : R[σ]) : p ∉ (∅ : TriangulatedSet σ R) := fun h ↦
  Nat.not_succ_le_zero _ (Exists.choose_spec h).1

theorem eq_empty_of_forall_notMem : (∀ p, p ∉ S) → S = ∅ := fun h ↦ by
  contrapose! h
  exact ⟨S 0, apply_mem <| length_gt_zero_iff.mpr h⟩

/-! ### Rank and Ordering -/

section Rank

/-- The rank of a Triangulated Set is a lexicographic sequence of ranks of its polynomials.
A more intuitive definition is `rank_lt_iff`, `S < T` if one of the following two occurs:
1. There exists some `k < S.length` such that
   `S₀ ≈ T₀`, `S₁ ≈ T₁`, ..., `Sₖ₋₁ ≈ Tₖ₋₁` and `Sₖ < Tₖ`.
2. `S.length > T.length` and `∀ i < T.length, Sᵢ ≈ Tᵢ` -/
noncomputable def rank (S : TriangulatedSet σ R) : Lex (ℕ → WithTop (WithBot σ ×ₗ ℕ)) :=
  fun i ↦ if i < S.length then WithTop.some (S i).rank else ⊤

theorem rank_def : S.rank = fun i ↦ if i < S.length then WithTop.some (S i).rank else ⊤ := rfl

theorem rank_apply {i : ℕ} (h : i < S.length) : S.rank i = (S i).rank := if_pos h

theorem rank_apply' {i : ℕ} (h : S.length ≤ i) : S.rank i = ⊤ := if_neg <| not_lt_of_ge h

theorem rank_lt_iff : S.rank < T.rank ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length < S.length ∧ ∀ i < T.length, S i ≈ T i) where
  mp h := by
    simp only [Pi.instLTLexForall, Pi.Lex, rank] at h
    rcases h with ⟨k, hk1, hk2⟩
    have klts : k < S.length := Decidable.byContradiction fun h ↦ not_top_lt <| if_neg h ▸ hk2
    rewrite [if_pos klts] at hk2
    by_cases kltt : k < T.length
    · rewrite [if_pos kltt, WithTop.coe_lt_coe, ← MvPolynomial.lt_def'] at hk2
      refine Or.inl ⟨k, klts, hk2, fun i hi ↦ ?_⟩
      have := hk1 i hi
      rewrite [if_pos <| lt_trans hi klts, if_pos <| lt_trans hi kltt, WithTop.coe_eq_coe] at this
      exact MvPolynomial.equiv_def'.mpr this
    have tlek : T.length ≤ k := Nat.le_of_not_lt kltt
    have tlts : T.length < S.length := lt_of_le_of_lt tlek klts
    refine Or.inr ⟨tlts, fun i hi ↦ ?_⟩
    have := hk1 i <| lt_of_lt_of_le hi tlek
    rewrite [if_pos (lt_trans hi tlts), if_pos hi, WithTop.coe_eq_coe] at this
    exact MvPolynomial.equiv_def'.mpr this
  mpr h := by
    simp only [Pi.instLTLexForall, Pi.Lex, rank]
    rcases h with (⟨k, hk, hk1, hk2⟩ | ⟨hlen, heq⟩)
    · use k ⊓ T.length
      constructor
      · intro i hi
        have hi := lt_min_iff.mp hi
        simp only [if_pos <| lt_trans hi.1 hk]
        rewrite [if_pos hi.2, WithTop.coe_eq_coe, ← MvPolynomial.equiv_def']
        exact hk2 i hi.1
      by_cases klt' : k < T.length
      · simpa [min_eq_left_of_lt klt', hk, klt'] using MvPolynomial.lt_def'.mp hk1
      have : T.length ≤ k := Nat.le_of_not_lt klt'
      simp [min_eq_right_iff.mpr this, lt_of_le_of_lt this hk]
    refine ⟨T.length, fun i hi ↦ ?_, ?_⟩
    · simpa [lt_trans hi hlen, hi] using MvPolynomial.equiv_def'.mp (heq i hi)
    simp only [hlen, reduceIte, lt_self_iff_false, WithTop.coe_lt_top]

theorem rank_eq_iff : S.rank = T.rank ↔ S.length = T.length ∧ ∀ k, S k ≈ T k where
  mp h := by
    rewrite [rank_def, rank_def, funext_iff] at h
    have tles := h S.length
    have slet := h T.length
    simp only [lt_self_iff_false, reduceIte, right_eq_ite_iff, WithTop.top_ne_coe, imp_false,
      not_lt, ite_eq_right_iff, WithTop.coe_ne_top] at tles slet
    have ltheq := eq_of_le_of_ge slet tles
    refine ⟨ltheq, fun i ↦ ?_⟩
    by_cases ilt : i < T.length
    · have := h i
      simp only [ltheq, ilt, reduceIte, WithTop.coe_eq_coe] at this
      exact MvPolynomial.equiv_def'.mpr this
    have t0 : T i = 0 := elements_eq_zero_iff.mp <| Nat.le_of_not_lt ilt
    have s0 : S i = 0 := elements_eq_zero_iff.mp <| Nat.le_of_not_lt <| ltheq ▸ ilt
    rw [t0, s0]
  mpr h := by
    rewrite [rank_def, rank_def, h.1]
    funext i
    split_ifs with ilt
    · rewrite [WithTop.coe_eq_coe]
      exact MvPolynomial.equiv_def'.mp <| h.2 i
    rfl

open scoped Classical in
theorem rank_le_iff : S.rank ≤ T.rank ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length ≤ S.length ∧ ∀ k < T.length, S k ≤ T k) := by
  rewrite [le_iff_lt_or_eq, rank_lt_iff, rank_eq_iff, or_assoc]
  refine ⟨fun h ↦ Or.elim h Or.inl (fun h ↦ Or.inr <| Or.elim h
      (fun h ↦ ⟨le_of_lt h.1, fun k hk ↦ (MvPolynomial.equiv_def''.mp <| h.2 k hk).1⟩)
      (fun h ↦ ⟨ge_of_eq h.1, fun k hk ↦ (MvPolynomial.equiv_def''.mp <| h.2 k).1⟩)),
    fun h ↦ Or.elim h Or.inl (fun ⟨h1, h2⟩ ↦ ?_)⟩
  by_cases h : ∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i
  · exact Or.inl h
  have h2 : ∀ k < T.length, S k ≈ T k := by
    contrapose! h
    let ⟨k, ⟨hk1, hk2⟩, hk3⟩ := Nat.findX h
    rewrite [MvPolynomial.equiv_def, not_and', MvPolynomial.not_lt_iff_ge, not_not] at hk2
    exact ⟨k, lt_of_lt_of_le hk1 h1, hk2 <| h2 k hk1,
      fun i hi ↦ not_not.mp <| not_and.mp (hk3 _ hi) <| lt_trans hi hk1⟩
  refine Or.inr <| Or.elim (lt_or_eq_of_le h1)
    (fun h ↦ Or.inl ⟨h, h2⟩)
    (fun h ↦ Or.inr ⟨h.symm, fun k ↦ if hk : k < T.length then (h2 k hk) else by
      rw [elements_eq_zero_iff.mp <| le_of_not_gt hk,
        elements_eq_zero_iff.mp <| le_of_not_gt <| h ▸ hk]⟩)

instance instPreorder : Preorder (TriangulatedSet σ R) where
  le := InvImage (· ≤ ·) rank
  le_refl := fun _ ↦ by rw [InvImage]
  le_trans := fun _ _ _ hpq hqr ↦ le_trans hpq hqr
  lt S T := S.rank ≤ T.rank ∧ ¬T.rank ≤ S.rank
  lt_iff_le_not_ge := by intros; rw [InvImage, InvImage]

theorem le_def' : S ≤ T ↔ S.rank ≤ T.rank := Iff.rfl

noncomputable instance : DecidableLE (TriangulatedSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ le_def'.symm

noncomputable instance : DecidableLT (TriangulatedSet σ R) := decidableLTOfDecidableLE

instance : IsTotal (TriangulatedSet σ R) (· ≤ ·) where
  total S T := le_total S.rank T.rank

theorem le_def : S ≤ T ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length ≤ S.length ∧ ∀ k < T.length, S k ≤ T k) := rank_le_iff

theorem lt_def' : S < T ↔ S.rank < T.rank := Iff.trans lt_iff_le_not_ge (by
  rewrite [le_def', le_def', not_le, and_iff_right_iff_imp]
  exact le_of_lt)

theorem lt_def : S < T ↔ (∃ k < S.length, S k < T k ∧ ∀ i < k, S i ≈ T i) ∨
    (T.length < S.length ∧ ∀ i < T.length, S i ≈ T i) := Iff.trans lt_def' rank_lt_iff

theorem lt_empty : S ≠ ∅ → S < ∅ := fun h ↦ lt_def.mpr <| Or.inr
  ⟨by rewrite [length_empty]; exact length_ge_one_iff.mpr h,
  fun i hi ↦ by rewrite [length_empty] at hi; exact absurd hi <| Nat.not_lt_zero i⟩

theorem le_empty (S : TriangulatedSet σ R) : S ≤ ∅ :=
  Or.elim (eq_or_ne S ∅) le_of_eq <| le_of_lt ∘ lt_empty

@[simp] theorem not_lt_iff_ge : ¬(S < T) ↔ T ≤ S := by rw [le_def', lt_def', not_lt]

@[simp] theorem not_le_iff_gt : ¬(S ≤ T) ↔ T < S := by rw [le_def', lt_def', not_le]

theorem ge_of_forall_equiv : (∀ n < S.length, ∃ i < T.length, T i ≈ S n) → T ≤ S := fun h ↦ by
  contrapose! h
  match lt_def.mp <| not_le_iff_gt.mp h with
  | .inl ⟨k, hk1, hk2, hk3⟩ =>
    refine ⟨k, hk1, fun i hi1 ↦ ?_⟩
    match Nat.lt_trichotomy i k with
    | .inl hi2 =>
      apply not_antisymmRel_of_lt
      rewrite [AntisymmRel.lt_congr_left <| Setoid.symm <| hk3 i hi2]
      exact apply_lt_of_index_lt hi2 hk1
    | .inr hi2 => match hi2 with
    | .inl hi2 => exact not_antisymmRel_of_gt (hi2 ▸ hk2)
    | .inr hi2 => exact not_antisymmRel_of_gt <| lt_trans hk2 <| apply_lt_of_index_lt hi2 hi1
  | .inr ⟨h1, h2⟩ =>
    refine ⟨T.length, h1, fun i hi1 ↦ ?_⟩
    apply not_antisymmRel_of_lt
    rewrite [AntisymmRel.lt_congr_left <| Setoid.symm <| h2 i hi1]
    exact apply_lt_of_index_lt hi1 h1

theorem ge_of_subset : S ⊆ T → T ≤ S := fun h ↦
  ge_of_forall_equiv fun n hn ↦
    have ⟨i, hi1, hi2⟩ : S n ∈ T := h <| apply_mem hn
    ⟨i, hi1, by rw [hi2]⟩

instance instSetoid : Setoid (TriangulatedSet σ R) := AntisymmRel.setoid _ (· ≤ ·)

noncomputable instance instDecidableRelEquiv : @DecidableRel (TriangulatedSet σ R) _ (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd

theorem equiv_def'' : S ≈ T ↔ S ≤ T ∧ T ≤ S := Iff.rfl

theorem equiv_def' : S ≈ T ↔ S.rank = T.rank := Iff.trans equiv_def''
  (by rewrite [le_def', le_def']; exact Std.le_antisymm_iff)

theorem equiv_def : S ≈ T ↔ ¬S < T ∧ ¬T < S := Iff.trans equiv_def''
  (by rw [not_lt_iff_ge, not_lt_iff_ge, and_comm])

theorem equiv_iff : S ≈ T ↔ S.length = T.length ∧ (∀ k, S k ≈ T k) :=
  Iff.trans equiv_def' rank_eq_iff

theorem equiv_iff' : S ≈ T ↔ S.length = T.length ∧ (∀ k < S.length, S k ≈ T k) := by
  simp only [equiv_iff, and_congr_right_iff]
  refine fun h1 ↦ ⟨fun h2 k _ ↦ h2 k, fun h2 k ↦ ?_⟩
  if hk : k < S.length then exact h2 k hk
  else
    have : S.length ≤ k := Nat.le_of_not_lt hk
    rw [elements_eq_zero_iff.mp this, elements_eq_zero_iff.mp (h1 ▸ this)]

theorem le_iff_lt_or_equiv : S ≤ T ↔ S < T ∨ S ≈ T := le_iff_lt_or_antisymmRel

theorem lt_of_equiv_of_lt {U : TriangulatedSet σ R} : S ≈ T → T < U → S < U :=
  lt_of_antisymmRel_of_lt

theorem lt_of_lt_of_equiv {U : TriangulatedSet σ R} : S < T → T ≈ U → S < U :=
  lt_of_lt_of_antisymmRel

theorem equiv_of_le_of_ge : S ≤ T → T ≤ S → S ≈ T := And.intro

theorem gt_of_ssubset : S ⊂ T → T < S := fun h ↦ by
  have := Set.ssubset_iff_subset_ne.mp h
  apply or_iff_not_imp_right.mp <|  le_iff_lt_or_equiv.mp <| ge_of_subset this.1
  refine Not.intro fun con ↦ absurd (length_lt_of_ssubset h) ?_
  exact not_lt_of_ge <| le_of_eq (equiv_iff.mp con).1

end Rank

noncomputable def single_of_ne_zero (hp : p ≠ 0) : TriangulatedSet σ R where
  length' := 1
  seq n := if n = 0 then p else 0
  elements_ne_zero := fun _ ↦
    ⟨fun hn ↦ ne_of_eq_of_ne (if_pos <| Nat.lt_one_iff.mp hn) hp,
    fun hn ↦ by by_contra con; exact hn (if_neg <| Nat.ne_zero_of_lt <| Nat.le_of_not_lt con)⟩
  ascending_mainVariable n hn := absurd hn <| Nat.not_lt_zero n

theorem single_of_ne_zero_apply (hp : p ≠ 0) :
    (single_of_ne_zero hp) n = if n = 0 then p else 0 := rfl

theorem length_single_of_ne_zero (hp : p ≠ 0) : (single_of_ne_zero hp).length = 1 := rfl

/-! ### Well-Foundedness -/

section WellFounded

theorem wellFoundedLT_mvPolynomial_of_wellFoundedLT :
    WellFoundedLT (TriangulatedSet σ R) → WellFoundedLT R[σ] := fun h ↦ by
  rewrite [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h ⊢
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf1⟩
  have hf2 (n : ℕ) : f n ≠ 0 := by
    by_contra con
    absurd con ▸ (hf1 n)
    exact MvPolynomial.not_lt_iff_ge.mpr MvPolynomial.zero_le
  use fun n ↦ single_of_ne_zero <| hf2 n
  intro n
  refine lt_def.mpr <| Or.inl ⟨0, ?_⟩
  simpa [length_single_of_ne_zero] using hf1 n

theorem wellFoundedLT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT (TriangulatedSet σ R) → WellFoundedLT σ :=
  MvPolynomial.wellFoundedLT_variables_of_wellFoundedLT ∘
    wellFoundedLT_mvPolynomial_of_wellFoundedLT

theorem wellFoundeGT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT (TriangulatedSet σ R) → WellFoundedGT σ := fun h ↦ by
  rewrite [WellFoundedGT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain]
  rewrite [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf1⟩
  have hf2 (n : ℕ) : (MvPolynomial.X (f n) : R[σ]) < MvPolynomial.X (f (n + 1)) :=
    MvPolynomial.X_lt_of_lt <| hf1 n
  let S (n : ℕ) : TriangulatedSet σ R := {
    length' := n
    seq i := if i < n then MvPolynomial.X (f i) else 0
    elements_ne_zero i := by simp
    ascending_mainVariable i hi := by simp [Nat.lt_of_lt_pred hi, Nat.add_lt_of_lt_sub hi, hf1 i]}
  have length_S (n : ℕ) : (S n).length = n := rfl
  have S_apply (n i : ℕ) : S n i = if i < n then MvPolynomial.X (f i) else 0 := rfl
  refine ⟨S, fun n ↦ lt_def.mpr <| Or.inr ?_⟩
  simp only [length_S, lt_add_iff_pos_right, zero_lt_one, S_apply, true_and]
  intro i hi
  simp only [Nat.lt_add_right 1 hi, ↓reduceIte, hi, Setoid.refl]

theorem length_le [Fintype σ] : S.length ≤ Fintype.card σ + 1 := by
  let f : Fin S.length → WithBot σ := fun i ↦ (S i).mainVariable
  have : f.Injective :=
    fun ⟨_, hi⟩ ⟨_, hj⟩ h ↦ Fin.mk.injEq _ hi _ hj ▸ index_eq_of_mainVariable_eq hi hj h
  have card_le := Fintype.card_le_of_injective f this
  have : Fintype.card (WithBot σ) = Fintype.card (Option σ) := rfl
  rewrite [Fintype.card_fin, this, Fintype.card_option] at card_le
  exact card_le

/-- An auxiliary rank mapping into a finite domain to prove well-foundedness. -/
private noncomputable def _rank [Fintype σ] (S : TriangulatedSet σ R) :
  Lex (Fin (Fintype.card σ + 1) → WithTop (WithBot σ ×ₗ ℕ)) := fun i ↦ S.rank i.1

private theorem _rank_lt_iff [Fintype σ] : S._rank < T._rank ↔ S.rank < T.rank where
  mp h := by
    simp only [Pi.instLTLexForall, Pi.Lex, _rank] at h ⊢
    rcases h with ⟨k, hk1, hk2⟩
    have kn : k < Fintype.card σ + 1 := Decidable.byContradiction fun con ↦ by
      simp only [rank_apply' <| le_trans length_le <| Nat.le_of_not_lt con] at hk2
      exact (lt_self_iff_false ⊤).mp hk2
    exact Exists.intro k.1 ⟨fun i hi ↦ hk1 ⟨i, lt_trans hi kn⟩ hi, hk2⟩
  mpr h := by
    simp only [Pi.instLTLexForall, Pi.Lex, _rank] at h ⊢
    rcases h with ⟨k, hk1, hk2⟩
    have kn : k < Fintype.card σ + 1 := Decidable.byContradiction fun con ↦ by
      simp only [rank_apply' <| le_trans length_le <| Nat.le_of_not_lt con] at hk2
      exact (lt_self_iff_false ⊤).mp hk2
    exact Exists.intro ⟨k, kn⟩ ⟨fun _ hi ↦ hk1 _ hi, hk2⟩

variable [Finite σ] (S' : Set (TriangulatedSet σ R))

/-- The set of Triangulated Sets is well-founded under the lexicographic rank ordering.
This is a crucial result that guarantees the termination of the Characteristic Set Algorithm. -/
instance instIsWellFoundedRankLT : IsWellFounded (TriangulatedSet σ R) (InvImage (· < ·) rank) :=
  haveI : Fintype σ := Fintype.ofFinite σ
  Subrelation.isWellFounded (InvImage (· < ·) _rank) _rank_lt_iff.mpr

instance : WellFoundedLT (TriangulatedSet σ R) :=
  Subrelation.isWellFounded (InvImage (· < ·) rank) lt_def'.mp

instance : WellFoundedRelation (TriangulatedSet σ R) := ⟨(· < ·), instWellFoundedLT.wf⟩

theorem Set.has_min (h : S'.Nonempty) : ∃ S ∈ S', ∀ T ∈ S', S ≤ T :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (TriangulatedSet σ R) _ _
  have ⟨S, hS1, hS2⟩ := WellFounded.has_min this S' h
  ⟨S, hS1, fun T hT ↦ not_lt_iff_ge.mp (hS2 T hT)⟩

noncomputable def Set.min (h : S'.Nonempty) : TriangulatedSet σ R := Exists.choose (has_min S' h)

theorem Set.min_mem (h : S'.Nonempty) : min S' h ∈ S' :=
  (Exists.choose_spec (has_min S' h)).1

theorem Set.min_le (h : S'.Nonempty) : ∀ T ∈ S', min S' h ≤ T :=
  (Exists.choose_spec (has_min S' h)).2

end WellFounded


noncomputable def take (S : TriangulatedSet σ R) (n : ℕ) : TriangulatedSet σ R where
  length' := n ⊓ S.length
  seq m := if m < n then S m else 0
  elements_ne_zero m := by
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp]
    exact ⟨fun h ↦ ⟨lt_of_lt_of_le h <| Nat.min_le_left ..,
      elements_ne_zero_iff.mp <| lt_of_lt_of_le h <| Nat.min_le_right ..⟩,
      fun h ↦ lt_min h.1 (elements_ne_zero_iff.mpr h.2)⟩
  ascending_mainVariable m hm := by
    have : n ⊓ S.length - 1 ≤ n - 1 := Nat.sub_le_sub_right (Nat.min_le_left ..) 1
    have : m + 1 < n := Nat.add_lt_of_lt_sub <| lt_of_lt_of_le hm this
    rewrite [if_pos this, if_pos <| Nat.lt_of_succ_lt this]
    have : n ⊓ S.length - 1 ≤ S.length - 1 := Nat.sub_le_sub_right (Nat.min_le_right ..) 1
    exact mainVariable_lt_mainVariable_next <| lt_of_lt_of_le hm this

@[simp]
theorem length_take (S : TriangulatedSet σ R) (n : ℕ) : (S.take n).length = n ⊓ S.length := rfl

theorem take_apply (S : TriangulatedSet σ R) (n m : ℕ) :
    (S.take n) m = if m < n then S m else 0 := rfl

theorem take_apply' {S : TriangulatedSet σ R} {n m : ℕ} (h : m < n ⊓ S.length) :
    (S.take n) m = S m := by
  rw [take_apply, if_pos (lt_of_lt_of_le h (Nat.min_le_left ..))]

theorem lt_take : n < S.length → S < S.take n := fun h ↦
  lt_def.mpr <| Or.inr ⟨S.length_take n ▸ inf_lt_of_left_lt h,
  fun i hi ↦ by rw [take_apply, if_pos (min_eq_left_of_lt h ▸ length_take S n ▸ hi)]⟩

@[simp] theorem take_zero (S : TriangulatedSet σ R) : S.take 0 = ∅ := ext fun _ ↦ rfl

@[simp] theorem take_length (S : TriangulatedSet σ R) : S.take (S.length) = S := ext fun i ↦ by
  rewrite [take_apply]
  split_ifs with hi
  · exact rfl
  rw [elements_eq_zero_iff.mp <| Nat.le_of_not_lt hi]

theorem take_subset (S : TriangulatedSet σ R) (n : ℕ) : S.take n ⊆ S := fun _ ⟨i, hi1, hi2⟩ ↦
  ⟨i, lt_of_lt_of_le hi1 (Nat.min_le_right ..),
    (@if_pos _ _ (lt_of_lt_of_le hi1 <| Nat.min_le_left ..) _ (S i) 0) ▸ hi2⟩

theorem toList_take_comm (S : TriangulatedSet σ R) (n : ℕ) :
    (S.take n).toList = S.toList.take n := by
    refine List.ext_getElem (by simp [length_toList, List.length_take]) fun i h1 h2 ↦ ?_
    rw [List.getElem_take, toList_getElem h1,
      toList_getElem (lt_of_lt_of_le (List.length_take ▸ h2) (Nat.min_le_right ..)),
      take_apply' (S.length_toList ▸ List.length_take ▸ h2)]

def drop (S : TriangulatedSet σ R) (n : ℕ) : TriangulatedSet σ R where
  length' := S.length - n
  seq m := S (m + n)
  elements_ne_zero _ := Iff.trans ⟨Nat.add_lt_of_lt_sub, Nat.lt_sub_of_add_lt⟩ elements_ne_zero_iff
  ascending_mainVariable m hm :=
    mainVariable_lt_of_index_lt (Nat.add_lt_add_right (lt_add_one m) n) <|
      (add_assoc m 1 n).symm ▸ Nat.add_lt_of_lt_sub <| (add_comm n 1) ▸ hm

@[simp]
theorem length_drop (S : TriangulatedSet σ R) (n : ℕ) : (S.drop n).length = S.length - n := rfl

@[simp] theorem drop_apply (S : TriangulatedSet σ R) (n m : ℕ) : (S.drop n) m = S (m + n) := rfl

@[simp] theorem drop_zero (S : TriangulatedSet σ R) : S.drop 0 = S :=
  ext fun i ↦ by rw [drop_apply, add_zero]

theorem drop_eq_empty_of_ge_length : S.length ≤ n → S.drop n = ∅ := fun h ↦
  ext fun _ ↦ (drop_apply S ..).symm ▸ elements_eq_zero_iff.mp (Nat.le_add_left_of_le h)

@[simp] theorem drop_length (S : TriangulatedSet σ R) : S.drop S.length = ∅ :=
  drop_eq_empty_of_ge_length (le_refl _)

theorem toList_drop_comm (S : TriangulatedSet σ R) (n : ℕ) :
    (S.drop n).toList = S.toList.drop n := by
  refine List.ext_getElem (by simp [length_toList, List.length_drop]) fun i h1 h2 ↦ ?_
  have h2 : n + i < S.toList.length := by
    rewrite [List.length_drop] at h2
    exact Nat.add_lt_of_lt_sub' h2
  rw [List.getElem_drop, toList_getElem h1, toList_getElem h2, drop_apply, add_comm i n]

theorem lt_drop : S ≠ ∅ → 0 < n → S < S.drop n := fun h1 h2 ↦
  if gel : S.length ≤ n then drop_eq_empty_of_ge_length gel ▸ lt_empty h1
  else lt_def.mpr <| Or.inl ⟨0, length_gt_zero_iff.mpr h1, by
      rewrite [drop_apply, zero_add]
      apply MvPolynomial.lt_of_mainVariable_lt
      exact mainVariable_lt_of_index_lt h2 <| Nat.lt_of_not_le gel,
    fun i hi ↦ absurd hi <| Nat.not_lt_zero i⟩

/-- The condition required to append `p` to `S` while maintaining the Triangulated Set property.
`p` must be non-zero and its main variable must be strictly greater than
the main variable of the last element of `S`. -/
abbrev canConcat (S : TriangulatedSet σ R) (p : R[σ]) : Prop :=
  p ≠ 0 ∧ (0 < S.length → (S (S.length - 1)).mainVariable < p.mainVariable)

theorem canConcat_def : S.canConcat p ↔
    (p ≠ 0 ∧ (0 < S.length → (S (S.length - 1)).mainVariable < p.mainVariable)) := Iff.rfl

theorem empty_canConcat : p ≠ 0 → (∅ : TriangulatedSet σ R).canConcat p :=
  fun h1 ↦ ⟨h1, fun h2 ↦ absurd h2 <| Nat.lt_irrefl 0⟩

theorem not_canConcat_zero : ¬ S.canConcat 0 := not_and.mpr fun a _ ↦ a rfl

/-- Appends a polynomial `p` to the end of `S`. Requires `S.canConcat p`. -/
noncomputable def concat (S : TriangulatedSet σ R) (p : R[σ])
    (h : S.canConcat p := by assumption) : TriangulatedSet σ R where
  length' := S.length + 1
  seq n := if n < S.length then S n else if n = S.length then p else 0
  elements_ne_zero n :=
    ⟨fun hn ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with (hn | hn)
      · simp [hn, elements_ne_zero_iff.mp hn]
      · simp [hn, h.1],
    fun hn ↦ by
      by_contra con
      have con := not_lt.mp con
      simp only [Nat.not_lt_of_gt con, reduceIte, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
      exact (Nat.ne_of_lt con) hn.1.symm⟩
  ascending_mainVariable n hn := by
    have hn : n < S.length := hn
    match Decidable.em (n + 1 < S.length) with
    | Or.inl h1 =>
      rewrite [if_pos hn, if_pos h1]
      exact mainVariable_lt_mainVariable_next <| Nat.lt_sub_of_add_lt h1
    | Or.inr h1 =>
      have h1 : n + 1 = S.length := Nat.le_antisymm hn <| Nat.le_of_not_lt h1
      simp only [hn, h1, lt_self_iff_false, reduceIte]
      exact add_tsub_cancel_right n 1 ▸ h1 ▸ h.2 (h1 ▸ Nat.zero_lt_succ n)

@[simp] theorem length_concat {p : R[σ]} (h : S.canConcat p) :
    (S.concat p).length = S.length + 1 := rfl

theorem concat_apply {p : R[σ]} (h : S.canConcat p) (n : ℕ) :
    (S.concat p) n = if n < S.length then S n else if n = S.length then p else 0 := rfl

theorem concat_apply_length {p : R[σ]} (h : S.canConcat p) : (S.concat p) S.length = p := by
  simp [concat_apply]

theorem concat_lt {p : R[σ]} (h : S.canConcat p) : S.concat p h < S := lt_def.mpr <|
  Or.inr ⟨length_concat h ▸ lt_add_one S.length, fun i hi ↦ by rw [concat_apply h, if_pos hi]⟩

theorem mem_concat {p : R[σ]} (h : S.canConcat p) : p ∈ S.concat p := by
  use S.length
  rewrite [length_concat, concat_apply h, if_neg (Nat.lt_irrefl S.length), if_pos rfl]
  simp only [lt_add_iff_pos_right, zero_lt_one, and_self]

theorem subset_concat {p : R[σ]} (h : S.canConcat p) : S ⊆ S.concat p := fun _ ⟨i, hi⟩ ↦
  ⟨i, (length_concat h) ▸ Nat.lt_add_one_of_lt hi.1, (concat_apply h _) ▸ if_pos hi.1 ▸ hi.2⟩

theorem mem_concat_iff {p q : R[σ]} (h : S.canConcat p) : q ∈ S.concat p ↔ q = p ∨ q ∈ S := by
  refine ⟨fun ⟨i, (hi1 : i < S.length + 1), hi2⟩ ↦ ?_, fun hp ↦ ?_⟩
  · rewrite [concat_apply h i] at hi2
    if hlt : i < S.length then
      exact Or.inr ⟨i, hlt, by apply if_pos hlt ▸ hi2⟩
    else
      have : i = S.length := Nat.eq_of_lt_succ_of_not_lt hi1 hlt
      exact Or.inl (if_pos this ▸ if_neg hlt ▸ hi2).symm
  exact Or.elim hp (fun hp ↦ hp ▸ mem_concat h) (fun hp ↦ subset_concat h hp)

theorem coe_concat_eq_insert {p : R[σ]} (h : S.canConcat p) :
    S.concat p = (S : Set R[σ]).insert p := Set.ext fun q ↦ by
  simpa using mem_concat_iff h

/-- Converts a list to a TriangulatedSet.
Requires the list to be non-zero and pairwise strictly ascending in main variable. -/
noncomputable def list (l : List R[σ]) (h1 : ∀ p ∈ l, p ≠ 0 := by assumption)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable := by assumption) :
    TriangulatedSet σ R where
  length' := l.length
  seq n := l.getD n 0
  elements_ne_zero n :=
    ⟨fun hn ↦ by simp [hn, List.forall_mem_iff_getElem.mp h1 n hn],
      fun hn ↦ by contrapose! hn; simp [hn]⟩
  ascending_mainVariable n hn := by
    have hn1 := Nat.lt_of_lt_pred hn
    have hn2 := Nat.add_lt_of_lt_sub hn
    simp [hn1, hn2, List.pairwise_iff_getElem.mp h2 _ _ hn1 hn2 (lt_add_one n)]

theorem length_list {l : List R[σ]} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) : (list l).length = l.length := rfl

theorem list_nil_eq_empty {l : List R[σ]} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) (h3 : l = []) : list l = ∅ :=
  length_eq_zero_iff.mp (by rw [length_list, h3, List.length_nil])

theorem list_apply {l : List R[σ]} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable)
    {n : ℕ} (hn : n < l.length) : (list l) n = l[n] := by
  change l.getD n 0 = l[n]
  simp only [List.getD_eq_getElem?_getD, hn, getElem?_pos, Option.getD_some]

theorem toList_list_eq {l : List R[σ]} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) : (list l).toList = l :=
  List.ext_getElem (length_toList (list l) ▸ rfl)
    (fun _ hi1 hi2 ↦ (list_apply _ _ hi2) ▸ toList_getElem hi1)

theorem list_eq_of_eq_toList {l : List R[σ]} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) (heq : l = S.toList) :
    list l = S := by
  refine ext' (heq ▸ S.length_toList) fun i (hi : i < l.length) ↦ ?_
  rw [list_apply _ _ hi, ← toList_getElem <| heq ▸ hi, List.getElem_of_eq heq hi]

theorem mem_list_iff {l : List R[σ]} (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) {p : R[σ]} :
    p ∈ list l ↔ p ∈ l := by
  simp only [mem_def, length_list, List.mem_iff_getElem]
  refine ⟨fun ⟨i, hi1, hi2⟩ ↦ ⟨i, hi1, ?_⟩, fun ⟨i, hi1, hi2⟩ ↦ ⟨i, hi1, ?_⟩⟩
  <;> rw [← hi2, list_apply]

variable [DecidableEq R] {S T: TriangulatedSet σ R} {p q : R[σ]}

/-- Unsafely construct a TriangulatedSet from a list. Panics if preconditions are not met.
This should be used with caution, primarily for computation where inputs are guaranteed correct. -/
noncomputable def list! (l : List R[σ]) : TriangulatedSet σ R :=
  if h : (∀ p ∈ l, p ≠ 0) ∧ l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable then list l h.1 h.2
  else panic "Illegal list input"

theorem list!_eq_list (l : List R[σ]) (h1 : ∀ p ∈ l, p ≠ 0)
    (h2 : l.Pairwise fun p q ↦ p.mainVariable < q.mainVariable) : list! l = list l := by
  unfold list!
  split_ifs with h
  · rfl
  exact absurd ⟨h1, h2⟩ h

noncomputable def single (p : R[σ]) : TriangulatedSet σ R :=
  if h : p = 0 then ∅ else single_of_ne_zero h

@[simp] theorem single_zero : single (0 : R[σ]) = ∅ := rfl

theorem length_single : p ≠ 0 → (single p).length = 1 :=
  fun h ↦ by simp only [single, h, reduceDIte]; exact rfl

theorem single_eq_zero_iff : p = 0 ↔ single p = ∅ :=
  ⟨fun h ↦ by simp only [single, h, reduceDIte],
  fun h ↦ by by_contra con; absurd h ▸ length_single con; exact Nat.ne_of_beq_eq_false rfl⟩

theorem length_single_zero : p = 0 → (single p).length = 0 := fun h ↦ single_eq_zero_iff.mp h ▸ rfl

theorem length_single_le_one : (single p).length ≤ 1 :=
  Or.elim (em (p = 0))
    (fun h ↦ le_of_eq_of_le (length_single_zero h) <| Nat.zero_le 1)
    (fun h ↦ (length_single h).symm ▸ le_refl 1)

theorem single_apply_zero (p : R[σ]) : single p 0 = p :=
  Or.elim (em (p = 0))
    (fun h ↦ by simp only [single, h, reduceDIte, empty_apply])
    (fun h ↦ by simp only [single, h, reduceDIte, single_of_ne_zero_apply h, reduceIte])

theorem single_apply_nonzero (p : R[σ]) : n ≠ 0 → single p n = 0 :=
  fun h ↦ Or.elim (em (p = 0))
    (fun hn ↦ by simp only [single, hn, reduceDIte, empty_apply])
    (fun hn ↦ by simp only [single, hn, reduceDIte, single_of_ne_zero_apply hn, reduceIte, h])

theorem mem_single_of_ne_zero : p ≠ 0 → p ∈ single p := fun h ↦
  mem_def.mpr ⟨0, length_single h ▸ Nat.one_pos, single_apply_zero p⟩

theorem notMem_single_of_ne {q : R[σ]} : q ≠ p → q ∉ single p := mt fun h ↦
  have ⟨_, hi1, hi2⟩ := h
  have hi1 := Nat.lt_one_iff.mp <| lt_of_lt_of_le hi1 length_single_le_one
  (single_apply_zero p) ▸ hi1 ▸ hi2.symm

theorem single_lt_empty : p ≠ 0 → (single p) < ∅ :=
  fun h ↦ lt_empty <| (not_iff_not.mpr single_eq_zero_iff).mp h

theorem gt_single_of_first_gt : p ≠ 0 → p < S 0 → single p < S := fun hp hs ↦
  lt_def.mpr <| Or.inl ⟨0,
    Nat.lt_of_sub_eq_succ <| length_single hp,
    (single_apply_zero p).symm ▸ hs,
    fun i hi ↦ absurd hi <| Nat.not_lt_zero i⟩

theorem single_of_length_le_one : S.length ≤ 1 → S = single (S 0) :=
  fun h ↦ ext fun i ↦ by
    match Decidable.em (i = 0) with
    | Or.inl hi => rw [hi, single_apply_zero]
    | Or.inr hi =>
      have : S.length ≤ i := Nat.le_trans h <| Nat.one_le_iff_ne_zero.mpr hi
      rw [elements_eq_zero_iff.mp this, single_apply_nonzero _ hi]

theorem single_of_last_mainVariable_eq_bot :
    (S (S.length - 1)).mainVariable = ⊥ → S = single (S 0) := fun h ↦
  have : S.length ≤ 1 := by
    by_cases hl : S.length = 0
    · exact hl ▸ Nat.zero_le 1
    have : S.length - 1 < S.length := Nat.sub_one_lt hl
    exact Nat.le_of_sub_eq_zero <| index_eq_zero_of_mainVariable_eq_bot this h
  single_of_length_le_one this

/--
`takeConcat S p` tries to construct a new Triangulated Set
by taking a prefix of `S` and appending `p`.
This is a key operation in constructing the Characteristic Set.
If `p` fits naturally at the end of `S`, it behaves like `S.concat p`.
If `p` conflicts with some element in `S` (in terms of main variable order), `takeConcat` finds the
first element in `S` that has a higher or equal main variable than `p`,
truncates `S` before that element, and appends `p`.
-/
noncomputable def takeConcat (S : TriangulatedSet σ R) (p : R[σ]) : TriangulatedSet σ R :=
  if S = ∅ then single p
  else if hc : p.mainVariable ≤ (S 0).mainVariable then single p
  else
    let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
    have hk : k ≤ S.length ∧ (S (k - 1)).mainVariable < p.mainVariable ∧
        (p.mainVariable ≤ (S k).mainVariable ∨ k = S.length) :=
      Nat.find_spec <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
    have mainVariable_lt : (S.take k).canConcat p := by
      rewrite [canConcat, length_take, min_eq_left hk.1, take_apply]
      refine ⟨MvPolynomial.ne_zero_of_mainVariable_ne_bot <| LT.lt.ne_bot <| lt_of_not_ge hc, ?_⟩
      exact fun hkz ↦ if_pos (Nat.sub_one_lt_of_lt hkz) ▸ hk.2.1
    (S.take k).concat p

theorem takeConcat_eq_concat_of_canConcat (h : S.canConcat p) : S.takeConcat p = S.concat p := by
  unfold takeConcat
  split_ifs with h1 hc
  · simp [h1, single, h.1, single_of_ne_zero, concat]
  repeat' have h1 := length_gt_zero_iff.mpr h1
  · absurd hc
    simp only [not_le]
    refine lt_of_le_of_lt (mainVariable_le_of_index_le (Nat.zero_le _) ?_) <| h.2 h1
    exact Nat.sub_one_lt_of_lt h1
  let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  have hk : k = S.length := by
    have : k ≤ S.length ∧ (S (k - 1)).mainVariable < p.mainVariable ∧
        (p.mainVariable ≤ (S k).mainVariable ∨ k = S.length) :=
      Nat.find_spec <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
    by_contra con
    simp only [con, or_false] at this
    absurd lt_of_le_of_ne this.1 con
    have := index_lt_of_apply_lt (Nat.sub_one_lt_of_lt h1) <|
      MvPolynomial.lt_of_mainVariable_lt <| lt_of_lt_of_le (h.2 h1) this.2.2
    exact Nat.not_lt.mpr <| Nat.le_of_pred_lt this
  change (S.take k).concat p _ = S.concat p
  simp only [hk, take_length]

theorem takeConcat_zero_eq_empty (S : TriangulatedSet σ R) : S.takeConcat 0 = ∅ := by
  simp only [takeConcat, single_zero, MvPolynomial.mainVariable_zero, bot_le, ↓reduceDIte, ite_self]

theorem mem_takeConcat (S : TriangulatedSet σ R) {p : R[σ]} (h : p ≠ 0) : p ∈ S.takeConcat p := by
  unfold takeConcat
  split_ifs with _ hc
  repeat' exact mem_single_of_ne_zero h
  exact mem_concat _

theorem takeConcat_subset : ∀ q ∈ S.takeConcat p, q ≠ p → q ∈ S := fun q hq1 hq2 ↦ by
  unfold takeConcat at hq1
  split_ifs at hq1 with hs hc
  repeat exact absurd hq1 <| notMem_single_of_ne hq2
  let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  apply S.take_subset k
  change q ∈ ((S.take k).concat p _ : Set R[σ]) at hq1
  simpa [coe_concat_eq_insert, Set.insert, hq2] using hq1


section Reduced

open MvPolynomial

theorem reducedTo_empty (q : R[σ]) : q.reducedToSet (∅ : TriangulatedSet σ R) :=
  fun p hp ↦ absurd hp (notMem_empty p)

theorem reducedToSet_iff : q.reducedToSet S ↔ ∀ i < S.length, q.reducedTo (S i) :=
  Iff.trans Iff.rfl S.forall_mem_iff_forall_index

noncomputable instance instDecidableRelReducedToSet :
    @DecidableRel _ (TriangulatedSet σ R) reducedToSet :=
  fun _ S ↦ @decidable_of_iff _ _ reducedToSet_iff.symm (S.length.decidableBallLT _)

theorem reducedToSet_congr_right : S ≈ T → (q.reducedToSet S ↔ q.reducedToSet T) := fun h ↦ by
  have := equiv_iff.mp h
  rw [reducedToSet_iff, reducedToSet_iff, ← this.1, forall_congr']
  refine fun i ↦ imp_congr_right fun _ ↦ reducedTo_congr_right <| this.2 i

/--
Key Lemma for the Basic Set Algorithm:
If `p` is non-zero and reduced with respect to `S`, then modifying `S`
by appending `p` (using `takeConcat`) strictly decreases the rank of the triangulated set.
This rank decrease is what guarantees the termination of the characteristic set computation.
-/
theorem takeConcat_lt_of_reducedToSet (p_ne_zero : p ≠ 0) (hp : p.reducedToSet S) :
    S.takeConcat p < S := by
  unfold takeConcat
  rewrite [reducedToSet_iff] at hp
  split_ifs with hS hc
  · exact hS ▸ single_lt_empty p_ne_zero
  · refine gt_single_of_first_gt p_ne_zero ?_
    rcases lt_or_eq_of_le hc with h | h
    · exact MvPolynomial.lt_of_mainVariable_lt h
    apply (MvPolynomial.reducedTo_iff_gt_of_mainVariable_eq p_ne_zero h).mp
    exact hp 0 <| length_ge_one_iff.mpr hS
  let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  have hk : k ≤ S.length ∧ (S (k - 1)).mainVariable < p.mainVariable ∧
      (p.mainVariable ≤ (S k).mainVariable ∨ k = S.length) :=
    Nat.find_spec <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  have length_tk : (S.take k).length = k := min_eq_left hk.1
  change (S.take k).concat p _ < S
  by_cases keq : k = S.length
  · refine lt_def.mpr <| Or.inr ?_
    rewrite [length_concat, length_tk]
    refine ⟨keq ▸ lt_add_one S.length, fun i hi ↦ ?_⟩
    rw [concat_apply, length_tk, keq, take_length, if_pos hi]
  refine lt_def.mpr <| Or.inl ?_
  simp only [length_concat, concat_apply, length_tk]
  refine ⟨k, lt_add_one k, ?_, fun i hi ↦ by rw [take_apply, if_pos hi, if_pos hi]⟩
  rewrite [if_neg <| Nat.lt_irrefl k, if_pos rfl]
  by_cases mainVariable_lt' : p.mainVariable < (S k).mainVariable
  · exact MvPolynomial.lt_of_mainVariable_lt mainVariable_lt'
  have : p.mainVariable ≤ (S k).mainVariable := (or_iff_left keq).mp hk.2.2
  have : p.mainVariable = (S k).mainVariable := eq_of_le_of_ge this <| le_of_not_gt mainVariable_lt'
  have := MvPolynomial.reducedTo_iff_gt_of_mainVariable_eq p_ne_zero this
  exact this.mp <| hp k <| Nat.lt_of_le_of_ne hk.1 keq

end Reduced

end TriangulatedSet
