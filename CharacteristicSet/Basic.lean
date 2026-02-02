import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring.RingNF

/-!
# Characteristic Set Basics

This file defines the fundamental concepts required for the Characteristic Set Method (Wu's Method),
including the Class, Degree, Rank, and Reduction of multivariate polynomials.

## Main Definitions

* `MvPolynomial.mainVariable`:
  The "main variable" of a polynomial, defined as the maximum variable index in its support.
* `MvPolynomial.mainDegree`: The degree of the polynomial with respect to its main variable.
* `MvPolynomial.rank`:
  A lexicographic combination of main variable and degree, defining a well-ordering on polynomials.
* `MvPolynomial.reducedTo`:
  The predicate indicating that a polynomial `q` is reduced with respect to `p`
  (meaning `q` has lower degree in `p`'s main variable).
* `MvPolynomial.reducedToSet`: `q` is reduced with respect to every polynomial in a set.

## Implementation Notes

We assume a linear order on the variable type `σ`.
The main variable `mainVariable p` is of type `WithBot σ` to handle the zero polynomial
conveniently (where `mainVariable 0 = ⊥`).

-/

namespace MvPolynomial

scoped[MvPolynomial] notation:9000 R "[" σ "]" => MvPolynomial σ R

variable {R σ : Type*} [CommSemiring R] {p q : R[σ]}

section MainVariable

variable [LinearOrder σ]

/-- The main variable of a multivariate polynomial `p` is the largest variable index
appearing in `p`. If `p = 0`, its main variable is `⊥`. -/
def mainVariable (p : R[σ]) : WithBot σ := p.support.sup (fun s ↦ s.support.max)

theorem mainVariable_def (p : R[σ]) : p.mainVariable = p.support.sup (fun s ↦ s.support.max) := rfl

@[simp] theorem mainVariable_zero : (0 : R[σ]).mainVariable = ⊥ := rfl

theorem ne_zero_of_mainVariable_ne_bot : p.mainVariable ≠ ⊥ → p ≠ 0 :=
  mt fun h ↦ h ▸ mainVariable_zero

@[simp] theorem mainVariable_monomial {r : R} (s : σ →₀ ℕ) (hr : r ≠ 0) :
    (monomial s r : R[σ]).mainVariable = s.support.max := by
  rw [← single_eq_monomial, mainVariable, support, Finsupp.support_single_ne_zero s hr,
    Finset.sup_singleton]

@[simp] theorem mainVariable_C (r : R) : (C r : R[σ]).mainVariable = ⊥ := by
  by_cases h : r = 0
  · simp only [mainVariable, h, C_0, support_zero, Finset.sup_empty]
  rw [C_apply, mainVariable_monomial _ h, Finsupp.support_zero, Finset.max_empty]

@[simp] theorem mainVariable_X_pow [Nontrivial R] (i : σ) {k : ℕ} (hk : k ≠ 0) :
    ((X i : R[σ]) ^ k).mainVariable = i := by
  rewrite [X_pow_eq_monomial, mainVariable_monomial _ one_ne_zero, Finsupp.single]
  simp only [hk, reduceIte, Finset.max_singleton]

@[simp] theorem mainVariable_X [Nontrivial R] (i : σ) : (X i : R[σ]).mainVariable = i :=
  (pow_one (X i : R[σ])).symm ▸ mainVariable_X_pow i Nat.one_ne_zero

theorem mainVariable_eq_bot_iff_eq_C : p.mainVariable = ⊥ ↔ (∃ r : R, p = C r) := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ h.choose_spec ▸ mainVariable_C h.choose)
  simp only [mainVariable, Finset.sup_eq_bot_iff, mem_support_iff, ne_eq] at h
  have h (m : σ →₀ ℕ) (hs : m ∈ p.support) : m = 0 :=
    have hs : ¬p.coeff m = 0 := mem_support_iff.mp hs
    Finsupp.support_eq_empty.mp <| Finset.max_eq_bot.mp (h m hs)
  have h : p.support = ∅ ∨ p.support = {0} :=
    Finset.subset_singleton_iff.mp <| Finset.coe_subset_singleton.mp h
  use ∑ s ∈ p.support, p.coeff s
  nth_rewrite 1 [map_sum, as_sum p]
  apply Or.elim h <;> (intro h; exact h ▸ rfl)

theorem mainVariable_add_le (p q : R[σ]) :
    (p + q).mainVariable ≤ p.mainVariable ⊔ q.mainVariable := by
  rewrite [mainVariable, mainVariable, mainVariable, ← Finset.sup_union]
  apply Finset.sup_le
  intro _ smem
  apply Finset.le_sup (support_add smem)

theorem mainVariable_mul_le (p q : R[σ]) :
    (p * q).mainVariable ≤ p.mainVariable ⊔ q.mainVariable := by
  apply Finset.sup_le
  intro s smem
  by_contra hs
  have ⟨hs1, hs2⟩ : (∀ x, ¬p.coeff x = 0 → x.support.max < s.support.max) ∧
      (∀ x, ¬q.coeff x = 0 → x.support.max < s.support.max):= by
    simp only [not_le, max_lt_iff] at hs
    have : ⊥ < s.support.max := bot_lt_of_lt hs.1
    simpa [mainVariable, Finset.sup_lt_iff this, mem_support_iff, ne_eq] using hs
  simp only [mem_support_iff, coeff_mul, ne_eq] at smem
  rcases Finset.exists_ne_zero_of_sum_ne_zero smem with ⟨⟨t1, t2⟩, ht1, ht2⟩
  simp only [Finset.mem_antidiagonal, ne_eq] at ht1 ht2
  rcases ne_zero_and_ne_zero_of_mul ht2 with ⟨ht2, ht3⟩
  absurd max_lt (hs1 t1 ht2) (hs2 t2 ht3)
  rewrite [not_lt, ← ht1, ← Finset.max_union]
  exact Finset.max_mono Finsupp.support_add

theorem mainVariable_sum_le {α : Type*} (s : Finset α) (f : α → R[σ]) :
    (∑ a ∈ s, f a).mainVariable ≤ s.sup (fun a ↦ (f a).mainVariable) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s has ih
  rewrite [Finset.sum_insert has, Finset.sup_insert]
  exact (mainVariable_add_le _ _).trans (sup_le_sup_left ih _)

theorem mainVariable_prod_le {α : Type*} (s : Finset α) (f : α → R[σ]) :
    (∏ a ∈ s, f a).mainVariable ≤ s.sup (fun a ↦ (f a).mainVariable) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sup_empty, le_bot_iff]; apply mainVariable_C
  | insert a s has ih =>
    rewrite [Finset.prod_insert has, Finset.sup_insert]
    exact (mainVariable_mul_le _ _).trans (sup_le_sup_left ih _)

theorem degreeOf_eq_zero_of_mainVariable_lt {i : σ} :
    p.mainVariable < i → p.degreeOf i = 0 := fun h ↦ by
  rewrite [degreeOf_eq_sup, ← Nat.bot_eq_zero, Finset.sup_eq_bot_iff, Nat.bot_eq_zero]
  intro s hs
  refine Finsupp.notMem_support_iff.mp ?_
  contrapose! h
  apply le_trans (Finset.le_max h)
  apply mainVariable_def p ▸ Finset.le_sup hs

theorem degreeOf_of_mainVariable_eq_bot (i : σ) : p.mainVariable = ⊥ → p.degreeOf i = 0 :=
  fun h ↦ degreeOf_eq_zero_of_mainVariable_lt (h ▸ WithBot.bot_lt_coe i)

end MainVariable

section MainDegree

variable {i j : σ}

theorem ne_zero_of_degreeOf_ne_zero : p.degreeOf i ≠ 0 → p ≠ 0 :=
  mt fun h ↦ h ▸ degreeOf_zero i

theorem le_degreeOf_of_mem_support (i : σ) {s : σ →₀ ℕ} :
    s ∈ p.support → s i ≤ p.degreeOf i := fun h ↦ by
  by_cases si : s i = 0
  · simp only [si, zero_le]
  have : 0 < s i := Nat.zero_lt_of_ne_zero si
  rewrite [degreeOf_eq_sup, Finset.le_sup_iff this]
  use s

theorem notMem_support_of_degreeOf_lt (i : σ) {s : σ →₀ ℕ} : p.degreeOf i < s i → s ∉ p.support :=
  fun h ↦ by contrapose! h; exact le_degreeOf_of_mem_support i h

@[simp] theorem degreeOf_X_self_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : R[σ]) ^ k).degreeOf i = k :=
  by rw [X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero, Finsupp.single_eq_same]

theorem degreeOf_X_pow_of_ne (k : ℕ) (h : i ≠ j) : ((X j : R[σ]) ^ k).degreeOf i = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]

@[simp] theorem degreeOf_X_self [Nontrivial R] (i : σ) : (X i : R[σ]).degreeOf i = 1 :=
  pow_one (X i : R[σ]) ▸ degreeOf_X_self_pow i 1

theorem degreeOf_X_of_ne (h : i ≠ j) : (X j : R[σ]).degreeOf i = 0 :=
  pow_one (X j : R[σ]) ▸ degreeOf_X_pow_of_ne 1 h

theorem degreeOf_mul_X_self_pow_eq_add_of_ne_zero (i : σ) (k : ℕ) (h : p ≠ 0) :
    (p * X i ^ k).degreeOf i = p.degreeOf i + k := by
  induction k with
  | zero => rw [pow_zero, mul_one, add_zero]
  | succ k hk =>
    have : p * X i ^ k ≠ 0 := by
      rcases ne_zero_iff.mp h with ⟨s, hs⟩
      refine ne_zero_iff.mpr ⟨s + Finsupp.single i k, ?_⟩
      rewrite [X_pow_eq_monomial, coeff_mul_monomial, mul_one]
      exact hs
    rewrite [pow_add, pow_one, ← mul_assoc]
    rw [(degreeOf_mul_X_eq_degreeOf_add_one_iff i _).mpr this, hk, add_assoc]

theorem degreeOf_mul_X_pow_of_ne (k : ℕ) (h : i ≠ j) :
    (p * X j ^ k).degreeOf i = p.degreeOf i := by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, degreeOf_mul_X_of_ne _ h, hk]

theorem degreeOf_add_eq_of_degreeOf_lt (h : q.degreeOf i < p.degreeOf i) :
    (p + q).degreeOf i = p.degreeOf i := by
  apply le_antisymm ((max_eq_left_of_lt h) ▸ degreeOf_add_le i p q)
  nth_rewrite 2 [degreeOf_eq_sup]
  apply (Finset.le_sup_iff <| Nat.zero_lt_of_lt h).mpr
  have : p.support.Nonempty := by apply support_nonempty.mpr; contrapose! h; simp [h]
  have ⟨s, hs1, hs2⟩ := Finset.exists_mem_eq_sup _ this (fun s ↦ s i)
  rewrite [← degreeOf_eq_sup i p] at hs2
  refine ⟨s, ?_, by rw [hs2]⟩
  have : s ∉ q.support := by contrapose! h; exact hs2 ▸ le_degreeOf_of_mem_support i h
  simp only [mem_support_iff, ne_eq, coeff_add, not_not] at hs1 ⊢ this
  rewrite [this, add_zero]
  exact hs1

theorem degreeOf_eq_of_degreeOf_add_lt {p q : R[σ]}
    (h : (p + q).degreeOf i < p.degreeOf i) : p.degreeOf i = q.degreeOf i := by
  contrapose! h
  apply le_trans (Nat.le_max_left _ (q.degreeOf i))
  rcases Nat.lt_or_lt_of_ne h with h | h
  · simp only [add_comm p q, degreeOf_add_eq_of_degreeOf_lt h, max_eq_right_of_lt h, le_refl]
  simp only [degreeOf_add_eq_of_degreeOf_lt h, max_eq_left_of_lt h, le_refl]

variable [LinearOrder σ] {c : σ}

/-- The "main degree" of `p`: the degree of `p` with respect to its main variable.
If `mainVariable p = ⊥` (i.e., `p` is a constant or zero), the degree is 0. -/
noncomputable def mainDegree (p : R[σ]) : ℕ :=
  match mainVariable p with
  | ⊥ => 0
  | some c => p.degreeOf c

theorem mainDegree_of_mainVariable_isSome : p.mainVariable = c → p.mainDegree = p.degreeOf c :=
  fun h ↦ by rw [mainDegree, h]

theorem mainDegree_of_mainVariable_isSome' :
    p.mainVariable = c → p.mainDegree = p.support.sup (fun s ↦ s c) :=
  fun h ↦ by rw [mainDegree_of_mainVariable_isSome h, degreeOf_eq_sup]

theorem mainDegree_eq_zero_iff : p.mainDegree = 0 ↔ p.mainVariable = ⊥ where
  mp h :=
    match hc : p.mainVariable with
    | ⊥ => rfl
    | some c => by
      simp only [mainDegree_of_mainVariable_isSome hc, degreeOf_eq_sup] at h
      rewrite [← Nat.bot_eq_zero, Finset.sup_eq_bot_iff] at h
      simp only [mem_support_iff, ne_eq, Nat.bot_eq_zero] at h
      have : ⊥ < p.mainVariable := by rewrite [hc]; exact compareOfLessAndEq_eq_lt.mp rfl
      rcases (Finset.le_sup_iff this).mp <| ge_of_eq p.mainVariable_def with ⟨t, ht1, ht2⟩
      absurd (Finset.sup_le_iff.mp <| le_of_eq <| p.mainVariable_def.symm.trans hc) t ht1
      have h := Finsupp.notMem_support_iff.mpr (h t <| mem_support_iff.mp ht1)
      have : c ≠ t.support.max := by contrapose! h; exact Finset.mem_of_max h.symm
      exact not_le_of_gt <| lt_of_le_of_ne (le_of_eq_of_le hc.symm ht2) this
  mpr h := by rw [mainDegree, h]

theorem mainDegree_eq_zero_iff' : p.mainDegree = 0 ↔ (∃ r : R, p = C r) :=
  Iff.trans mainDegree_eq_zero_iff mainVariable_eq_bot_iff_eq_C

theorem degreeOf_mainVariable_ne_zero : p.mainVariable = c → p.degreeOf c ≠ 0 := fun h ↦
  have := (not_iff_not.mpr mainDegree_eq_zero_iff).mpr (h ▸ WithBot.coe_ne_bot)
  mainDegree_of_mainVariable_isSome h ▸ this

theorem mainVariable_mem_degrees : p.mainVariable = c → c ∈ p.degrees := fun h ↦
  have := degreeOf_mainVariable_ne_zero h; Multiset.count_ne_zero.mp (degreeOf_def c p ▸ this)

@[simp] theorem mainDegree_zero : (0 : R[σ]).mainDegree = 0 := rfl

@[simp] theorem mainDegree_monomial {s : σ →₀ ℕ} {r : R} (hr : r ≠ 0)
    (hs : s.support.max = c) : (monomial s r).mainDegree = s c := by
  rewrite [mainDegree_of_mainVariable_isSome <| (mainVariable_monomial s hr).trans hs]
  exact degreeOf_monomial_eq s c hr

@[simp] theorem mainDegree_C (r : R) : (C r : R[σ]).mainDegree = 0 :=
  mainDegree_eq_zero_iff.mpr <| mainVariable_C r

@[simp] theorem mainDegree_X_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : R[σ]) ^ k).mainDegree = k := by
  by_cases hk : k = 0
  · exact hk ▸ pow_zero (X i : R[σ]) ▸ mainDegree_C 1
  have : (Finsupp.single i k).support.max = i := by rw [Finsupp.support_single_ne_zero i hk]; rfl
  rw [X_pow_eq_monomial, mainDegree_monomial one_ne_zero this, Finsupp.single_eq_same]

@[simp] theorem mainDegree_X [Nontrivial R] (i : σ) : (X i : R[σ]).mainDegree = 1 :=
  pow_one (X i : R[σ]) ▸ mainDegree_X_pow i 1

end MainDegree

section Rank

variable [LinearOrder σ] {p : R[σ]}

/-- The rank of a polynomial `p` is the pair `(mainVariable p, degree p)`.
Ranks are ordered lexicographically. -/
noncomputable def rank (p : R[σ]) : WithBot σ ×ₗ ℕ := (p.mainVariable, p.mainDegree)

theorem rank_def : p.rank = (p.mainVariable, p.mainDegree) := rfl

theorem rank_eq : p.rank = q.rank ↔ p.mainVariable = q.mainVariable ∧ p.mainDegree = q.mainDegree :=
  Prod.mk_inj

instance instPreorder : Preorder R[σ] where
  le := InvImage (· ≤ ·) rank
  le_refl := fun _ ↦ by rw [InvImage]
  le_trans := fun _ _ _ ↦ le_trans

theorem le_def' : p ≤ q ↔ p.rank ≤ q.rank := Iff.rfl

noncomputable instance instDecidableLE : DecidableLE R[σ] := fun _ _ ↦
  decidable_of_iff _ le_def'.symm

noncomputable instance instDecidableLT : DecidableLT R[σ] := decidableLTOfDecidableLE

instance instIsTotalLe : Std.Total (@LE.le R[σ] _) where
  total p q := le_total p.rank q.rank

theorem le_def : p ≤ q ↔ p.mainVariable < q.mainVariable ∨
    p.mainVariable = q.mainVariable ∧ p.mainDegree ≤ q.mainDegree := Prod.lex_def

theorem le_iff : (p ≤ q) ↔ ¬(p.mainVariable < q.mainVariable) →
    (p.mainVariable = q.mainVariable ∧ p.mainDegree ≤ q.mainDegree) :=
  Iff.trans le_def <| Decidable.or_iff_not_imp_left

theorem mainVariable_le_of_le : p ≤ q → p.mainVariable ≤ q.mainVariable :=
  fun h ↦ Or.elim (le_def.mp h) le_of_lt (fun h ↦ le_of_eq h.1)

theorem lt_def' : p < q ↔ p.rank < q.rank := Iff.trans lt_iff_le_not_ge (by
  rewrite [le_def', le_def', not_le, and_iff_right_iff_imp]
  exact le_of_lt)

theorem lt_def : p < q ↔ p.mainVariable < q.mainVariable ∨
    p.mainVariable = q.mainVariable ∧ p.mainDegree < q.mainDegree :=
  Iff.trans lt_def' Prod.lex_def

theorem lt_iff : p < q ↔ ¬(p.mainVariable < q.mainVariable)
    → p.mainVariable = q.mainVariable ∧ p.mainDegree < q.mainDegree :=
  Iff.trans lt_def <| Decidable.or_iff_not_imp_left

theorem lt_of_mainVariable_lt : p.mainVariable < q.mainVariable → p < q :=
  fun h ↦ lt_def.mpr <| Or.inl h

@[simp] theorem not_lt_iff_ge : ¬(p < q) ↔ q ≤ p := by rw [le_def', lt_def', not_lt]

@[simp] theorem not_le_iff_gt : ¬(p ≤ q) ↔ q < p := by rw [le_def', lt_def', not_le]

theorem X_lt_of_lt [Nontrivial R] {i j : σ} : i < j → (X i : R[σ]) < X j := fun h ↦ by
  apply lt_of_mainVariable_lt; rewrite [mainVariable_X, mainVariable_X, WithBot.coe_lt_coe]; exact h

instance instSetoid : Setoid (R[σ]) := AntisymmRel.setoid R[σ] (· ≤ ·)

noncomputable instance instDecidableRelEquiv : @DecidableRel R[σ] R[σ] (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd

theorem equiv_def'' : p ≈ q ↔ p ≤ q ∧ q ≤ p := Iff.rfl

theorem equiv_def' : p ≈ q ↔ p.rank = q.rank := Iff.trans equiv_def''
  (by rewrite [le_def', le_def']; exact Std.le_antisymm_iff)

theorem equiv_def : p ≈ q ↔ ¬p < q ∧ ¬q < p := Iff.trans equiv_def''
  (by rw [not_lt_iff_ge, not_lt_iff_ge, and_comm])

theorem equiv_iff : p ≈ q ↔ p.mainVariable = q.mainVariable ∧ p.mainDegree = q.mainDegree :=
  Iff.trans equiv_def' rank_eq

theorem le_iff_lt_or_equiv : p ≤ q ↔ p < q ∨ p ≈ q := le_iff_lt_or_antisymmRel

theorem lt_of_equiv_of_lt {r : R[σ]} : p ≈ q → q < r → p < r := lt_of_antisymmRel_of_lt

theorem lt_of_lt_of_equiv {r : R[σ]} : p < q → q ≈ r → p < r := lt_of_lt_of_antisymmRel

theorem equiv_of_le_of_ge : p ≤ q → q ≤ p → p ≈ q := And.intro

protected theorem zero_le : 0 ≤ p := by
  apply le_def'.mpr
  rewrite [rank, mainVariable_zero, mainDegree_zero]
  exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl p.rank

end Rank

section WellFounded

variable [LinearOrder σ]

theorem wellFoundedLT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT R[σ] → WellFoundedLT σ := fun h ↦ by
  rewrite [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h ⊢
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf⟩
  exact ⟨X ∘ f, fun n ↦ X_lt_of_lt <| hf n⟩

instance instWellFoundedLT [WellFoundedLT σ] : WellFoundedLT R[σ] :=
  Subrelation.isWellFounded (InvImage _ _) lt_def'.mp

theorem wellFoundedLT_iff [Nontrivial R] : WellFoundedLT R[σ] ↔ WellFoundedLT σ :=
  ⟨wellFoundedLT_variables_of_wellFoundedLT, @instWellFoundedLT _ _ _ _⟩

variable [WellFoundedLT R[σ]] (PS : Set R[σ])

theorem Set.has_min (h : PS.Nonempty) : ∃ p ∈ PS, ∀ q ∈ PS, ¬q < p :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (R[σ]) _ _
  WellFounded.has_min this PS h

noncomputable def Set.min (h : PS.Nonempty) : R[σ] := Exists.choose (has_min PS h)

theorem Set.min_mem (h : PS.Nonempty) : (min PS h) ∈ PS := (Exists.choose_spec (has_min PS h)).1

end WellFounded

section Reduced

variable [DecidableEq R] [LinearOrder σ] {p q r : R[σ]}

/-- `q` is reduced with respect to `p`if `q = 0` or
if the degree of `q` in the main variable of `p` is strictly less than the degree of `p`.

Note: if `p` is a constant, then no non-zero `q` is reduced with respect to `p`. -/
def reducedTo (q p : R[σ]) : Prop :=
  if q = 0 then True
  else
    match p.mainVariable with
    | ⊥ => False
    | some c => q.degreeOf c < p.degreeOf c

theorem zero_reducedTo (p : R[σ]) : (0 : R[σ]).reducedTo p := trivial

theorem not_reducedTo_of_bot_mainVariable (hq : q ≠ 0) : p.mainVariable = ⊥ → ¬q.reducedTo p :=
  fun hp ↦ by simp only [reducedTo, hq, reduceIte, hp, not_false_eq_true]

theorem mainVariable_ne_bot_of_reducedTo (hq : q ≠ 0) : q.reducedTo p → p.mainVariable ≠ ⊥ :=
  fun hp con ↦ not_reducedTo_of_bot_mainVariable hq con hp

theorem reducedTo_iff {c : σ} (hp : p.mainVariable = c) (hq : q ≠ 0) :
    q.reducedTo p ↔ q.degreeOf c < p.degreeOf c := by simp only [reducedTo, hq, reduceIte, hp]

noncomputable instance : DecidableRel (@reducedTo R σ _ _ _) := fun q p ↦
  if hq : q = 0 then isTrue <| hq ▸ zero_reducedTo p
  else
    match hp : p.mainVariable with
    | ⊥ => isFalse <| not_reducedTo_of_bot_mainVariable hq hp
    | some _ => decidable_of_iff _ (reducedTo_iff hp hq).symm

theorem reducedTo_of_mainVariable_lt (h : q.mainVariable < p.mainVariable) : q.reducedTo p := by
  if hq : q = 0 then exact hq ▸ zero_reducedTo p
  else
    rcases WithBot.ne_bot_iff_exists.mp <| LT.lt.ne_bot h with ⟨c, hc⟩
    apply (reducedTo_iff hc.symm hq).mpr
    rewrite [degreeOf_eq_zero_of_mainVariable_lt (hc ▸ h)]
    exact Nat.pos_of_ne_zero <| degreeOf_mainVariable_ne_zero hc.symm

theorem reducedTo_congr_right : p ≈ q → (r.reducedTo p ↔ r.reducedTo q) := fun h ↦
  have (p q : R[σ]) (h : p ≈ q) : r.reducedTo p → r.reducedTo q := by
    have : p.mainVariable = q.mainVariable ∧ p.mainDegree = q.mainDegree := equiv_iff.mp h
    simp only [reducedTo, if_true_left]
    intro hr1 hr2
    match hc : q.mainVariable with
    | none => simp [hr2, hc ▸ this.1] at hr1
    | some c =>
      have hc' := hc ▸ this.1
      simp [hr2, hc', mainDegree_of_mainVariable_isSome hc' ▸ this.2] at hr1
      simp only [mainDegree_of_mainVariable_isSome hc ▸ hr1]
  ⟨this p q h, this q p h.symm⟩

theorem reducedTo_iff_gt_of_mainVariable_eq (hq : q ≠ 0) (h : q.mainVariable = p.mainVariable) :
    q.reducedTo p ↔ q < p where
  mp hl :=
    match hp : p.mainVariable with
    | ⊥ => absurd hl <| not_reducedTo_of_bot_mainVariable hq hp
    | some c => lt_def.mpr <| Or.inr ⟨h, by
      rw [mainDegree_of_mainVariable_isSome hp, mainDegree_of_mainVariable_isSome <| h.trans hp]
      exact (reducedTo_iff hp hq).mp hl⟩
  mpr hr :=
    have : q.mainDegree < p.mainDegree := (lt_iff.mp hr <| Eq.not_lt h).2
    match hp : p.mainVariable with
    | ⊥ => by
      rewrite [mainDegree_eq_zero_iff.mpr hp, mainDegree_eq_zero_iff.mpr (h ▸ hp)] at this
      exact absurd this <| Nat.not_lt_zero 0
    | some c => by
      rw [mainDegree_of_mainVariable_isSome hp, mainDegree_of_mainVariable_isSome (h ▸ hp)] at this
      exact (reducedTo_iff hp hq).mpr this

theorem not_reduceTo_self (h : p ≠ 0) : ¬p.reducedTo p :=
  mt (reducedTo_iff_gt_of_mainVariable_eq h rfl).mp (lt_irrefl p)

theorem mainVariable_lt_of_reducedTo_of_le (h1 : q ≠ 0) (h2 : p ≤ q) (h3 : q.reducedTo p) :
    p.mainVariable < q.mainVariable := by
  by_contra con
  have con : q.mainVariable = p.mainVariable :=
    le_antisymm (not_lt.mp con) (mainVariable_le_of_le h2)
  have := (reducedTo_iff_gt_of_mainVariable_eq h1 con).mp h3
  exact absurd h2 <| not_le_iff_gt.mpr this

theorem lt_of_reducedTo_of_le (h1 : q ≠ 0) (h2 : p ≤ q) (h3 : q.reducedTo p) : p < q :=
  lt_of_mainVariable_lt <| mainVariable_lt_of_reducedTo_of_le h1 h2 h3

variable {α : Type*} [Membership R[σ] α] {p q : R[σ]} {a : α}

/-- `q` is reduced with respect to a set `a`
if it is reduced with respect to all elements of `a`. -/
def reducedToSet (q : R[σ]) (a : α) : Prop := ∀ p ∈ a, q.reducedTo p

noncomputable instance : @DecidableRel _ (List R[σ]) reducedToSet :=
  fun _ ↦ List.decidableBAll _

theorem reducedToSet_def : q.reducedToSet a ↔ ∀ p ∈ a, q.reducedTo p := Iff.rfl

theorem zero_reducedToSet : (0 : R[σ]).reducedToSet a := fun _ _ ↦ zero_reducedTo _

end Reduced

end MvPolynomial
