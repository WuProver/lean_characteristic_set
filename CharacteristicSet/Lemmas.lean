import Mathlib.Algebra.MvPolynomial.Variables

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {p q : MvPolynomial σ R}

section Degrees

theorem degrees_eq_zero_iff_support_subset_zero : p.degrees = 0 ↔ p.support ⊆ {0} := by
  rewrite [Finset.subset_singleton_iff', Multiset.eq_zero_iff_forall_notMem]
  refine ⟨fun h s hs ↦ ?_, fun h i hi ↦ ?_⟩
  · apply Finsupp.support_eq_empty.mp
    refine Finset.eq_empty_of_forall_notMem fun i ↦ ?_
    have := (not_iff_not.mpr mem_degrees).mp (h i)
    have := not_and.mp <| not_exists.mp this s
    exact this (mem_support_iff.mp hs)
  rcases mem_degrees.mp hi with ⟨s, hs1, hs2⟩
  have := Finsupp.support_eq_empty.mpr (h s <| mem_support_iff.mpr hs1) ▸ hs2
  exact absurd this (Finset.notMem_empty i)

end Degrees

section DegreeOf


@[simp] theorem degreeOf_X_self [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).degreeOf i = 1 :=
  by classical rw [degreeOf_X, if_pos rfl]

lemma ne_zero_of_degreeOf_ne_zero {i : σ} : p.degreeOf i ≠ 0 → p ≠ 0 :=
  mt fun h ↦ h ▸ degreeOf_zero i

@[simp] theorem degreeOf_X_self_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : MvPolynomial σ R) ^ k).degreeOf i = k := by
  rw [X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero, Finsupp.single_eq_same]

lemma le_degreeOf_of_mem_support (i : σ) {s : σ →₀ ℕ} :
    s ∈ p.support → s i ≤ p.degreeOf i := fun h ↦ by
  by_cases si : s i = 0
  · simp only [si, zero_le]
  have : 0 < s i := Nat.zero_lt_of_ne_zero si
  rewrite [degreeOf_eq_sup, Finset.le_sup_iff this]
  use s

lemma notMem_support_of_degreeOf_lt (i : σ) {s : σ →₀ ℕ} : p.degreeOf i < s i → s ∉ p.support :=
  fun h ↦ by contrapose! h; exact le_degreeOf_of_mem_support i h

theorem degreeOf_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    ((X j : MvPolynomial σ R) ^ k).degreeOf i = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]

theorem degreeOf_X_of_ne {i j : σ} (h : i ≠ j) : (X j : MvPolynomial σ R).degreeOf i = 0 :=
  pow_one (X j : MvPolynomial σ R) ▸ degreeOf_X_pow_of_ne 1 h

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

theorem degreeOf_mul_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    (p * X j ^ k).degreeOf i = p.degreeOf i := by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, degreeOf_mul_X_of_ne _ h, hk]

theorem degreeOf_add_eq_of_degreeOf_lt {i : σ} (h : q.degreeOf i < p.degreeOf i) :
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

theorem degreeOf_eq_of_degreeOf_add_lt {i : σ} (h : (p + q).degreeOf i < p.degreeOf i) :
    p.degreeOf i = q.degreeOf i := by
  contrapose! h
  apply le_trans (Nat.le_max_left _ (q.degreeOf i))
  rcases Nat.lt_or_lt_of_ne h with h | h
  · simp only [add_comm p q, degreeOf_add_eq_of_degreeOf_lt h, max_eq_right_of_lt h, le_refl]
  simp only [degreeOf_add_eq_of_degreeOf_lt h, max_eq_left_of_lt h, le_refl]

end DegreeOf

section Vars

theorem mem_vars_iff_degreeOf_ne_zero {i : σ} : i ∈ p.vars ↔ p.degreeOf i ≠ 0 := by
  classical rw [degreeOf, vars_def, Multiset.mem_toFinset, Multiset.count_ne_zero]

theorem support_subset_vars_of_mem_support {s : σ →₀ ℕ} (h : s ∈ p.support) :
    s.support ⊆ p.vars := fun i hi ↦ by
  contrapose! hi
  have := mem_support_notMem_vars_zero h hi
  exact Finsupp.notMem_support_iff.mpr this

theorem vars_eq_empty_iff_eq_C : p.vars = ∅ ↔ ∃ r : R, p = C r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.choose_spec ▸ vars_C⟩
  classical rewrite [vars_def, Multiset.toFinset_eq_empty] at h
  have h : p.support = ∅ ∨ p.support = {0} :=
    Finset.subset_singleton_iff.mp <| degrees_eq_zero_iff_support_subset_zero.mp h
  use ∑ s ∈ p.support, p.coeff s
  nth_rewrite 1 [map_sum, as_sum p]
  apply Or.elim h <;> (intro h; exact h ▸ rfl)

end Vars

end MvPolynomial
