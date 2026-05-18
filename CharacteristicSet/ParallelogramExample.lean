import MonomialOrderedPolynomial
import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet MonomialOrder

scoped[MvPolynomial] notation:9000 R "[" σ "]" => MvPolynomial σ R

noncomputable section

def p₁ : ℚ[Fin 8] := X 1 - X 0 - (X 3 - X 2)
def p₂ : ℚ[Fin 8] := X 2 - X 0 - (X 3 - X 1)
def p₃ : ℚ[Fin 8] := X 5 - X 4 - (X 7 - X 6)
def p₄ : ℚ[Fin 8] := X 6 - X 4 - (X 7 - X 5)

def p₅ : ℚ[Fin 8] := X 0 + X 3 - (X 1 + X 2)
def p₆ : ℚ[Fin 8] := X 4 + X 7 - (X 5 + X 6)

def l : List ℚ[Fin 8] := [p₁, p₂, p₃, p₄]

def lCS := [p₅, p₆]

lemma lCS_non_zero : 0 ∉ lCS := by
  simp only [lCS, p₅, Fin.isValue, p₆, List.mem_cons, List.not_mem_nil, or_false, not_or]
  decide +kernel

lemma lCS_isChain : lCS.IsChain fun p q ↦ p.vars.max < q.vars.max := by
  sorry

def CS : TriangularSet (Fin 8) ℚ := TriangularSet.mk lCS lCS_non_zero lCS_isChain

lemma a₅: p₅.initial = 1 := by
  rw [p₅]
  sorry

lemma a₆: p₆.initial = 1 := by
  rw [p₆]
  sorry




theorem hCS : CS.IsCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold IsSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    ----------
    simp only [l, List.mem_cons, List.not_mem_nil, or_false, p₁, p₂, p₃, p₄] at hg
    rcases hg with hg | hg | hg | hg
    · use [1, 1], [1, 1]
      have : CS.toList = lCS := rfl
      rw [TriangularSet.length, this]
      simp [← TriangularSet.toList_getElem?_getD, this, lCS]

      -- rw [a₅, a₆, p₅, p₆]
      sorry
    ·

      sorry
    · sorry
    sorry
    ----------
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS} = {p | p ∈ lCS} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq]
    have : lCS = CS.toList := rfl
    rw [this, TriangularSet.mem_toList_iff]
  rw [l, this, lCS]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have heq1 (p q : ℚ[Fin 8]) : {r | r = p ∨ r = q} = {p, q} := Set.insert_def ..
  have heq2 (p1 p2 p3 p4 : ℚ[Fin 8]) : {r | r = p1 ∨ r = p2 ∨ r = p3 ∨ r = p4} = {p1, p2, p3, p4} :=
    Set.insert_def ..
  rw [heq1, heq2]
  ----------

  ----------
  sorry

lemma foldrIdx_mul_eq_prod {σ R : Type*} [CommSemiring R] [LinearOrder σ] (es : List ℕ)
    (S : ℕ → MvPolynomial σ R) :
    es.foldrIdx (fun i e I ↦ (S i) ^ e * I) 1  = ∏ i : Fin es.length, (S i) ^ es[i] := by
  have (es : List ℕ) (S : ℕ → MvPolynomial σ R) : es.foldrIdx (fun i e I ↦ (S i) ^ e * I) 1
      = (∏ i ∈ Finset.range es.length, (S i) ^ es.getD i 0) := by
    induction es generalizing S with
    | nil => simp
    | cons e es ih =>
      simp only [List.foldrIdx, zero_add, List.length_cons]
      rewrite [List.foldrIdx_start, ih, add_comm _ 1, Finset.prod_range_add, Finset.prod_range_one]
      simp [add_comm]
  simp [this, Finset.prod_range]

lemma foldrIdx_add_eq_sum {σ R : Type*} [CommSemiring R] [LinearOrder σ]
    (qs : List (MvPolynomial σ R)) (S : ℕ → MvPolynomial σ R) :
    qs.foldrIdx (fun i q Q ↦ q * S i + Q) 0  = ∑ i : Fin qs.length, qs[i] * S i := by
  have (qs : List _) (S : ℕ → MvPolynomial σ R) : qs.foldrIdx (fun i q Q ↦ q * S i + Q) 0
      = (∑ i ∈ Finset.range qs.length, qs.getD i 0 * S i) := by
    induction qs generalizing S with
    | nil => simp
    | cons q qs ih =>
      simp only [List.foldrIdx, zero_add, List.length_cons]
      rewrite [List.foldrIdx_start, ih, add_comm _ 1, Finset.sum_range_add, Finset.sum_range_one]
      simp [add_comm]
  simp [this, Finset.sum_range]

example : { I : ℚ[Fin 8] // vanishingSet ℚ l \ vanishingSet' ℚ I ⊆ vanishingSet' ℚ p₅ } := by
  let I : ℚ[Fin 8] := 1
  have hI : ∃ (qs : List ℚ[Fin 8]),
    qs.length = CS.length ∧ I * p₅ = qs.foldrIdx (fun i q Q ↦ q * CS i + Q) 0 := by
    use [1, 0]
    have : CS.toList = lCS := rfl
    rw [TriangularSet.length, this]
    simp [← TriangularSet.toList_getElem?_getD, this, lCS]
    -----

    -----
    sorry
  use I
  intro x hx
  simp only [vanishingSet, vanishingSet', Set.mem_diff, Set.mem_setOf_eq] at hx ⊢
  have : (I * p₅).eval x = 0 := by
    rcases hI with ⟨qs, hl, heq⟩
    have heq := foldrIdx_add_eq_sum qs CS ▸ heq
    simp only [heq, Fin.getElem_fin, map_sum, map_mul]
    have (i : Fin qs.length) : (CS i).eval x = 0 := by
      exact (hCS.2 hx.1) _ <| TriangularSet.apply_mem <| hl ▸ i.2
    simp only [this, mul_zero, Finset.sum_const_zero]
  rewrite [map_mul] at this
  exact (mul_eq_zero_iff_left hx.2).mp this

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₅ = 0 := by

  sorry

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₆ = 0 := by

  sorry

end
