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
lemma lCS_non_zero : ∀ p ∈ lCS, p ≠ 0 := fun p hp ↦ by
  simp only [lCS, p₅, Fin.isValue, p₆, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · rw [hp]
    decide +kernel
  rw [hp]
  decide +kernel
lemma lCS_pairwise : lCS.Pairwise fun p q ↦ p.vars.max < q.vars.max := sorry

def CS : TriangularSet (Fin 8) ℚ := TriangularSet.list lCS lCS_non_zero lCS_pairwise

theorem hCS : CS.isCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold isSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    ----------
    simp only [l, List.mem_cons, List.not_mem_nil, or_false, p₁, p₂, p₃, p₄] at hg
    rcases hg with hg | hg | hg | hg
    · use [99, 99]
      use [99, 99]
      simp [CS, TriangularSet.length_list, TriangularSet.list_apply, lCS]

      sorry
    ·
      sorry
    ·
      sorry
    sorry
    ----------
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS} = {p | p ∈ lCS} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq, CS]
    exact TriangularSet.mem_list_iff lCS_non_zero lCS_pairwise
  rw [l, this, lCS]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have heq1 (p q : ℚ[Fin 8]) : {r | r = p ∨ r = q} = {p, q} := Set.insert_def ..
  have heq2 (p1 p2 p3 p4 : ℚ[Fin 8]) : {r | r = p1 ∨ r = p2 ∨ r = p3 ∨ r = p4} = {p1, p2, p3, p4} :=
    Set.insert_def ..
  rw [heq1, heq2]
  ----------

  ----------
  sorry

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₅ = 0 := by
  suffices ∀ p ∈ [p₅], p = 0 by simpa using this
  apply forall_eq_zero_of_vanishingSet_subset l
  · have : ∃ (I : ℚ[Fin 8]) (qs : List ℚ[Fin 8]),
        qs.length = CS.length ∧ I * p₅ = ∑ i : Fin qs.length, qs[i] * CS i := sorry
    rcases this with ⟨I, qs, hl, heq⟩
    simp only [vanishingSet, aeval_eq_eval, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      Set.setOf_subset_setOf]
    intro x hx
    have h : I.eval x ≠ 0 := by
      
      sorry
    have hx : ∀ p ∈ CS, (eval x) p = 0 := hCS.2 hx
    have : (I * p₅).eval x = 0 := by
      simp only [heq, Fin.getElem_fin, map_sum, map_mul]
      have (i : Fin qs.length) : (CS i).eval x = 0 := by
        exact hx _ <| TriangularSet.apply_mem <| hl ▸ i.2
      simp only [this, mul_zero, Finset.sum_const_zero]
    rewrite [map_mul] at this
    exact (mul_eq_zero_iff_left h).mp this
  simp [l, h₁, h₂, h₃, h₄]

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₆ = 0 := by
  simp only [p₁, p₂, p₃, p₄, p₆] at *
  sorry

end
