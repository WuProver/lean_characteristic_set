import MonomialOrderedPolynomial
import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet MonomialOrder

scoped[MvPolynomial] notation:9000 R "[" σ "]" => MvPolynomial σ R

noncomputable section

def l : List ℚ[Fin 8] :=
   [ X 1 - X 0 - (X 3 - X 2), X 2 - X 0 - (X 3 - X 1), X 5 - X 4 - (X 7 - X 6), X 6 - X 4 - (X 7 - X 5)]

def lCS : List ℚ[Fin 8] := [X 0 + X 3 - (X 1 + X 2), X 4 + X 7 - (X 5 + X 6)]

def computed_CS : List ℚ[Fin 8] := [X 0 + X 3 - (X 1 + X 2), X 4 + X 7 - (X 5 + X 6)]

lemma CS_non_zero : 0 ∉ computed_CS := by
  simp only [computed_CS, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false, not_or]
  decide +kernel


lemma CS_isChain : computed_CS.IsChain fun p q ↦ p.vars.max < q.vars.max := by
  sorry

def CS : TriangularSet (Fin 8) ℚ := TriangularSet.mk computed_CS CS_non_zero CS_isChain

theorem hCS : CS.IsCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold IsSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
      ----------
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg | hg
    · use [1, 1], [1, 1]
      simp
      refine ⟨rfl, ?_⟩
      simp only [hg, CS, ← TriangularSet.toList_getElem?_getD, Fin.isValue]


      sorry
    ·
      sorry
    ·
      sorry
    sorry
    ---------
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
