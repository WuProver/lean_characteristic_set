import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet

noncomputable section

def p₁ : ℚ[Fin 2] := X 0 + X 1
def p₂ : ℚ[Fin 2] := X 0 * X 1 - 1

def l : List ℚ[Fin 2] := [p₁, p₂]

lemma hc₁ : p₁.cls = 1 := sorry
example : p₁.degree = 1 := sorry
example : p₂.cls = 1 := sorry
example : p₂.degree = 1 := sorry

def AS₁ : AscendingSet (Fin 2) ℚ :=
  ⟨TriangulatedSet.single p₁, TriangulatedSet.isAscendingSet_single p₁⟩
def AS₂ : AscendingSet (Fin 2) ℚ :=
  ⟨TriangulatedSet.single p₂, TriangulatedSet.isAscendingSet_single p₂⟩

-- lemma l_bs_eq : l.basicSet = AS₁ := sorry
-- example : isMinimal AS₁ l := by
--   rw [← l_bs_eq]
--   exact List.basicSet_isMinimal l

def p₃ : ℚ[Fin 2] := X 0 ^ 2 + 1
lemma hc₃ : p₃.cls = 0 := sorry
example : p₃.degree = 2 := sorry

def lCS : List ℚ[Fin 2] := [p₃, p₁]
lemma lCS_non_zero : ∀ p ∈ lCS, p ≠ 0 := sorry
lemma lCS_pairwise : lCS.Pairwise fun p q ↦ p.cls < q.cls := by
  simpa [lCS, hc₁, hc₃] using compareOfLessAndEq_eq_lt.mp rfl

def CS : TriangulatedSet (Fin 2) ℚ := TriangulatedSet.list lCS lCS_non_zero lCS_pairwise

example : CS.isCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold isSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    simp only [l, List.mem_cons, List.not_mem_nil, or_false, p₁, p₂] at hg
    use [0, 0]
    rcases hg with hg | hg
    · use [0, 1]
      simp [CS, TriangulatedSet.length_list, TriangulatedSet.list_apply, lCS, p₁, hg]
    use [-1, X 0]
    simp [CS, TriangulatedSet.length_list, TriangulatedSet.list_apply, lCS, p₃, p₁, hg]
    ring -- ring may fail if the system is more complex
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS} = {p | p ∈ lCS} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq, CS]
    exact TriangulatedSet.mem_list_iff lCS_non_zero lCS_pairwise
  rw [l, this, lCS]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have (p q : ℚ[Fin 2]) : {r | r = p ∨ r = q} = {p, q} := (Set.insert_def p {q}).symm
  rw [this p₃ p₁, this p₁ p₂]

  sorry

lemma l_cs_eq : l.characteristicSet = CS := by

  sorry

example : l.zeroDecomposition = [CS] := by
  unfold List.zeroDecomposition
  simp?
  refine ⟨l_cs_eq, fun _ s hs1 hs2 hl' ↦ ?_⟩
  rw [← hl', l_cs_eq, CS, TriangulatedSet.toList_list_eq lCS_non_zero lCS_pairwise]
  unfold List.zeroDecomposition
  simp?

  sorry

end
