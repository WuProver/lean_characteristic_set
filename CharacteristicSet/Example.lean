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

example : isMinimal AS₁ l := sorry
lemma l_bs_eq : l.basicSet = AS₁ := sorry

def p₃ : ℚ[Fin 2] := X 0 ^ 2 - 1
lemma hc₃ : p₃.cls = 0 := sorry
example : p₃.degree = 2 := sorry

def lCS : List ℚ[Fin 2] := [p₃, p₁]
lemma lCS_non_zero : ∀ p ∈ lCS, p ≠ 0 := sorry
lemma lCS_pairwise : lCS.Pairwise fun p q ↦ p.cls < q.cls := by
  simpa [lCS, hc₁, hc₃] using compareOfLessAndEq_eq_lt.mp rfl

def CS : TriangulatedSet (Fin 2) ℚ := TriangulatedSet.list lCS lCS_non_zero lCS_pairwise

lemma l_cs_eq : l.characteristicSet = CS := by
  unfold List.characteristicSet List.characteristicSet.go
  rw [l_bs_eq, AS₁]
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
