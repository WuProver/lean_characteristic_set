import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet

noncomputable section

namespace em1

def p₁ : ℚ[Fin 2] := X 0 + X 1
def p₂ : ℚ[Fin 2] := X 0 * X 1 - 1

def l : List ℚ[Fin 2] := [p₁, p₂]

lemma hc₁ : p₁.mainVariable = 1 := sorry
example : p₁.mainDegree = 1 := sorry
example : p₂.mainVariable = 1 := sorry
example : p₂.mainDegree = 1 := sorry

def AS₁ : AscendingSet (Fin 2) ℚ :=
  ⟨TriangulatedSet.single p₁, TriangulatedSet.isAscendingSet_single p₁⟩
def AS₂ : AscendingSet (Fin 2) ℚ :=
  ⟨TriangulatedSet.single p₂, TriangulatedSet.isAscendingSet_single p₂⟩

def p₃ : ℚ[Fin 2] := X 0 ^ 2 + 1
lemma hc₃ : p₃.mainVariable = 0 := sorry
example : p₃.mainDegree = 2 := sorry

def lCS : List ℚ[Fin 2] := [p₃, p₁]
lemma lCS_non_zero : ∀ p ∈ lCS, p ≠ 0 := sorry
lemma lCS_pairwise : lCS.Pairwise fun p q ↦ p.mainVariable < q.mainVariable := by
  simpa [lCS, hc₁, hc₃] using compareOfLessAndEq_eq_lt.mp rfl

def CS : TriangulatedSet (Fin 2) ℚ := TriangulatedSet.list lCS lCS_non_zero lCS_pairwise

example : CS.isCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold isSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    simp only [l, List.mem_cons, List.not_mem_nil, or_false, p₁, p₂] at hg
    ----------
    use [0, 0]
    rcases hg with hg | hg
    · use [0, 1]
      simp [CS, TriangulatedSet.length_list, TriangulatedSet.list_apply, lCS, p₁, hg]
    use [-1, X 0]
    simp [CS, TriangulatedSet.length_list, TriangulatedSet.list_apply, lCS, p₃, p₁, hg]
    ring
    ----------
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS} = {p | p ∈ lCS} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq, CS]
    exact TriangulatedSet.mem_list_iff lCS_non_zero lCS_pairwise
  rw [l, this, lCS]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have (p q : ℚ[Fin 2]) : {r | r = p ∨ r = q} = {p, q} := Set.insert_def ..
  rw [this, this]
  ----------
  rw [p₁, p₂, p₃]
  apply Ideal.span_le.mpr
  refine Set.pair_subset ?_ ?_
  <;> apply Ideal.mem_span_pair.mpr
  · use X 0, -1
    ring
  use 1, 0
  ring
  ----------

example : l.zeroDecomposition = [CS] := sorry

end em1

namespace em2

def p₁ : ℚ[Fin 3] := X 0 * X 1 * X 2 - X 1 * X 2 ^ 2 - X 0 - X 1 - X 2
def p₂ : ℚ[Fin 3] := X 0 * X 1 - X 1 ^ 2 - X 0 + X 1 - X 2
def p₃ : ℚ[Fin 3] := X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2

def l : List ℚ[Fin 3] := [p₁, p₂, p₃]

def AS₁ : AscendingSet (Fin 3) ℚ :=
  ⟨TriangulatedSet.single p₁, TriangulatedSet.isAscendingSet_single p₁⟩
def AS₂ : AscendingSet (Fin 3) ℚ :=
  ⟨TriangulatedSet.single p₂, TriangulatedSet.isAscendingSet_single p₂⟩
def AS₃ : AscendingSet (Fin 3) ℚ :=
  ⟨TriangulatedSet.single p₃, TriangulatedSet.isAscendingSet_single p₃⟩

def c₁ : ℚ[Fin 3] := X 1 * (X 0 - 1) ^ 2 * (X 0 + 1) * (X 0 - 5)
def c₂ : ℚ[Fin 3] := - X 2 - X 1 ^ 2 + X 1 * X 0 + X 1 - X 0

lemma hIc₁ : c₁.initial = (X 0 - 1) ^ 2 * (X 0 + 1) * (X 0 - 5) := sorry
lemma hIc₂ : c₂.initial = -1 := sorry

def lCS₁ : List ℚ[Fin 3] := [c₁, c₂]
lemma lCS₁_non_zero : ∀ p ∈ lCS₁, p ≠ 0 := sorry
lemma lCS₁_pairwise : lCS₁.Pairwise fun p q ↦ p.mainVariable < q.mainVariable := sorry

def CS₁ : TriangulatedSet (Fin 3) ℚ := TriangulatedSet.list lCS₁ lCS₁_non_zero lCS₁_pairwise

example : CS₁.isCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold isSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hg
    ----------
    sorry
    ----------
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS₁} = {p | p ∈ lCS₁} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq, CS₁]
    exact TriangulatedSet.mem_list_iff lCS₁_non_zero lCS₁_pairwise
  rw [l, this, lCS₁]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have this₁ (p q : ℚ[Fin 3]) : {t | t = p ∨ t = q} = {p, q} := Set.insert_def ..
  have this₂ (p q r : ℚ[Fin 3]) : {t | t = p ∨ t = q ∨ t = r} = {p, q, r} := Set.insert_def ..
  rw [this₁, this₂]
  ----------
  rw [p₁, p₂, p₃]
  apply Ideal.span_le.mpr
  refine Set.insert_subset_iff.mpr ?_

  ----------
  sorry

example : l.zeroDecomposition = sorry := sorry

end em2
end
