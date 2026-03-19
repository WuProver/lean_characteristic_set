import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet

scoped[MvPolynomial] notation:9000 R "[" σ "]" => MvPolynomial σ R

noncomputable section

def p₁ : ℚ[Fin 8] := X 1 - X 0 - (X 3 - X 2)
def p₂ : ℚ[Fin 8] := X 2 - X 0 - (X 3 - X 1)
def p₃ : ℚ[Fin 8] := X 5 - X 4 - (X 7 - X 6)
def p₄ : ℚ[Fin 8] := X 6 - X 4 - (X 7 - X 5)

def p₅ : ℚ[Fin 8] := X 0 + X 3 - (X 1 + X 2)
def p₆ : ℚ[Fin 8] := X 4 + X 7 - (X 5 + X 6)

def l₁ : List (ℚ[Fin 8]) := [p₁, p₂, p₃, p₄]

def CS := l₁.cs

theorem hCS : CS.isCharacteristicSet ℚ l₁ := l₁.cs_isCharacteristicSet ℚ

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₅ = 0 := by
  suffices ∀ p ∈ [p₅], p = 0 by simpa using this
  apply forall_eq_zero_of_vanishingSet_subset l₁
  · have : (0 : ℚ[Fin 8]).isSetRemainder p₅ CS := by
      sorry
    rcases this with ⟨_, es, qs, ⟨hle, hlq⟩, heq⟩
    set I := (∏ i : Fin es.length, (CS ↑i).initial ^ es[i])
    simp only [vanishingSet, aeval_eq_eval, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      Set.setOf_subset_setOf]
    intro x hx
    have h : I.eval x ≠ 0 := by

      sorry
    have hx : ∀ p ∈ CS, (eval x) p = 0 := hCS.2 hx
    have : (I * p₅).eval x = 0 := by
      simp only [heq, add_zero, Fin.getElem_fin, map_sum, map_mul]
      have (i : Fin qs.length) : (CS i).eval x = 0 := by
        exact hx _ <| TriangularSet.apply_mem <| hlq ▸ i.2
      simp only [this, mul_zero, Finset.sum_const_zero]
    rewrite [map_mul] at this
    exact (mul_eq_zero_iff_left h).mp this
  simp [l₁, h₁, h₂, h₃, h₄]

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₆ = 0 := sorry

end
