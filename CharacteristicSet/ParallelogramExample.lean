import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet

noncomputable section

def p₁ : ℚ[Fin 8] := X 1 - X 0 - (X 3 - X 2)
def p₂ : ℚ[Fin 8] := X 2 - X 0 - (X 3 - X 1)
def p₃ : ℚ[Fin 8] := X 5 - X 4 - (X 7 - X 6)
def p₄ : ℚ[Fin 8] := X 6 - X 4 - (X 7 - X 5)

def p₅ : ℚ[Fin 8] := X 0 + X 3 - (X 1 + X 2)
def p₆ : ℚ[Fin 8] := X 4 + X 7 - (X 5 + X 6)

example (h₁ : p₁ = 0) (h₂ : p₂ = 0) (h₃ : p₃ = 0) (h₄ : p₄ = 0) : p₅ = 0 ∧ p₆ = 0 := by
  constructor
  · rw [p₁] at h₁
    rw [p₂] at h₂
    rw [p₃] at h₃
    rw [p₄] at h₄
    rw [p₅]
    grind
  · rw [p₁] at h₁
    rw [p₂] at h₂
    rw [p₃] at h₃
    rw [p₄] at h₄
    rw [p₆]
    grind



end
