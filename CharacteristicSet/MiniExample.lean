import MonomialOrderedPolynomial
import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet

open MvPolynomial WeakAscendingSet MonomialOrder

scoped[MvPolynomial] notation:9000 R "[" σ "]" => MvPolynomial σ R

noncomputable section

def l : List ℚ[Fin 8] :=
   [ X 1 - X 0 - (X 3 - X 2), X 2 - X 0 - (X 3 - X 1), X 5 - X 4 - (X 7 - X 6), X 6 - X 4 - (X 7 - X 5)]

def lCS : List ℚ[Fin 8] := [X 0 + X 3 - (X 1 + X 2), X 4 + X 7 - (X 5 + X 6)]

lemma lCS_non_zero : ∀ p ∈ lCS, p ≠ 0 := fun p hp ↦ by
  simp only [lCS, Fin.isValue, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · rw [hp]
    decide +kernel
  rw [hp]
  decide +kernel

lemma lCS_pairwise : lCS.Pairwise fun p q ↦ p.vars.max < q.vars.max := by
  sorry

