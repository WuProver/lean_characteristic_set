/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSetTheory.Rank

/-!
# Basic sets

## Main declarations

* `BasicSetSpec`: The basic set interface used by the characteristic set algorithms.
* `BasicSetSpec.basicSet_append_comm`: Appending lists in either order gives equivalent basic sets.
* `BasicSetSpec.basicSet_append_toList_lt`: Adding a nonzero reduced polynomial to the list
  of a basic set strictly decreases its rank.

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]
* [Wen-Tsun Wu, *Mathematics Mechanization*][wen2000mathematics]

-/

@[expose] public section

/-- A basic set algorithm with the properties required for characteristic sets
and zero decomposition. -/
structure BasicSetSpec (σ R : Type*) [CommSemiring R] [DecidableEq R] [LinearOrder σ] where
  /-- Compute a basic set from a list of polynomials. -/
  basicSet : List (MvPolynomial σ R) → TriangularSet σ R
  basicSet_subset : ∀ l, ∀ ⦃p⦄, p ∈ basicSet l → p ∈ l
  basicSet_toList_equiv : ∀ l, basicSet (basicSet l).toList ≈ basicSet l
  /-- Order reduction property: appending a reduced element strictly decreases the basic set order.
  Crucial for proving termination of zero decomposition. -/
  basicSet_append_lt :
    ∀ {l₁ l₂}, (∃ p ∈ l₂, p ≠ 0 ∧ p.reducedToSet (basicSet l₁)) → basicSet (l₂ ++ l₁) < basicSet l₁
  -- For zero decomposition.
  basicSet_ge_of_subset : ∀ {l₁ l₂}, l₁ ⊆ l₂ → basicSet l₂ ≤ basicSet l₁
  initial_reduced : ∀ l p, p ∈ basicSet l → p.vars.max ≠ ⊥ → p.initial.reducedToSet (basicSet l)

namespace BasicSetSpec

open MvPolynomial TriangularSet

variable {σ R : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ]
variable (B : BasicSetSpec σ R) {l₁ l₂ : List (MvPolynomial σ R)}

theorem basicSet_append_comm : B.basicSet (l₁ ++ l₂) ≈ B.basicSet (l₂ ++ l₁) := by
  apply TriangularSet.equiv_of_le_of_ge
  · apply B.basicSet_ge_of_subset
    intro p hp
    simpa only [List.mem_append, or_comm] using hp
  · apply B.basicSet_ge_of_subset
    intro p hp
    simpa only [List.mem_append, or_comm] using hp

theorem basicSet_toList_le (l : List (MvPolynomial σ R)) :
    B.basicSet (B.basicSet l).toList ≤ B.basicSet l :=
  (TriangularSet.equiv_def''.mp (B.basicSet_toList_equiv l)).1

theorem reducedToSet_basicSet {p : MvPolynomial σ R} {S : TriangularSet σ R}
    (h : p.reducedToSet S) : p.reducedToSet (B.basicSet S.toList) :=
  fun q hq ↦ h q (mem_toList_iff.mp (B.basicSet_subset S.toList hq))

theorem basicSet_cons_lt {p : MvPolynomial σ R} (hp : p ≠ 0)
    (h : p.reducedToSet (B.basicSet l₁)) : B.basicSet (p :: l₁) < B.basicSet l₁ := by
  apply B.basicSet_append_lt (l₂ := [p])
  exact ⟨p, List.mem_cons_self, hp, h⟩

theorem basicSet_append_toList_lt (l : List (MvPolynomial σ R))
    (h : ∃ p ∈ l₂, p ≠ 0 ∧ p.reducedToSet (B.basicSet l)) :
    B.basicSet (l₂ ++ (B.basicSet l).toList) < B.basicSet l := by
  apply TriangularSet.lt_of_lt_of_equiv ?_ (B.basicSet_toList_equiv l)
  obtain ⟨p, hp, hp0, hred⟩ := h
  exact B.basicSet_append_lt ⟨p, hp, hp0, B.reducedToSet_basicSet hred⟩

end BasicSetSpec
