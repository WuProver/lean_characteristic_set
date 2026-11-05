/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic

/-! Coordinate geometry definitions and lemmas shared by the bridge examples. -/
@[expose] public section

namespace CharacteristicSet.Bridge.Examples.Geometry

/-- The real coordinate plane, with its usual affine structure. -/
abbrev Point := ℝ × ℝ
/-- Euclidean squared distance in coordinates. -/
def sqDist (a b : Point) : ℝ := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2
/-- Four points have a common circle center. -/
def OnCommonCircle (a b c p : Point) : Prop :=
  ∃ o, sqDist a o = sqDist b o ∧ sqDist a o = sqDist c o ∧ sqDist a o = sqDist p o
/-- The foot lies on the whole side line and its displacement from the point is perpendicular. -/
def IsPerpendicularFoot (p a b d : Point) : Prop :=
  (d.1 - a.1) * (b.2 - a.2) - (d.2 - a.2) * (b.1 - a.1) = 0 ∧
  (p.1 - d.1) * (b.1 - a.1) + (p.2 - d.2) * (b.2 - a.2) = 0

/-- Three points with zero coordinate determinant are collinear, including coincident points. -/
theorem collinear_of_det_eq_zero (a b c : Point)
    (hc : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0) :
    Collinear ℝ ({a, b, c} : Set Point) := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  rcases c with ⟨cx, cy⟩
  change (bx - ax) * (cy - ay) - (by' - ay) * (cx - ax) = 0 at hc
  rw [collinear_iff_of_mem (Set.mem_insert (ax, ay) _)]
  by_cases hx : bx - ax = 0
  · by_cases hy : by' - ay = 0
    · refine ⟨(cx - ax, cy - ay), ?_⟩
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨0, by ext <;> simp_all [sub_eq_zero]⟩
      · exact ⟨1, by ext <;> simp⟩
    · have hcx : cx - ax = 0 := by
        have hh : (by' - ay) * (cx - ax) = 0 := by rw [hx] at hc; nlinarith
        exact (mul_eq_zero.mp hh).resolve_left hy
      refine ⟨(0, by' - ay), ?_⟩
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by ext <;> simp_all [sub_eq_zero]⟩
      · exact ⟨(cy - ay) / (by' - ay), by ext <;> simp_all [sub_eq_zero]⟩
  · refine ⟨(bx - ax, by' - ay), ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by ext <;> simp⟩
    · refine ⟨(cx - ax) / (bx - ax), ?_⟩
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, vadd_eq_add]
      all_goals field_simp
      all_goals nlinarith [hc]

/-- The circle equation after normalizing two vertices to `(0, 0)` and `(1, 0)`. -/
theorem OnCommonCircle.normalized_equation {U V : ℝ} {P : Point}
    (hc : OnCommonCircle (0, 0) (1, 0) (U, V) P) :
    V * (P.1 ^ 2 + P.2 ^ 2 - P.1) - (U ^ 2 + V ^ 2 - U) * P.2 = 0 := by
  obtain ⟨⟨ox, oy⟩, hAB, hAC, hAP⟩ := hc
  simp only [sqDist] at hAB hAC hAP
  linear_combination (V * P.1 - U * P.2) * hAB + P.2 * hAC - V * hAP

end CharacteristicSet.Bridge.Examples.Geometry
