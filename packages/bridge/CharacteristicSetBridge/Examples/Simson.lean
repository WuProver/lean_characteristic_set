/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import CharacteristicSetBridge.CharacteristicSet
public import CharacteristicSetBridge.Examples.Geometry
public import HexMvPoly.Ring
public meta import CharacteristicSet.Computable.CharacteristicSet
public meta import HexMvPoly.Ring
public meta import HexMvPoly.Operations

/-! The Wallace–Simson theorem in normalized real coordinates, proved by Wu elimination. -/
@[expose] public section

namespace CharacteristicSet.Bridge.Examples.Simson
open Hex HexMvPolyTheory Geometry
open scoped HexMvPolyTheory

-- Natural variable order: u, v, p, q, f, e, h, g.
-- Putting vertical foot coordinates first avoids artificial slope assumptions.
private abbrev Poly := MvPoly 8 Rat Mono.lex
private def u : Poly := MvPoly.X 0
private def v : Poly := MvPoly.X 1
private def p : Poly := MvPoly.X 2
private def q : Poly := MvPoly.X 3
private def f : Poly := MvPoly.X 4
private def e : Poly := MvPoly.X 5
private def h : Poly := MvPoly.X 6
private def g : Poly := MvPoly.X 7
private def equations : List Poly :=
  [v * (p ^ 2 + q ^ 2 - p) - (u ^ 2 + v ^ 2 - u) * q,
   v * (e - 1) - (u - 1) * f, (p - e) * (u - 1) + (q - f) * v,
   v * g - u * h, u * (p - g) + v * (q - h)]
private def conclusion : Poly := (e - p) * h - f * (g - p)

private def a : Poly := u ^ 2 + v ^ 2
private def b : Poly := (u - 1) ^ 2 + v ^ 2
private def cs : List Poly :=
  [v * (p ^ 2 + q ^ 2 - p) - (u ^ 2 + v ^ 2 - u) * q,
   -b * f + v * ((u - 1) * (p - 1) + v * q),
   v * (-b * e + (u - 1) ^ 2 * p + v ^ 2 + (u - 1) * v * q),
   -a * h + v ^ 2 * q + u * v * p,
   v * (-a * g + u * v * q + u ^ 2 * p)]

section
-- Use native evaluation for the concrete computations.
set_option linter.style.native false

private theorem computed : Computable.Standard.characteristicSet equations = cs := by
  native_decide

private theorem remainder_zero : Computable.setPseudoRem conclusion cs = 0 := by
  native_decide

private theorem initials : cs.map Computable.initial = [v, -b, -v * b, -a, -v * a] := by
  native_decide

end

private theorem polynomial_implication (U V P Q E F G H : ℝ) (hv : V ≠ 0)
    (hc : V * (P ^ 2 + Q ^ 2 - P) - (U ^ 2 + V ^ 2 - U) * Q = 0)
    (he : V * (E - 1) - (U - 1) * F = 0) (hep : (P - E) * (U - 1) + (Q - F) * V = 0)
    (hf : V * G - U * H = 0) (hfp : U * (P - G) + V * (Q - H) = 0) :
    (E - P) * H - F * (G - P) = 0 := by
  let x : Fin 8 → ℝ := ![U, V, P, Q, F, E, H, G]
  have hz : ∀ z ∈ equations, MvPolynomial.aeval x (toMvPolynomial z) = 0 := by
    simpa [equations, u, v, p, q, f, e, h, g, x] using And.intro hc ⟨he, hep, hf, hfp⟩
  have hv2 : 0 < V ^ 2 := sq_pos_of_ne_zero hv
  have ha : U ^ 2 + V ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg U])
  have hb : (U - 1) ^ 2 + V ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (U - 1)])
  have hi : ∀ z ∈ cs.map Computable.initial, MvPolynomial.aeval x (toMvPolynomial z) ≠ 0 := by
    simp only [initials, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      toMvPolynomial_neg, toMvPolynomial_mul, map_neg, map_mul, neg_ne_zero, mul_ne_zero_iff]
    simp [a, b, u, v, x, hv, ha, hb]
  have result := aeval_eq_zero_of_characteristicSet Computable.Standard.basicSet
    (Standard.basicSetSpec Mono.lex) (Standard.basicSetSpec_toList Mono.lex)
    ℝ equations cs conclusion x computed remainder_zero hz hi
  simpa [conclusion, e, p, h, f, g, x] using result

-- For comparison, prove the same polynomial implication directly using `grind`.
private theorem polynomial_implication_grind (U V P Q E F G H : ℝ) (hv : V ≠ 0)
    (hc : V * (P ^ 2 + Q ^ 2 - P) - (U ^ 2 + V ^ 2 - U) * Q = 0)
    (he : V * (E - 1) - (U - 1) * F = 0) (hep : (P - E) * (U - 1) + (Q - F) * V = 0)
    (hf : V * G - U * H = 0) (hfp : U * (P - G) + V * (Q - H) = 0) :
    (E - P) * H - F * (G - P) = 0 := by
  have ha : U ^ 2 + V ^ 2 ≠ 0 := by positivity
  have hb : (U - 1) ^ 2 + V ^ 2 ≠ 0 := by positivity
  grind

/-- **Wallace–Simson theorem**: the perpendicular feet from a point on the
circumcircle of a nondegenerate normalized triangle are collinear.
The feet may coincide, and the side lines include their extensions. -/
theorem simson_normalized (U V : ℝ) (P D E F : Point) (hv : V ≠ 0)
    (hc : OnCommonCircle (0, 0) (1, 0) (U, V) P)
    (hd : IsPerpendicularFoot P (0, 0) (1, 0) D)
    (he : IsPerpendicularFoot P (1, 0) (U, V) E)
    (hf : IsPerpendicularFoot P (0, 0) (U, V) F) :
    Collinear ℝ ({D, E, F} : Set Point) := by
  have hcircle := hc.normalized_equation
  rcases P with ⟨px, py⟩
  rcases D with ⟨dx, dy⟩
  rcases E with ⟨ex, ey⟩
  rcases F with ⟨fx, fy⟩
  simp only [IsPerpendicularFoot, sub_zero, sub_self, mul_zero, mul_one,
    add_zero, sub_eq_zero] at hd
  obtain ⟨rfl, rfl⟩ := hd
  apply collinear_of_det_eq_zero
  simp only [sub_zero]
  apply polynomial_implication U V px py _ _ _ _ hv hcircle
  · simpa [IsPerpendicularFoot, mul_comm] using he.1
  · simpa [IsPerpendicularFoot, mul_comm] using he.2
  · simpa [IsPerpendicularFoot, mul_comm] using hf.1
  · simpa [IsPerpendicularFoot, mul_comm] using hf.2

-- A nonvertex circle point; the feet lie on x + y = 1.
example : Collinear ℝ ({(1, 0), (1/2, 1/2), (0, 1)} : Set Point) := by
  apply simson_normalized 0 1 (1, 1)
  · norm_num
  · refine ⟨(1/2, 1/2), ?_⟩
    norm_num [sqDist]
  all_goals norm_num [IsPerpendicularFoot]

-- A right triangle with u = 0 and the circle point at A: two feet coincide.
example : Collinear ℝ ({(0, 0), (1/2, 1/2), (0, 0)} : Set Point) := by
  apply simson_normalized 0 1 (0, 0)
  · norm_num
  · refine ⟨(1/2, 1/2), ?_⟩
    norm_num [sqDist]
  all_goals norm_num [IsPerpendicularFoot]

-- The circle point at B, again allowing coincident feet.
example : Collinear ℝ ({(1, 0), (1, 0), (0, 0)} : Set Point) := by
  apply simson_normalized 0 1 (1, 0)
  · norm_num
  · refine ⟨(1/2, 1/2), ?_⟩
    norm_num [sqDist]
  all_goals norm_num [IsPerpendicularFoot]

-- The other vertical-side case u = 1, with the circle point at C.
example : Collinear ℝ ({(1, 0), (1, 1), (1, 1)} : Set Point) := by
  apply simson_normalized 1 1 (1, 1)
  · norm_num
  · refine ⟨(1/2, 1/2), ?_⟩
    norm_num [sqDist]
  all_goals norm_num [IsPerpendicularFoot]

end CharacteristicSet.Bridge.Examples.Simson
