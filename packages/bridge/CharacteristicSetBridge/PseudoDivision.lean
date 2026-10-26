module

public import CharacteristicSet.Computable.PseudoDivision
public import CharacteristicSetBridge.Initial
public import CharacteristicSetTheory.PseudoDivision

/-! Exact correspondence and sufficient internal bound for Hex pseudo-division. -/

public section

namespace CharacteristicSet.Bridge

open Hex HexMvPolyTheory MvPolynomial
open scoped HexMvPolyTheory

section CommRing

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [CommRing R] [DecidableEq R]
  [NoZeroDivisors R]

/-- Interpret all three fields without changing the elimination count. -/
noncomputable def pseudoResultToMvPolynomial (p : Computable.PseudoResult (MvPoly n R cmp)) :
    MvPolynomial.PseudoResult (MvPolynomial (Fin n) R) :=
  ⟨p.exponent, toMvPolynomial p.quotient, toMvPolynomial p.remainder⟩

omit [DecidableEq R] in
/-- The cancellation bound used by the reference recursive algorithm. -/
private theorem cancellation_degree_lt (i : Fin n) (f r : MvPolynomial (Fin n) R)
    (h : f.degreeOf i ≠ 0) (hn : ¬ r.degreeOf i < f.degreeOf i) :
    (f.initialOf i * r -
      (r.initialOf i * X i ^ (r.degreeOf i - f.degreeOf i)) * f).degreeOf i <
      r.degreeOf i := by
  let I := f.initialOf i
  let term := r.initialOf i * X i ^ (r.degreeOf i - f.degreeOf i)
  change (I * r - term * f).degreeOf i < r.degreeOf i
  suffices (I * r - term * f).degreeOf i ≤ r.degreeOf i - 1 by
    exact (Nat.le_sub_one_iff_lt (lt_of_lt_of_le
      (Nat.ne_zero_iff_zero_lt.mp h) (Nat.not_lt.mp hn))).mp this
  have Id : I.degreeOf i = 0 := by rw [degreeOf_initialOf_self]
  have hmul : (I * r).degreeOf i - 1 ≤ r.degreeOf i - 1 := by
    apply Nat.sub_le_sub_right
    rw [← zero_add (r.degreeOf i), ← Id]
    exact degreeOf_mul_le ..
  refine le_trans ?_ hmul
  apply degreeOf_sub_lt_of_initialOf_eq
  repeat1' rw [mul_assoc, mul_comm _ f, ← mul_assoc]
  · rw [initialOf_mul_X_self_pow, initialOf_mul_eq, initialOf_mul_eq]
    rw [initialOf_initialOf_self, initialOf_initialOf_self, mul_comm]
  have f_ne : f ≠ 0 := ne_zero_of_degreeOf_ne_zero h
  have I_ne : I ≠ 0 := initialOf_ne_zero i f_ne
  have r_ne : r ≠ 0 := by
    contrapose! hn
    rw [hn, degreeOf_zero]
    exact Nat.zero_lt_of_ne_zero h
  have Ir_ne : r.initialOf i ≠ 0 := initialOf_ne_zero i r_ne
  rw [degreeOf_mul_X_self_pow_eq_add_of_ne_zero _ _ (mul_ne_zero_iff.mpr ⟨Ir_ne, f_ne⟩)]
  rw [degreeOf_mul_eq I_ne r_ne, degreeOf_mul_eq Ir_ne f_ne]
  simpa [I] using (Nat.add_sub_of_le <| Nat.le_of_not_lt hn).symm

/-- Every actual Hex elimination strictly decreases the selected degree. -/
theorem pseudoOf_step_degree_lt (i : Fin n) (f r : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) (hn : ¬ r.degreeOf i < f.degreeOf i) :
    (Computable.initialOf i f * r -
      (Computable.initialOf i r * MvPoly.X i ^ (r.degreeOf i - f.degreeOf i)) * f).degreeOf i <
      r.degreeOf i := by
  simpa only [degreeOf_toMvPolynomial, toMvPolynomial_sub, toMvPolynomial_mul,
    initialOf_toMvPolynomial, toMvPolynomial_pow, toMvPolynomial_X] using
    cancellation_degree_lt i (toMvPolynomial f) (toMvPolynomial r)
      (by simpa using h) (by simpa using hn)

/-- Any bound larger than the current remainder degree gives the exact reference
result. The zero-fuel branch is unreachable under this hypothesis. -/
theorem pseudoOf_go_toMvPolynomial (i : Fin n) (f : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) (fuel s : Nat) (q r : MvPoly n R cmp)
    (enough : r.degreeOf i < fuel) :
    pseudoResultToMvPolynomial (Computable.pseudoOf.go i f fuel s q r) =
      MvPolynomial.pseudoOf.go i (toMvPolynomial f) s (toMvPolynomial q)
        (toMvPolynomial r) (by simpa using h) := by
  induction fuel generalizing s q r with
  | zero => omega
  | succ fuel ih =>
    rw [Computable.pseudoOf.go, MvPolynomial.pseudoOf.go]
    by_cases hn : r.degreeOf i < f.degreeOf i
    · simp only [← degreeOf_toMvPolynomial, hn, ↓reduceIte, pseudoResultToMvPolynomial]
    · simp only [← degreeOf_toMvPolynomial, hn, ↓reduceIte]
      have descent := pseudoOf_step_degree_lt i f r h hn
      have next := ih (s + 1) (Computable.initialOf i f * q +
        Computable.initialOf i r * MvPoly.X i ^ (r.degreeOf i - f.degreeOf i))
        (Computable.initialOf i f * r -
        (Computable.initialOf i r * MvPoly.X i ^ (r.degreeOf i - f.degreeOf i)) * f)
        (by omega)
      simpa only [toMvPolynomial_add, toMvPolynomial_mul, toMvPolynomial_sub,
        initialOf_toMvPolynomial, toMvPolynomial_pow, toMvPolynomial_X,
        degreeOf_toMvPolynomial] using next

/-- Exact equality of exponent, quotient and remainder with the theory algorithm. -/
theorem pseudoOf_toMvPolynomial (i : Fin n) (g f : MvPoly n R cmp) :
    pseudoResultToMvPolynomial (Computable.pseudoOf i g f) =
      (toMvPolynomial g).pseudoOf i (toMvPolynomial f) := by
  unfold Computable.pseudoOf MvPolynomial.pseudoOf
  by_cases h : f.degreeOf i = 0
  · simp only [← degreeOf_toMvPolynomial, h, ↓reduceIte, ↓reduceDIte,
      pseudoResultToMvPolynomial, toMvPolynomial_zero]
  · simp only [← degreeOf_toMvPolynomial, h, ↓reduceIte, ↓reduceDIte]
    simpa using pseudoOf_go_toMvPolynomial i f h (g.degreeOf i + 1) 0 0 g
      (Nat.lt_succ_self _)

/-- The actual bounded Hex loop reaches the stopping condition whenever its
bound exceeds the starting degree; it cannot silently return a truncated state. -/
theorem pseudoOf_go_stops (i : Fin n) (f : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) (fuel s : Nat) (q r : MvPoly n R cmp)
    (enough : r.degreeOf i < fuel) :
    (Computable.pseudoOf.go i f fuel s q r).remainder.degreeOf i < f.degreeOf i := by
  have exactResult := congrArg MvPolynomial.PseudoResult.remainder
    (pseudoOf_go_toMvPolynomial i f h fuel s q r enough)
  have bound := MvPolynomial.degreeOf_pseudoOfGo_remainder_lt_of_degreeOf_ne_zero
    (i := i) (f := toMvPolynomial f) (by simpa using h) s
    (toMvPolynomial q) (toMvPolynomial r)
  rw [← exactResult] at bound
  simpa only [pseudoResultToMvPolynomial, ← degreeOf_toMvPolynomial] using bound

/-- The computed exponent is the actual exponent of the theory algorithm. -/
theorem pseudoOf_exponent (i : Fin n) (g f : MvPoly n R cmp) :
    (Computable.pseudoOf i g f).exponent =
      ((toMvPolynomial g).pseudoOf i (toMvPolynomial f)).exponent :=
  congrArg MvPolynomial.PseudoResult.exponent (pseudoOf_toMvPolynomial i g f)

/-- Exact interpretation of the computed quotient. -/
theorem pseudoOf_quotient (i : Fin n) (g f : MvPoly n R cmp) :
    toMvPolynomial (Computable.pseudoOf i g f).quotient =
      ((toMvPolynomial g).pseudoOf i (toMvPolynomial f)).quotient :=
  congrArg MvPolynomial.PseudoResult.quotient (pseudoOf_toMvPolynomial i g f)

/-- Exact interpretation of the computed remainder. -/
theorem pseudoOf_remainder (i : Fin n) (g f : MvPoly n R cmp) :
    toMvPolynomial (Computable.pseudoOf i g f).remainder =
      ((toMvPolynomial g).pseudoOf i (toMvPolynomial f)).remainder :=
  congrArg MvPolynomial.PseudoResult.remainder (pseudoOf_toMvPolynomial i g f)

/-- Reconstruction holds as an equality of Hex polynomials. -/
theorem pseudoOf_equation (i : Fin n) (g f : MvPoly n R cmp) :
    Computable.initialOf i f ^ (Computable.pseudoOf i g f).exponent * g =
      (Computable.pseudoOf i g f).quotient * f + (Computable.pseudoOf i g f).remainder := by
  apply toMvPolynomial_injective
  simpa only [toMvPolynomial_mul, toMvPolynomial_pow, initialOf_toMvPolynomial,
    toMvPolynomial_add, pseudoOf_exponent, pseudoOf_quotient, pseudoOf_remainder] using
    MvPolynomial.pseudoOf_equation i (toMvPolynomial g) (toMvPolynomial f)

/-- Positive-degree divisors yield a remainder of strictly smaller degree. -/
theorem pseudoOf_remainder_degree_lt (i : Fin n) (g f : MvPoly n R cmp)
    (h : f.degreeOf i ≠ 0) :
    (Computable.pseudoOf i g f).remainder.degreeOf i < f.degreeOf i := by
  rw [Computable.pseudoOf, ite_eq_right h]
  exact pseudoOf_go_stops i f h (g.degreeOf i + 1) 0 0 g (Nat.lt_succ_self _)

end CommRing

section Field

variable {n : Nat} {R : Type*} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Field R] [DecidableEq R]

private theorem pseudo_termsList_isEmpty_iff (p : MvPoly n R cmp) :
    p.termsList.isEmpty = true ↔ toMvPolynomial p = 0 := by
  rw [List.isEmpty_iff]
  constructor
  · intro h
    have hp : p = 0 := MvPoly.termsList_inj h
    simp [hp]
  · intro h
    have hp : p = 0 := toMvPolynomial_injective (by simpa using h)
    subst p
    rfl

/-- General pseudo-division agrees exactly with the theory, including constants. -/
theorem pseudo_toMvPolynomial (g f : MvPoly n R cmp) :
    pseudoResultToMvPolynomial (Computable.pseudo g f) =
      (toMvPolynomial g).pseudo (toMvPolynomial f) := by
  unfold Computable.pseudo MvPolynomial.pseudo
  simp only [pseudo_termsList_isEmpty_iff]
  split_ifs with h
  · simp [pseudoResultToMvPolynomial]
  · rw [← mainVar_toMvPolynomial]
    cases Computable.mainVar f with
    | none =>
      simp only [pseudoResultToMvPolynomial, toMvPolynomial_mul, toMvPolynomial_C,
        toMvPolynomial_zero, ← MvPolynomial.smul_eq_C_mul]
      congr 2
      simpa using (coeff_toMvPolynomial (Mono.zero : Mono n) f).symm
    | some i => exact pseudoOf_toMvPolynomial i g f

/-- The exponent counts exactly the eliminations performed by general pseudo-division. -/
theorem pseudo_exponent (g f : MvPoly n R cmp) :
    (Computable.pseudo g f).exponent =
      ((toMvPolynomial g).pseudo (toMvPolynomial f)).exponent :=
  congrArg MvPolynomial.PseudoResult.exponent (pseudo_toMvPolynomial g f)

/-- Exact interpretation of the general pseudo-quotient. -/
theorem pseudo_quotient (g f : MvPoly n R cmp) :
    toMvPolynomial (Computable.pseudo g f).quotient =
      ((toMvPolynomial g).pseudo (toMvPolynomial f)).quotient :=
  congrArg MvPolynomial.PseudoResult.quotient (pseudo_toMvPolynomial g f)

/-- Exact interpretation of the general pseudo-remainder. -/
theorem pseudo_remainder (g f : MvPoly n R cmp) :
    toMvPolynomial (Computable.pseudo g f).remainder =
      ((toMvPolynomial g).pseudo (toMvPolynomial f)).remainder :=
  congrArg MvPolynomial.PseudoResult.remainder (pseudo_toMvPolynomial g f)

/-- General pseudo-division reconstructs the dividend as an equality in Hex. -/
theorem pseudo_equation (g f : MvPoly n R cmp) :
    Computable.initial f ^ (Computable.pseudo g f).exponent * g =
      (Computable.pseudo g f).quotient * f + (Computable.pseudo g f).remainder := by
  apply toMvPolynomial_injective
  simpa only [toMvPolynomial_mul, toMvPolynomial_pow, initial_toMvPolynomial,
    toMvPolynomial_add, pseudo_exponent, pseudo_quotient, pseudo_remainder] using
    MvPolynomial.pseudo_equation (toMvPolynomial g) (toMvPolynomial f)

/-- For a nonzero divisor, the interpreted output satisfies the theory's remainder relation. -/
theorem pseudo_remainder_isRemainder (g f : MvPoly n R cmp) (h : f ≠ 0) :
    (toMvPolynomial (Computable.pseudo g f).remainder).IsRemainder
      (toMvPolynomial g) (toMvPolynomial f) := by
  rw [pseudo_remainder]
  apply MvPolynomial.pseudo_remainder_isRemainder
  intro hf
  apply h
  exact toMvPolynomial_injective (by simpa using hf)

/-- Zero divisors preserve the dividend, with zero exponent and quotient. -/
theorem pseudo_zero (g : MvPoly n R cmp) :
    Computable.pseudo g 0 = ⟨0, 0, g⟩ := rfl

/-- Nonzero constants perform ordinary coefficient division. -/
theorem pseudo_C (g : MvPoly n R cmp) (c : R) (h : c ≠ 0) :
    Computable.pseudo g (MvPoly.C c) = ⟨0, MvPoly.C c⁻¹ * g, 0⟩ := by
  have hv : Computable.mainVar (MvPoly.C c : MvPoly n R cmp) = none := by
    simpa only [toMvPolynomial_C, vars_C, Finset.max_empty, WithBot.none_eq_bot] using
      mainVar_toMvPolynomial (MvPoly.C c : MvPoly n R cmp)
  unfold Computable.pseudo
  simp only [pseudo_termsList_isEmpty_iff, toMvPolynomial_C, C_ne_zero.mpr h,
    ↓reduceIte, hv, MvPoly.coeff_C, ↓reduceIte]

/-- A divisor with a main variable selects precisely the existing `pseudoOf` result. -/
theorem pseudo_of_mainVar (g f : MvPoly n R cmp) (i : Fin n)
    (h : Computable.mainVar f = some i) :
    Computable.pseudo g f = Computable.pseudoOf i g f := by
  have hn : toMvPolynomial f ≠ 0 := by
    intro hf
    have hv := mainVar_toMvPolynomial f
    rw [h, hf] at hv
    simp at hv
  unfold Computable.pseudo
  simp only [pseudo_termsList_isEmpty_iff, hn, ↓reduceIte, h]

/-- Exact right-to-left semantics for every ordered Hex list, without triangularity. -/
theorem setPseudoRem_toMvPolynomial (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) :
    toMvPolynomial (Computable.setPseudoRem g ps) =
      (ps.map toMvPolynomial).foldr
        (fun f r => (MvPolynomial.pseudo r f).remainder) (toMvPolynomial g) := by
  induction ps with
  | nil => rfl
  | cons f ps ih =>
    simp only [Computable.setPseudoRem_cons, List.map_cons, List.foldr_cons]
    rw [pseudo_remainder, ih]

/-- A list representing a theory triangular set computes its remainder-only algorithm. -/
theorem setPseudoRem_eq_setPseudoRem (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    toMvPolynomial (Computable.setPseudoRem g ps) = (toMvPolynomial g).setPseudoRem S := by
  rw [setPseudoRem_toMvPolynomial, hps]
  rfl

/-- The actual Hex output also agrees with the full theory certificate algorithm. -/
theorem setPseudoRem_eq_setPseudo_remainder (g : MvPoly n R cmp)
    (ps : List (MvPoly n R cmp)) (S : TriangularSet (Fin n) R)
    (hps : ps.map toMvPolynomial = S.toList) :
    toMvPolynomial (Computable.setPseudoRem g ps) =
      ((toMvPolynomial g).setPseudo S).remainder := by
  rw [setPseudoRem_eq_setPseudoRem g ps S hps, MvPolynomial.setPseudo_remainder_eq_setPseudoRem]

/-- Reduction to the whole set requires the ordered list to represent a triangular set. -/
theorem setPseudoRem_reducedToSet (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    (toMvPolynomial (Computable.setPseudoRem g ps)).reducedToSet S := by
  rw [setPseudoRem_eq_setPseudo_remainder g ps S hps]
  exact MvPolynomial.setPseudo_remainder_reducedToSet (toMvPolynomial g) S

/-- The computed remainder satisfies the theory relation for a represented triangular set. -/
theorem setPseudoRem_isSetRemainder (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp))
    (S : TriangularSet (Fin n) R) (hps : ps.map toMvPolynomial = S.toList) :
    (toMvPolynomial (Computable.setPseudoRem g ps)).IsSetRemainder (toMvPolynomial g) S := by
  rw [setPseudoRem_eq_setPseudo_remainder g ps S hps]
  exact MvPolynomial.setPseudo_remainder_isSetRemainder (toMvPolynomial g) S

end Field

end CharacteristicSet.Bridge
