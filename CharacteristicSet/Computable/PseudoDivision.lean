module

public import CharacteristicSet.Computable.Initial
public import HexMvPoly.Operations

/-! Executable specified-variable and general pseudo-division on sparse Hex polynomials. -/

@[expose] public section

namespace CharacteristicSet.Computable

universe u

/-- Actual elimination count, quotient, and remainder of pseudo-division. -/
structure PseudoResult (α : Type u) where
  /-- Number of elimination steps (one in `pseudoOf`'s degree-zero divisor branch). -/
  exponent : Nat
  /-- Accumulated pseudo-quotient. -/
  quotient : α
  /-- Final pseudo-remainder. -/
  remainder : α
  deriving BEq

open Hex

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Zero R] [One R] [Add R] [Mul R] [Neg R] [BEq R] [LawfulBEq R]

/-- Structural implementation of the elimination loop. The public entry point
derives sufficient fuel from the dividend degree; fuel is never the output exponent.
For a positive-degree divisor the bridge proves strict descent and no truncation. -/
def pseudoOf.go (i : Fin n) (f : MvPoly n R cmp) :
    Nat → Nat → MvPoly n R cmp → MvPoly n R cmp → PseudoResult (MvPoly n R cmp)
  | 0, s, q, r => ⟨s, q, r⟩
  | fuel + 1, s, q, r =>
      if r.degreeOf i < f.degreeOf i then ⟨s, q, r⟩ else
        let I := initialOf i f
        let term := initialOf i r * MvPoly.X i ^ (r.degreeOf i - f.degreeOf i)
        go i f fuel (s + 1) (I * q + term) (I * r - term * f)

/-- Pseudo-divide `g` by `f` in variable `i`, counting only actual eliminations.
A divisor of degree zero (including zero) returns `(1, g, 0)`, as in the theory.
All computation stays in the Hex representation. -/
def pseudoOf (i : Fin n) (g f : MvPoly n R cmp) : PseudoResult (MvPoly n R cmp) :=
  if f.degreeOf i = 0 then ⟨1, g, 0⟩
  else pseudoOf.go i f (g.degreeOf i + 1) 0 0 g

/-- Pseudo-divide using the divisor's greatest occurring variable.
Zero returns `(0, 0, g)`; a nonzero constant returns ordinary division
`(0, C c⁻¹ * g, 0)`. Only the native coefficient inverse interface is needed. -/
def pseudo [Inv R] (g f : MvPoly n R cmp) : PseudoResult (MvPoly n R cmp) :=
  if f.termsList.isEmpty then ⟨0, 0, g⟩
  else match mainVar f with
    | none => ⟨0, MvPoly.C (f.coeff Mono.zero)⁻¹ * g, 0⟩
    | some i => pseudoOf i g f

/-- Successively pseudo-divide by an ordered list, from right to left.
An empty list preserves `g`; zero and constant divisors retain `pseudo`'s semantics.
No triangularity, sorting, or filtering is required for this computation. -/
def setPseudoRem [Inv R] (g : MvPoly n R cmp) (ps : List (MvPoly n R cmp)) :
    MvPoly n R cmp :=
  ps.foldr (fun f r => (pseudo r f).remainder) g

@[simp] theorem setPseudoRem_nil [Inv R] (g : MvPoly n R cmp) :
    setPseudoRem g [] = g := rfl

/-- The head divisor acts after the entire tail. -/
@[simp] theorem setPseudoRem_cons [Inv R] (g f : MvPoly n R cmp)
    (ps : List (MvPoly n R cmp)) :
    setPseudoRem g (f :: ps) = (pseudo (setPseudoRem g ps) f).remainder := rfl

end CharacteristicSet.Computable
