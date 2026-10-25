import CharacteristicSet.Computable
import HexMvPoly.Ring

/-! Executable acceptance examples. Run `lake env lean CharacteristicSet/Computable/Examples.lean`.
All inputs and intermediate polynomials use Hex; there is no Mathlib import. -/

open Hex Hex.MvPoly CharacteristicSet.Computable

abbrev P := MvPoly 2 Rat Mono.lex

def x : P := X 0
def y : P := X 1

def samples : List P := [0, C 3, x * x + y, x * y * y + C 1, (y - y) + x]

-- Displays each main variable, degree, and canonical initial term list.
#eval samples.map fun p => (mainVar p, mainDegree p,
  (initial p).termsList.map fun (m, c) => (m.toList, c))

#guard (samples.map mainVar) == [none, none, some 1, some 1, some 0]
#guard (samples.map mainDegree) == [0, 0, 1, 2, 1]
#guard (samples.map initial) == [0, C 1, C 1, x, C 1]
#guard initialOf 0 (x * y * y + C 1) == y * y
#guard initialOf 1 (C 3 : P) == C 3
#guard initialOf 1 (0 : P) == 0

#eval (initialOf 0 (x * y * y + C 1)).termsList.map fun (m, c) => (m.toList, c)
#eval (compareRank (x + C 1) (x + C 2), (x + C 1) == (x + C 2))
#guard compareRank (x + C 1) (x + C 2) == .eq
#guard !((x + C 1) == (x + C 2))
#guard compareRank x y == .lt
#guard compareRank (y * y) y == .gt
#guard compareRank (C 3 : P) x == .lt

abbrev P0 := MvPoly 0 Rat Mono.lex
#guard mainVar (C 3 : P0) == none
#guard mainDegree (C 3 : P0) == 0
#guard initial (C 3 : P0) == C 1
#guard initial (0 : P0) == 0
#eval (mainVar (C 3 : P0), mainDegree (C 3 : P0),
  (initial (C 3 : P0)).termsList.map fun (m, c) => (m.toList, c))

abbrev G := MvPoly 2 Rat Mono.grevlex

def gx : G := X 0
def gy : G := X 1
#guard mainVar (gx * gx + gy) == some 1
#guard mainDegree (gx * gx + gy) == 1
#guard initial (gx * gx + gy) == C 1
#guard initial (gx * gy * gy + C 1) == gx
#eval (mainVar (gx * gx + gy), mainDegree (gx * gx + gy),
  (initial (gx * gx + gy)).termsList.map fun (m, c) => (m.toList, c))


-- Full integer outputs, including the degree-zero convention and degree jumps.
namespace PseudoExamples

abbrev Z := MvPoly 2 Int Mono.lex
def x : Z := X 0
def y : Z := X 1

#guard pseudoOf 1 (y ^ 4) (0 : Z) == ⟨1, y ^ 4, 0⟩
#guard pseudoOf 1 (y ^ 4) (C 3 : Z) == ⟨1, y ^ 4, 0⟩
#guard pseudoOf 1 (y ^ 4) x == ⟨1, y ^ 4, 0⟩
#guard pseudoOf 1 (0 : Z) (y + C 1) == ⟨0, 0, 0⟩
#guard pseudoOf 1 y (y ^ 2 + C 1) == ⟨0, 0, y⟩
#guard pseudoOf 1 (x * y ^ 2 + C 1) (x * y ^ 2 + C 1) == ⟨1, x, 0⟩
#guard pseudoOf 1 (y ^ 4 + C 1) (y + C 1) ==
  ⟨4, y ^ 3 - y ^ 2 + y - C 1, C 2⟩
#guard pseudoOf 1 (y ^ 4) (x * y ^ 2 + C 1) == ⟨2, x * y ^ 2 - C 1, C 1⟩
-- Selected variable is independent of the monomial storage order.
#guard pseudoOf 0 (x ^ 4) (y * x ^ 2 + C 1) == ⟨2, y * x ^ 2 - C 1, C 1⟩
#eval let p := pseudoOf 1 (y ^ 4) (x * y ^ 2 + C 1)
  (p.exponent, p.quotient.termsList.map fun (m, c) => (m.toList, c),
    p.remainder.termsList.map fun (m, c) => (m.toList, c))

abbrev ZG := MvPoly 2 Int Mono.grevlex
def gx : ZG := X 0
def gy : ZG := X 1
#guard pseudoOf 1 (gy ^ 4) (gx * gy ^ 2 + C 1) == ⟨2, gx * gy ^ 2 - C 1, C 1⟩
#guard pseudoOf 0 (gx ^ 4) (gy * gx ^ 2 + C 1) == ⟨2, gy * gx ^ 2 - C 1, C 1⟩
#guard pseudoOf 1 (gy ^ 4 + C 1) (gy + C 1) ==
  ⟨4, gy ^ 3 - gy ^ 2 + gy - C 1, C 2⟩

end PseudoExamples

-- General division distinguishes zero and constants and automatically selects the main variable.
namespace GeneralPseudoExamples

#guard pseudo (y + C 1) (0 : P) == ⟨0, 0, y + C 1⟩
#guard pseudo (0 : P) 0 == ⟨0, 0, 0⟩
#guard pseudo (0 : P) (C 2) == ⟨0, 0, 0⟩
#guard pseudo (0 : P) (y + C 1) == ⟨0, 0, 0⟩
#guard pseudo (y + C 1) (C 2) == ⟨0, C (1 / 2) * y + C (1 / 2), 0⟩
#guard pseudo (y + C 1) (C (-2)) == ⟨0, C (-1 / 2) * y + C (-1 / 2), 0⟩
#guard pseudo (C (2 / 3) * y + C (3 / 5)) (C (3 / 2)) ==
  ⟨0, C (4 / 9) * y + C (2 / 5), 0⟩
#guard pseudo (y ^ 4) (x * y ^ 2 + C 1) == ⟨2, x * y ^ 2 - C 1, C 1⟩
#guard pseudo (y ^ 4 + C 1) (y + C 1) == ⟨4, y ^ 3 - y ^ 2 + y - C 1, C 2⟩
#guard pseudo (x ^ 4 : P) (x ^ 2 + C 1 : P) == ⟨2, x ^ 2 - C 1, C 1⟩
#guard pseudo (gy + C 1) (C 2 : G) == ⟨0, C (1 / 2) * gy + C (1 / 2), 0⟩
#guard pseudo (gy ^ 4) (gx * gy ^ 2 + C 1) == ⟨2, gx * gy ^ 2 - C 1, C 1⟩
#guard pseudo (C 1 : P0) (C 2) == ⟨0, C (1 / 2), 0⟩
#guard pseudo (C 1 : P0) 0 == ⟨0, 0, C 1⟩

end GeneralPseudoExamples
