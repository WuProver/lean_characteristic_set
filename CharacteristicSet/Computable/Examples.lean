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
