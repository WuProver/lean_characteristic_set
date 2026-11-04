import CharacteristicSet.Computable
import HexMvPoly.Ring

/-! Executable characteristic-set regression examples, without Mathlib or bridge imports.
Run from `packages/computable`:
`lake env lean CharacteristicSet/Computable/Examples/CharacteristicSet.lean`. -/

open Hex Hex.MvPoly CharacteristicSet.Computable

namespace CharacteristicSetExamples
abbrev P := MvPoly 2 Rat Mono.lex
def x : P := X 0
def y : P := X 1

#guard Standard.characteristicSet ([] : List P) == []
#guard Weak.characteristicSet ([] : List P) == []
#guard Standard.characteristicSet ([0, 0] : List P) == []
#guard Weak.characteristicSet ([0, 0] : List P) == []
#guard Standard.characteristicSet [y, C 3, C 2, x] == [C 3]
#guard Weak.characteristicSet [y, C 3, C 2, x] == [C 3]
#guard Standard.characteristicSet [y, x, x, 0, y] == [x, y]
#guard Weak.characteristicSet [y, x, x, 0, y] == [x, y]
#guard Standard.characteristicSet [x, y + x] == [x, y]
#guard Weak.characteristicSet [x, y + x] == [x, y + x]
#guard Standard.characteristicSet [x, x + C 1, x] == [C 1]
#guard Weak.characteristicSet [x, x + C 1, x] == [C 1]
-- Two continuation steps: x²+1, then x+1, then the first constant remainder -2.
#guard Standard.characteristicSet [x ^ 3 + C 2 * x + C 1, x ^ 2 + C 1] == [C (-2)]
#guard Weak.characteristicSet [x ^ 3 + C 2 * x + C 1, x ^ 2 + C 1] == [C (-2)]
#guard Standard.characteristicSet [x + C 2, x + C 1] == [C (-1)]
#guard Weak.characteristicSet [x + C 1, x + C 2] == [C 1]

abbrev P0 := MvPoly 0 Rat Mono.lex
#guard Standard.characteristicSet ([0, C 3, C 2] : List P0) == [C 3]
#guard Weak.characteristicSet ([0, C 3, C 2] : List P0) == [C 3]
#guard Standard.characteristicSet ([0, 0] : List P0) == []
#guard Weak.characteristicSet ([0, 0] : List P0) == []

abbrev G := MvPoly 2 Rat Mono.grevlex
def gx : G := X 0
def gy : G := X 1
#guard Standard.characteristicSet [gx, gy + gx] == [gx, gy]
#guard Weak.characteristicSet [gx, gy + gx] == [gx, gy + gx]
#guard Standard.characteristicSet [gx ^ 3 + C 2 * gx + C 1, gx ^ 2 + C 1] == [C (-2)]
#guard Weak.characteristicSet [gx ^ 3 + C 2 * gx + C 1, gx ^ 2 + C 1] == [C (-2)]

end CharacteristicSetExamples
