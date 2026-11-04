import CharacteristicSet.Computable
import HexMvPoly.Ring

/-! Zero-decomposition regression examples, executable without Mathlib or the bridge. -/

open Hex Hex.MvPoly CharacteristicSet.Computable
namespace ZeroDecompositionExamples
abbrev P := MvPoly 2 Rat Mono.lex
def x : P := X 0
def y : P := X 1

#guard Standard.zeroDecomposition ([] : List P) == [[]]
#guard Weak.zeroDecomposition ([0, 0] : List P) == [[]]
#guard Standard.zeroDecomposition ([C 3] : List P) == [[C 3]]
#guard Weak.zeroDecomposition ([C 3] : List P) == [[C 3]]
#guard Standard.zeroDecomposition [x * y] == [[x * y], [x], [C 1]]
#guard Weak.zeroDecomposition [x * y] == [[x * y], [x], [C 1]]
#guard Standard.zeroDecomposition [x, y] == [[x, y], [C 1], [C 1]]
#guard Weak.zeroDecomposition [x, y] == [[x, y], [C 1], [C 1]]
#guard Standard.zeroDecomposition [x, y + x] == [[x, y], [C 1], [C 1]]
#guard Weak.zeroDecomposition [x, y + x] == [[x, y + x], [C 1], [C 1]]
#guard Standard.zeroDecomposition [x, x + C 1] == [[C 1]]
#guard Weak.zeroDecomposition [x, x + C 1] == [[C 1]]

abbrev P0 := MvPoly 0 Rat Mono.lex
#guard Standard.zeroDecomposition ([0] : List P0) == [[]]
#guard Weak.zeroDecomposition ([C 2] : List P0) == [[C 2]]

abbrev G := MvPoly 2 Rat Mono.grevlex
#guard Standard.zeroDecomposition ([X 0 * X 1] : List G) == [[X 0 * X 1], [X 0], [C 1]]
#guard Weak.zeroDecomposition ([X 0 * X 1] : List G) == [[X 0 * X 1], [X 0], [C 1]]
end ZeroDecompositionExamples
