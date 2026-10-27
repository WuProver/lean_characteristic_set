import LeanBench
import CharacteristicSetBench.Input

/-! Prefix replacement with n=10 and eight nonzero polynomials of increasing
main variables 1..8. Each has t=max 1 T distinct terms: coordinate 0 is j+1,
the selected high coordinate is 7, and the coefficient is j%7+1+offset.
The new polynomial has high=4 (middle replacement) or 9 (tail append), offset=1.
Complete outputs are the first three or all eight originals followed by p.

The fixed dimension/list length motivates a linear T diagnostic model, fixed
before sampling. Prep stores the raw list and p, without precomputing their
queries. The timer includes takeConcat (zero/main-variable queries), the output
wrapper map, full ordered result hashing and framework overhead. This measures
two API paths with different output lengths, not a pure prefix scan or speedup. -/

namespace CharacteristicSetBench.Triangular
open Hex

abbrev P := MvPoly 10 Int Mono.lex

structure Input where
  polynomials : List P
  polynomial : P

instance : Hashable Input where
  hash s := hash (s.polynomials.map Poly.mk, Poly.mk s.polynomial)

def prep (high t : Nat) : Input :=
  let t := max 1 t
  ⟨(List.range 8).map (fun k => MvPoly.ofTerms (terms 10 t t (k + 1) 7 0)),
    MvPoly.ofTerms (terms 10 t t high 7 1)⟩

def prep_middle (t : Nat) : Input := prep 4 t
def prep_append (t : Nat) : Input := prep 9 t

@[noinline] def middle (s : Input) : List (Poly 10 Mono.lex) :=
  (CharacteristicSet.Computable.takeConcat s.polynomials s.polynomial).map Poly.mk

setup_benchmark middle t => t with prep := prep_middle where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["triangular"]
}

@[noinline] def append (s : Input) : List (Poly 10 Mono.lex) :=
  (CharacteristicSet.Computable.takeConcat s.polynomials s.polynomial).map Poly.mk

setup_benchmark append t => t with prep := prep_append where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["triangular"]
}

end CharacteristicSetBench.Triangular
