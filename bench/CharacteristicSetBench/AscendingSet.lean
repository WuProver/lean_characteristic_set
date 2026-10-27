import LeanBench
import CharacteristicSetBench.Input

/-! Standard basic sets at fixed n=10 and eight raw inputs. U(high,s,k,t) has
only coordinate high nonzero: exponent j+1+s, coefficient j%7+1+k, 0≤j<t.
Same-variable inputs descend from U(8,7,7,t) to U(8,0,0,t); only the last survives.
Different-variable inputs descend from U(8,0,7,t) to U(1,0,0,t); all survive,
in reverse order. Prep only constructs raw polynomials, without sorting or queries.

A linear T diagnostic model at fixed dimension and list length is declared before
sampling. The timer includes basicSet (stable sorting, zero removal, rank queries,
prefix updates and reduction filtering), output wrapping, complete ordered output
hashing and framework overhead. The paths return one/eight polynomials; these
measure full API costs, not isolated sorting/filtering, a speedup, or scaling in
input count or dimension. Full ordered input hashing occurs outside timing. -/

namespace CharacteristicSetBench.Ascending
open Hex

abbrev P := MvPoly 10 Int Mono.lex

structure Input where
  polynomials : List P

instance : Hashable Input where
  hash s := hash (s.polynomials.map Poly.mk)

/-- Sparse univariate input with exactly max 1 T positive terms. -/
def univariate (high shift offset t : Nat) : P :=
  MvPoly.ofTerms ((List.range (max 1 t)).map fun j =>
    (Vector.ofFn (fun i : Fin 10 => if i.val == high then j + 1 + shift else 0),
      Int.ofNat (j % 7 + 1 + offset)))

def prep_same (t : Nat) : Input :=
  ⟨((List.range 8).map (fun k => univariate 8 k k t)).reverse⟩

def prep_distinct (t : Nat) : Input :=
  ⟨((List.range 8).map (fun k => univariate (k + 1) 0 k t)).reverse⟩

@[noinline] def same (s : Input) : List (Poly 10 Mono.lex) :=
  (CharacteristicSet.Computable.basicSet s.polynomials).map Poly.mk

setup_benchmark same t => t with prep := prep_same where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["basic"]
}

@[noinline] def distinct (s : Input) : List (Poly 10 Mono.lex) :=
  (CharacteristicSet.Computable.basicSet s.polynomials).map Poly.mk

setup_benchmark distinct t => t with prep := prep_distinct where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["basic"]
}

end CharacteristicSetBench.Ascending
