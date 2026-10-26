import LeanBench
import CharacteristicSetBench.Input

/-! Ordinary-list reduction checks with eight divisors and n=8 fixed.
`prepare 8 ... Mono.lex 2 2 T` gives T distinct terms, selected variable 7,
and degrees p=7, q=9 in that variable (also for verify's T=0, clamped to 1).
The checked polynomial is p; seven copies of q pass and p itself fails.
Only the failing divisor's position changes: first versus last. These are
short-circuit control cases, not a triangular-set input distribution.

At fixed dimension and list length, scanning terms motivates the linear T
diagnostic model, declared before sampling. Inputs and the actual divisor list
are prepared outside the timer; only the predicate and Bool hashing are timed. -/

namespace CharacteristicSetBench.Reduced
open Hex

abbrev P := MvPoly 8 Int Mono.lex

/-- Keep the raw polynomial and ordered list ready for the timed API call. -/
structure Input where
  polynomial : P
  divisors : List P

instance : Hashable Input where
  hash s := hash (hash (Poly.mk s.polynomial), s.divisors.map (fun p => hash (Poly.mk p)))

def prep (first : Bool) (t : Nat) : Input :=
  let s := prepare 8 (by decide) Mono.lex 2 2 t
  let passing := List.replicate 7 s.q.value
  ⟨s.p.value, if first then s.p.value :: passing else passing ++ [s.p.value]⟩

def prep_firstFailure (t : Nat) : Input := prep true t
def prep_lastFailure (t : Nat) : Input := prep false t

@[noinline] def firstFailure (s : Input) : Bool :=
  CharacteristicSet.Computable.reducedToSet s.polynomial s.divisors

setup_benchmark firstFailure t => t with prep := prep_firstFailure where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["reduced"]
}

@[noinline] def lastFailure (s : Input) : Bool :=
  CharacteristicSet.Computable.reducedToSet s.polynomial s.divisors

setup_benchmark lastFailure t => t with prep := prep_lastFailure where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["reduced"]
}

end CharacteristicSetBench.Reduced
