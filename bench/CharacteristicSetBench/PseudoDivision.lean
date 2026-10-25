import LeanBench
import CharacteristicSetBench.Input

/-! Pseudo-division of sparse integer polynomials in variable 1.
Inputs are prepared outside the timer; hashing consumes the entire output.

`successive` uses y^d + 1 divided by y + 1: d eliminations and a growing
quotient. The d^2 * (log2 d + 1) model accounts for repeated traversal and
ordered-map arithmetic on that quotient, as a diagnostic only.

`degreeJump` uses y^(2k) divided by x*y^k + 1: exactly two eliminations,
with quotient x*y^k - 1 and remainder 1. Repeated-squaring power construction
still depends on k; log2 k + 1 is a diagnostic model, not a constant-time claim.
The parameter is d for successive and k (half the dividend degree) for degreeJump. -/

namespace CharacteristicSetBench.PseudoDivision
open Hex

/-- Consume the elimination count and every coefficient and monomial of both outputs. -/
structure Result where
  exponent : Nat
  quotient : Poly 2 Mono.lex
  remainder : Poly 2 Mono.lex

instance : Hashable Result where
  hash r := hash (r.exponent, hash r.quotient, hash r.remainder)

@[noinline] def run (s : Input 2 Mono.lex) : Result :=
  let r := CharacteristicSet.Computable.pseudoOf s.i s.p.value s.q.value
  ⟨r.exponent, ⟨r.quotient⟩, ⟨r.remainder⟩⟩

def prep_successive (d : Nat) : Input 2 Mono.lex :=
  let y : MvPoly 2 Int Mono.lex := MvPoly.X 1
  ⟨⟨y ^ max 1 d + MvPoly.C 1⟩, ⟨y + MvPoly.C 1⟩, 1⟩

@[noinline] def successive (s : Input 2 Mono.lex) : Result := run s
setup_benchmark successive d => d * d * (Nat.log2 d + 1) with prep := prep_successive where {
  paramSchedule := .custom #[16, 32, 64, 128]
  paramFloor := 16
  paramCeiling := 128
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["pseudo"]
}

def prep_degreeJump (k : Nat) : Input 2 Mono.lex :=
  let k := max 1 k
  let x : MvPoly 2 Int Mono.lex := MvPoly.X 0
  let y : MvPoly 2 Int Mono.lex := MvPoly.X 1
  ⟨⟨y ^ (2 * k)⟩, ⟨x * y ^ k + MvPoly.C 1⟩, 1⟩

@[noinline] def degreeJump (s : Input 2 Mono.lex) : Result := run s
setup_benchmark degreeJump k => Nat.log2 k + 1 with prep := prep_degreeJump where {
  paramSchedule := .custom #[16, 128, 1024, 8192]
  paramFloor := 16
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["pseudo"]
}

end CharacteristicSetBench.PseudoDivision
