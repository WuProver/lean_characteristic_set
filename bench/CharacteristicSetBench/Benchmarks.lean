import LeanBench
import CharacteristicSetBench.Input

/-! Models declared before formal sampling. At fixed n, queries scan O(T) terms.
Initials model scanning plus K tree lookups/insertions; full output hashing adds O(nK).
These are diagnostic reference models, not claimed exact time or asymptotic proofs. -/
namespace CharacteristicSetBench
open Hex

namespace Main

def prep_mainVar (t : Nat) := prepare 8 (by decide) Mono.lex 1 0 t
@[noinline] def mainVar (s : Input 8 Mono.lex) :=
  CharacteristicSet.Computable.mainVar s.p.value
setup_benchmark mainVar t => t with prep := prep_mainVar where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_mainDegree (t : Nat) := prepare 8 (by decide) Mono.lex 1 0 t
@[noinline] def mainDegree (s : Input 8 Mono.lex) :=
  CharacteristicSet.Computable.mainDegree s.p.value
setup_benchmark mainDegree t => t with prep := prep_mainDegree where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_rank (t : Nat) := prepare 8 (by decide) Mono.lex 1 0 t
@[noinline] def rank (s : Input 8 Mono.lex) :=
  CharacteristicSet.Computable.rank s.p.value
setup_benchmark rank t => t with prep := prep_rank where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_initialOfOne (t : Nat) := prepare 8 (by decide) Mono.lex 0 0 t
@[noinline] def initialOfOne (s : Input 8 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initialOf s.i s.p.value⟩ : Poly 8 Mono.lex)
setup_benchmark initialOfOne t => t + 1 * (Nat.log2 t + Nat.log2 (1 + 1) + 1) with prep := prep_initialOfOne where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_initialOfHalf (t : Nat) := prepare 8 (by decide) Mono.lex 1 0 t
@[noinline] def initialOfHalf (s : Input 8 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initialOf s.i s.p.value⟩ : Poly 8 Mono.lex)
setup_benchmark initialOfHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialOfHalf where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_initialOfAll (t : Nat) := prepare 8 (by decide) Mono.lex 2 0 t
@[noinline] def initialOfAll (s : Input 8 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initialOf s.i s.p.value⟩ : Poly 8 Mono.lex)
setup_benchmark initialOfAll t => t + t * (Nat.log2 t + Nat.log2 (t + 1) + 1) with prep := prep_initialOfAll where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_initialOne (t : Nat) := prepare 8 (by decide) Mono.lex 0 0 t
@[noinline] def initialOne (s : Input 8 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initial s.p.value⟩ : Poly 8 Mono.lex)
setup_benchmark initialOne t => t + 1 * (Nat.log2 t + Nat.log2 (1 + 1) + 1) with prep := prep_initialOne where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_initialHalf (t : Nat) := prepare 8 (by decide) Mono.lex 1 0 t
@[noinline] def initialHalf (s : Input 8 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initial s.p.value⟩ : Poly 8 Mono.lex)
setup_benchmark initialHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialHalf where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_initialAll (t : Nat) := prepare 8 (by decide) Mono.lex 2 0 t
@[noinline] def initialAll (s : Input 8 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initial s.p.value⟩ : Poly 8 Mono.lex)
setup_benchmark initialAll t => t + t * (Nat.log2 t + Nat.log2 (t + 1) + 1) with prep := prep_initialAll where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_compareVar (t : Nat) := prepare 8 (by decide) Mono.lex 1 1 t
@[noinline] def compareVar (s : Input 8 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareVar t => t with prep := prep_compareVar where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_compareDegree (t : Nat) := prepare 8 (by decide) Mono.lex 1 2 t
@[noinline] def compareDegree (s : Input 8 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareDegree t => t with prep := prep_compareDegree where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

def prep_compareEqual (t : Nat) := prepare 8 (by decide) Mono.lex 1 0 t
@[noinline] def compareEqual (s : Input 8 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareEqual t => t with prep := prep_compareEqual where {
  paramSchedule := .custom #[128, 512, 2048, 8192]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["main"]
}

end Main

namespace N2

def prep_rank (t : Nat) := prepare 2 (by decide) Mono.lex 1 0 t
@[noinline] def rank (s : Input 2 Mono.lex) :=
  CharacteristicSet.Computable.rank s.p.value
setup_benchmark rank t => t with prep := prep_rank where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_initialOfHalf (t : Nat) := prepare 2 (by decide) Mono.lex 1 0 t
@[noinline] def initialOfHalf (s : Input 2 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initialOf s.i s.p.value⟩ : Poly 2 Mono.lex)
setup_benchmark initialOfHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialOfHalf where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_initialHalf (t : Nat) := prepare 2 (by decide) Mono.lex 1 0 t
@[noinline] def initialHalf (s : Input 2 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initial s.p.value⟩ : Poly 2 Mono.lex)
setup_benchmark initialHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialHalf where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareVar (t : Nat) := prepare 2 (by decide) Mono.lex 1 1 t
@[noinline] def compareVar (s : Input 2 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareVar t => t with prep := prep_compareVar where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareDegree (t : Nat) := prepare 2 (by decide) Mono.lex 1 2 t
@[noinline] def compareDegree (s : Input 2 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareDegree t => t with prep := prep_compareDegree where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareEqual (t : Nat) := prepare 2 (by decide) Mono.lex 1 0 t
@[noinline] def compareEqual (s : Input 2 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareEqual t => t with prep := prep_compareEqual where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

end N2

namespace N32

def prep_rank (t : Nat) := prepare 32 (by decide) Mono.lex 1 0 t
@[noinline] def rank (s : Input 32 Mono.lex) :=
  CharacteristicSet.Computable.rank s.p.value
setup_benchmark rank t => t with prep := prep_rank where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_initialOfHalf (t : Nat) := prepare 32 (by decide) Mono.lex 1 0 t
@[noinline] def initialOfHalf (s : Input 32 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initialOf s.i s.p.value⟩ : Poly 32 Mono.lex)
setup_benchmark initialOfHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialOfHalf where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_initialHalf (t : Nat) := prepare 32 (by decide) Mono.lex 1 0 t
@[noinline] def initialHalf (s : Input 32 Mono.lex) :=
  (⟨CharacteristicSet.Computable.initial s.p.value⟩ : Poly 32 Mono.lex)
setup_benchmark initialHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialHalf where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareVar (t : Nat) := prepare 32 (by decide) Mono.lex 1 1 t
@[noinline] def compareVar (s : Input 32 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareVar t => t with prep := prep_compareVar where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareDegree (t : Nat) := prepare 32 (by decide) Mono.lex 1 2 t
@[noinline] def compareDegree (s : Input 32 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareDegree t => t with prep := prep_compareDegree where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareEqual (t : Nat) := prepare 32 (by decide) Mono.lex 1 0 t
@[noinline] def compareEqual (s : Input 32 Mono.lex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareEqual t => t with prep := prep_compareEqual where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

end N32

namespace Grevlex

def prep_rank (t : Nat) := prepare 8 (by decide) Mono.grevlex 1 0 t
@[noinline] def rank (s : Input 8 Mono.grevlex) :=
  CharacteristicSet.Computable.rank s.p.value
setup_benchmark rank t => t with prep := prep_rank where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_initialOfHalf (t : Nat) := prepare 8 (by decide) Mono.grevlex 1 0 t
@[noinline] def initialOfHalf (s : Input 8 Mono.grevlex) :=
  (⟨CharacteristicSet.Computable.initialOf s.i s.p.value⟩ : Poly 8 Mono.grevlex)
setup_benchmark initialOfHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialOfHalf where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_initialHalf (t : Nat) := prepare 8 (by decide) Mono.grevlex 1 0 t
@[noinline] def initialHalf (s : Input 8 Mono.grevlex) :=
  (⟨CharacteristicSet.Computable.initial s.p.value⟩ : Poly 8 Mono.grevlex)
setup_benchmark initialHalf t => t + (t / 2) * (Nat.log2 t + Nat.log2 ((t / 2) + 1) + 1) with prep := prep_initialHalf where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareVar (t : Nat) := prepare 8 (by decide) Mono.grevlex 1 1 t
@[noinline] def compareVar (s : Input 8 Mono.grevlex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareVar t => t with prep := prep_compareVar where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareDegree (t : Nat) := prepare 8 (by decide) Mono.grevlex 1 2 t
@[noinline] def compareDegree (s : Input 8 Mono.grevlex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareDegree t => t with prep := prep_compareDegree where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

def prep_compareEqual (t : Nat) := prepare 8 (by decide) Mono.grevlex 1 0 t
@[noinline] def compareEqual (s : Input 8 Mono.grevlex) :=
  CharacteristicSet.Computable.compareRank s.p.value s.q.value
setup_benchmark compareEqual t => t with prep := prep_compareEqual where {
  paramSchedule := .custom #[2048]
  paramFloor := 128
  paramCeiling := 8192
  targetInnerNanos := 1000000000
  maxSecondsPerCall := 5.0
  outerTrials := 3
  tags := #["supplement"]
}

end Grevlex

end CharacteristicSetBench
