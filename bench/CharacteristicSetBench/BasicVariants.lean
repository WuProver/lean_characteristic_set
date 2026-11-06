import CharacteristicSet.Computable.Basic
import LeanBench.Env
import Lean

/-! Frozen original queries and alternatives to the production Internal direct/fused
traversals. Every fixture is checked before timing. -/
namespace CharacteristicSetBench.BasicVariants

open Hex Lean

private abbrev P (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] := MvPoly n Int cmp

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

@[noinline] private def degreeReuse (p : P n cmp) : Nat :=
  let d := p.degrees
  (Mono.support d).max?.elim 0 (fun i => d[i])

@[noinline] private def degreeTwoPass (p : P n cmp) : Nat :=
  (CharacteristicSet.Computable.mainVar p).elim 0 (fun i => p.degreeOf i)

@[noinline] private def degreeInternal (p : P n cmp) : Nat :=
  CharacteristicSet.Computable.mainDegree p

@[noinline] private def varOriginal (p : P n cmp) : Nat :=
  p.vars.max?.elim 0 (fun i => i.val + 1)

@[noinline] private def varInternal (p : P n cmp) : Nat :=
  (CharacteristicSet.Computable.mainVar p).elim 0 (fun i => i.val + 1)

@[noinline] private def degreeOriginal (p : P n cmp) : Nat :=
  p.vars.max?.elim 0 (fun i => p.degreeOf i)

private def variants : Array (String × (P n cmp → Nat)) := #[
  ("var.original", varOriginal), ("var.internal", varInternal),
  ("degree.original", degreeOriginal), ("degree.reuse", degreeReuse),
  ("degree.two-pass", degreeTwoPass),
  ("degree.internal", degreeInternal)]

/-- Coordinate zero gives unique monomials; all coefficients are nonzero.
The rare cases place the only occurrence of the main variable at opposite
ends of lexicographic term iteration. -/
private def fixture (n count top : Nat) (shape : String) : List (Mono n × Int) :=
  (List.range count).map fun row =>
    (Vector.ofFn fun i : Fin n =>
      if i.val == 0 then row + 1
      else if i.val > top then 0
      else if shape == "dense" then (row * (i.val + 3) + i.val) % 7 + 1
      else if i.val == top then
        if (shape == "rare-first" && row == 0) ||
            (shape == "rare-last" && row + 1 == count) then 3 else 0
      else (row + i.val) % 4,
     Int.ofNat (row % 7 + 1))

private def check (p : P n cmp) (expectedVar expectedDegree : Nat) : IO Unit := do
  for (name, query) in (variants : Array (String × (P n cmp → Nat))) do
    let expected := if name.startsWith "var." then expectedVar else expectedDegree
    let actual := query p
    if actual != expected then
      throw (IO.userError s!"{name}: expected {expected}, got {actual}")

/-- The reference is computed from raw exponents, independently of every query. -/
private def checkTerms (terms : List (Mono n × Int)) (p : P n cmp) : IO Unit := do
  let expectedVar := terms.foldl (fun v (m, _) =>
    (List.finRange n).foldl (fun v i => if m[i] == 0 then v else max v (i.val + 1)) v) 0
  let expectedDegree := terms.foldl (fun d (m, _) =>
    (List.finRange n).foldl (fun d i =>
      if i.val + 1 == expectedVar then max d m[i] else d) d) 0
  check p expectedVar expectedDegree

private def verifyOrder (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : IO Unit := do
  check (0 : P n cmp) 0 0
  check (MvPoly.C 7 : P n cmp) 0 0
  if n > 0 then
    for count in [1, 2, 7, 31] do
      for top in [:n] do
        for shape in ["dense", "rare-first", "rare-last"] do
          let ts := fixture n count top shape
          let p : P n cmp := MvPoly.ofTerms ts
          checkTerms ts p
          -- Exercise changing main variables in the opposite tree order as well.
          let reversed : P n cmp := MvPoly.ofTerms ts.reverse
          checkTerms ts reversed

def verify : IO UInt32 := do
  for n in [0, 1, 2, 8, 32] do
    verifyOrder n Mono.lex
    verifyOrder n Mono.grevlex
  IO.eprintln "Basic variants: all generated fixtures agree with raw-exponent references."
  return 0

/-- A noinline IO boundary and the existing opaque consumer keep each invocation live.
The small scalar hash and loop/consumer overhead are included for every variant. -/
@[noinline] private def batch (query : P n cmp → Nat) (p : P n cmp) (calls : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:calls] do
    LeanBench.blackBox (hash (query p))
  return (← IO.monoNanosNow) - start

private def targetNanos : Nat := 20000000
private def trials : Nat := 7

private def calibrate (query : P n cmp → Nat) (p : P n cmp) : IO Nat := do
  let mut calls := 1
  for _ in [:24] do
    let elapsed ← batch query p calls
    if elapsed ≥ targetNanos then return calls
    calls := calls * 2
  throw (IO.userError "basic variants: failed to calibrate batch")

private def measure (order label shape : String) (p : P n cmp) : IO (Array Json) := do
  let qs : Array (String × (P n cmp → Nat)) := variants
  let mut counts : Array Nat := #[]
  let mut samples : Array (Array Nat) := qs.map fun _ => #[]
  for (_, query) in qs do
    counts := counts.push (← calibrate query p)
  -- Rotate the order across trials rather than always putting the original first.
  for trial in [:trials] do
    for offset in [:qs.size] do
      let i := (trial + offset) % qs.size
      let elapsed ← batch qs[i]!.2 p counts[i]!
      samples := samples.modify i (·.push elapsed)
  let mut rows := #[]
  for i in [:qs.size] do
    let elapsed := samples[i]!
    let perCall := elapsed.map fun ns => ns.toFloat / counts[i]!.toFloat
    let sorted := perCall.qsort (· < ·)
    let median := sorted[sorted.size / 2]!
    rows := rows.push (Json.mkObj [
      ("case", toJson label), ("order", toJson order), ("shape", toJson shape),
      ("variables", toJson n), ("terms", toJson p.termCount),
      ("main_variable", toJson ((CharacteristicSet.Computable.mainVar p).map Fin.val)),
      ("variant", toJson qs[i]!.1), ("calls_per_batch", toJson counts[i]!),
      ("batch_nanoseconds", toJson elapsed), ("nanoseconds_per_call", toJson perCall),
      ("median_ns", toJson median), ("min_ns", toJson sorted[0]!),
      ("max_ns", toJson sorted[sorted.size - 1]!)])
  IO.eprintln s!"Basic variants: {order}/{label} measured"
  return rows

private def measureFixture (n count top : Nat) (shape order : String)
    (cmp : Mono n → Mono n → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    IO (Array Json) := do
  let ts := fixture n count top shape
  let p : P n cmp := MvPoly.ofTerms ts
  if p.termCount != count then throw (IO.userError "fixture lost terms")
  checkTerms ts p
  measure order s!"n{n}-t{count}-v{top}-{shape}" shape p

def run (output : String) : IO UInt32 := do
  let _ ← verify
  let mut rows := #[]
  for n in [2, 8, 32, 128] do
    for count in [128, 2048] do
      for top in ([0, n / 2, n - 1].eraseDups) do
        rows := rows ++ (← measureFixture n count top "dense" "lex" Mono.lex)
  for n in [8, 32] do
    for top in [0, n / 2, n - 1] do
      rows := rows ++ (← measureFixture n 8192 top "dense" "lex" Mono.lex)
      rows := rows ++ (← measureFixture n 2048 top "dense" "grevlex" Mono.grevlex)
  for n in [8, 32, 128] do
    for top in [n / 2, n - 1] do
      for shape in ["rare-first", "rare-last"] do
        rows := rows ++ (← measureFixture n 2048 top shape "lex" Mono.lex)
  for n in [0, 32] do
    rows := rows ++ (← measure "lex" s!"n{n}-zero" "zero" (0 : P n Mono.lex))
    rows := rows ++ (← measure "lex" s!"n{n}-constant" "constant" (MvPoly.C 7 : P n Mono.lex))
  let result := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("lean_version", toJson Lean.versionString),
    ("trials", toJson trials), ("target_batch_ns", toJson targetNanos),
    ("timing", toJson "native query + scalar hash + blackBox; preparation/checks excluded; warm batches; rotated variant order"),
    ("rows", toJson rows)]
  IO.FS.writeFile output (result.pretty ++ "\n")
  IO.println s!"Basic variants: wrote {rows.size} rows to {output}"
  return 0

end CharacteristicSetBench.BasicVariants
