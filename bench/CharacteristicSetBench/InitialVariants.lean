import CharacteristicSetBench.Input
import LeanBench.Env
import Lean

/-! Frozen initial definitions, production `csimp` calls, and an unproved single-pass
candidate. Preparation and reference checks are outside the timed batches. -/
namespace CharacteristicSetBench.InitialVariants

open Hex Lean CharacteristicSet.Computable

private abbrev P (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] := MvPoly n Int cmp

variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

-- Spell out the old definitions so `csimp` cannot redirect the baselines.
@[noinline] private def ofOriginal (i : Fin n) (p : P n cmp) : P n cmp :=
  let d := p.degreeOf i
  MvPoly.ofTerms ((p.monomials.filter (fun m => m[i] == d)).map
    (fun m => (m.set i 0, p.coeff m)))

@[noinline] private def ofProduction (i : Fin n) (p : P n cmp) : P n cmp :=
  initialOf i p

-- Experimental only: fixed-degree erasure is injective, so retained keys cannot collide.
-- Directly building MvPoly uses its internal backing-map field. Retain `0 + c`
-- from ofTerms, rather than silently assuming a law about an arbitrary Add instance.
private def insertDistinct (p : P n cmp) (m : Mono n) (c : Int) : P n cmp :=
  let c' := 0 + c
  if hc : c' = 0 then p else
    { termsInternal := p.termsInternal.insert m c'
      nonzeroInternal := by
        intro k
        rw [Std.ExtTreeMap.getElem?_insert]
        split
        · simpa using hc
        · exact p.nonzeroInternal k }

@[noinline] private def ofDistinct (i : Fin n) (p : P n cmp) : P n cmp :=
  let d := p.degreeOf i
  p.foldTerms (fun acc m c =>
    if m[i] == d then insertDistinct acc (m.set i 0) c else acc) 0

-- Experimental only: earlier output trees can be discarded when the degree increases.
@[noinline] private def ofSinglePass (i : Fin n) (p : P n cmp) : P n cmp :=
  (p.foldTerms (fun (state : Nat × P n cmp) m c =>
    if m[i] > state.1 then (m[i], (0 : P n cmp).addMonomial (m.set i 0) c)
    else if m[i] == state.1 then (state.1, state.2.addMonomial (m.set i 0) c)
    else state) (0, 0)).2

@[noinline] private def initialOriginal (p : P n cmp) : P n cmp :=
  if p.termsList.isEmpty then 0 else
    (mainVar p).elim (MvPoly.C 1) (fun i => ofOriginal i p)

-- Freeze the nested main-variable query too, for an end-to-end standard baseline.
@[noinline] private def initialStandard (p : P n cmp) : P n cmp :=
  if p.termsList.isEmpty then 0 else
    p.vars.max?.elim (MvPoly.C 1) (fun i => ofOriginal i p)

@[noinline] private def initialProduction (p : P n cmp) : P n cmp := initial p

@[noinline] private def initialDistinct (p : P n cmp) : P n cmp :=
  if p.termCount == 0 then 0 else
    (mainVar p).elim (MvPoly.C 1) (fun i => ofDistinct i p)

@[noinline] private def initialSinglePass (p : P n cmp) : P n cmp :=
  if p.termCount == 0 then 0 else
    (mainVar p).elim (MvPoly.C 1) (fun i => ofSinglePass i p)

private def variants (i : Option (Fin n)) : Array (String × (P n cmp → P n cmp)) :=
  let initials := #[
    ("initial.standard", initialStandard),
    ("initial.original", initialOriginal), ("initial.two-pass", initialProduction),
    ("initial.distinct", initialDistinct), ("initial.single-pass", initialSinglePass)]
  match i with
  | none => initials
  | some i => #[
      ("of.original", ofOriginal i), ("of.two-pass", ofProduction i),
      ("of.distinct", ofDistinct i), ("of.single-pass", ofSinglePass i)] ++ initials

/-- Unique row coordinate, nonzero coefficients, and controlled selected-variable degrees. -/
private def fixture (n count : Nat) (shape : String) : List (Mono n × Int) :=
  (List.range count).map fun row =>
    (Vector.ofFn fun i : Fin n =>
      if i.val == 0 then row + 1
      else if i.val + 1 == n then
        if shape == "one-first" then (if row == 0 then 7 else 3)
        else if shape == "one-last" then (if row + 1 == count then 7 else 3)
        else if shape == "half" then (if row < count / 2 then 7 else 3)
        else if shape == "rising" then row + 1
        else if shape == "falling" then count - row
        else 7
      else (row + i.val) % 4,
     Int.ofNat (row % 7 + 1))

private def referenceOf (i : Fin n) (ts : List (Mono n × Int)) : P n cmp :=
  let d := ts.foldl (fun d t => max d t.1[i]) 0
  MvPoly.ofTerms (ts.filterMap fun (m, c) =>
    if m[i] == d then some (m.set i 0, c) else none)

private def check (ts : List (Mono n × Int)) (p : P n cmp) (i : Option (Fin n)) : IO Unit := do
  let expectedOf := i.map fun j => referenceOf j ts
  let top := ts.foldl (fun top (m, _) =>
    (List.finRange n).foldl (fun top j =>
      if m[j] == 0 then top else max top (j.val + 1)) top) 0
  let expectedInitial : P n cmp := if ts.isEmpty then 0 else
    if h : top > 0 ∧ top ≤ n then referenceOf ⟨top - 1, by omega⟩ ts else MvPoly.C 1
  for (name, query) in variants i do
    let expected := if name.startsWith "of." then expectedOf.getD 0 else expectedInitial
    if query p != expected then throw (IO.userError s!"{name}: initial reference mismatch")

private def shapes := ["one-first", "one-last", "half", "all", "rising", "falling"]

private def verifyOrder (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : IO Unit := do
  let i := if h : n > 0 then some (⟨n - 1, by omega⟩ : Fin n) else none
  check [] (0 : P n cmp) i
  check [(Mono.zero, 7)] (MvPoly.C 7 : P n cmp) i
  if n ≥ 2 then
    for count in [1, 2, 7, 31] do
      for shape in shapes do
        let ts := fixture n count shape
        let p : P n cmp := MvPoly.ofTerms ts
        -- Check all selected coordinates, including degree zero and non-main variables.
        for j in List.finRange n do
          check ts p (some j)
        check ts (MvPoly.ofTerms ts.reverse : P n cmp) i

def verify : IO UInt32 := do
  for n in [0, 1, 2, 8, 32] do
    verifyOrder n Mono.lex
    verifyOrder n Mono.grevlex
  IO.eprintln "Initial variants: all generated fixtures agree with raw-term references."
  return 0

-- Hash every output exponent and coefficient; include the same consumption cost in all variants.
@[noinline] private def batch (query : P n cmp → P n cmp) (p : P n cmp) (calls : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:calls] do
    LeanBench.blackBox (hash (⟨query p⟩ : Poly n cmp))
  return (← IO.monoNanosNow) - start

private def targetNanos : Nat := 20000000
private def trials : Nat := 7

private def calibrate (query : P n cmp → P n cmp) (p : P n cmp) : IO Nat := do
  let mut calls := 1
  for _ in [:24] do
    if (← batch query p calls) ≥ targetNanos then return calls
    calls := calls * 2
  throw (IO.userError "initial variants: failed to calibrate batch")

private def measure (order label shape : String) (p : P n cmp) (i : Option (Fin n)) :
    IO (Array Json) := do
  let qs := variants i
  let mut counts := #[]
  let mut samples : Array (Array Nat) := qs.map fun _ => #[]
  for (_, query) in qs do counts := counts.push (← calibrate query p)
  for trial in [:trials] do
    for offset in [:qs.size] do
      let j := (trial + offset) % qs.size
      let elapsed ← batch qs[j]!.2 p counts[j]!
      samples := samples.modify j (·.push elapsed)
  let mut rows := #[]
  for j in [:qs.size] do
    let perCall := samples[j]!.map fun ns => ns.toFloat / counts[j]!.toFloat
    let sorted := perCall.qsort (· < ·)
    rows := rows.push (Json.mkObj [
      ("case", toJson label), ("order", toJson order), ("shape", toJson shape),
      ("variables", toJson n), ("terms", toJson p.termCount),
      ("selected_variable", toJson (i.map Fin.val)),
      ("output_terms", toJson (qs[j]!.2 p).termCount),
      ("variant", toJson qs[j]!.1), ("calls_per_batch", toJson counts[j]!),
      ("batch_nanoseconds", toJson samples[j]!), ("nanoseconds_per_call", toJson perCall),
      ("median_ns", toJson sorted[sorted.size / 2]!),
      ("min_ns", toJson sorted[0]!), ("max_ns", toJson sorted[sorted.size - 1]!)])
  IO.eprintln s!"Initial variants: {order}/{label} measured"
  return rows

private def measureFixture (n count : Nat) (hn : 2 ≤ n) (shape order : String)
    (cmp : Mono n → Mono n → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    IO (Array Json) := do
  let ts := fixture n count shape
  let p : P n cmp := MvPoly.ofTerms ts
  if p.termCount != count then throw (IO.userError "fixture lost terms")
  let i : Fin n := ⟨n - 1, by omega⟩
  check ts p (some i)
  measure order s!"n{n}-t{count}-{shape}" shape p (some i)

def run (output : String) : IO UInt32 := do
  let _ ← verify
  let mut rows := #[]
  for hn : n in [2, 8, 32] do
    have hn : 2 ≤ n := by simp at hn; omega
    for count in [128, 2048] do
      for shape in shapes do
        rows := rows ++ (← measureFixture n count hn shape "lex" Mono.lex)
  for shape in shapes do
    rows := rows ++ (← measureFixture 8 2048 (by decide) shape "grevlex" Mono.grevlex)
  for n in [0, 8] do
    rows := rows ++ (← measure "lex" s!"n{n}-zero" "zero" (0 : P n Mono.lex) none)
    rows := rows ++ (← measure "lex" s!"n{n}-constant" "constant" (MvPoly.C 7 : P n Mono.lex) none)
  IO.FS.writeFile output ((Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("lean_version", toJson Lean.versionString),
    ("trials", toJson trials), ("target_batch_ns", toJson targetNanos),
    ("timing", toJson "native query + full output hash + blackBox; preparation/checks excluded; warm batches; rotated variant order"),
    ("rows", toJson rows)]).pretty ++ "\n")
  IO.println s!"Initial variants: wrote {rows.size} rows to {output}"
  return 0

end CharacteristicSetBench.InitialVariants
