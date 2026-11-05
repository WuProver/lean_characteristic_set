import CharacteristicSet
import Lean

/-! Runtime input prevents the smoke computation from becoming a closed constant. -/
namespace CharacteristicSetBench.CasSmoke
open Hex Lean

abbrev P := MvPoly 2 Rat Mono.lex

private def polynomial (j : Json) : Except String P := do
  let ts ← j.getArr?
  let terms ← ts.toList.mapM fun t => do
    let powers ← (← t.getObjVal? "powers").getArr?
    if powers.size != 2 then throw "expected two exponents"
    let a ← powers[0]!.getNat?
    let b ← powers[1]!.getNat?
    let some num := (← (← t.getObjVal? "num").getStr?).toInt?
      | throw "invalid numerator"
    let some den := (← (← t.getObjVal? "den").getStr?).toNat?
      | throw "invalid denominator"
    if den == 0 then throw "zero denominator"
    pure ((#v[a, b] : Mono 2), mkRat num den)
  pure (MvPoly.ofTerms terms)

@[noinline] private def multiply (p q : P) : P := p * q

private def encode (r : P) : Json :=
  toJson (r.termsList.map fun (m, c) => Json.mkObj [
    ("powers", toJson m.toList), ("num", toJson (toString c.num)),
    ("den", toJson (toString c.den))])

def run (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let result : Except String (P × P × Nat × Nat) := do
    let j ← Json.parse source
    let p ← polynomial (← j.getObjVal? "lhs")
    let q ← polynomial (← j.getObjVal? "rhs")
    let batch ← (← j.getObjVal? "batch_size").getNat?
    let trials ← (← j.getObjVal? "trials").getNat?
    pure (p, q, batch, trials)
  match result with
  | .error e => throw (IO.userError e)
  | .ok (p, q, batch, trials) =>
    let warmup ← IO.mkRef (multiply p q)
    let mut samples : Array Json := #[]
    for trial in [:trials] do
      let inputs := (Array.range batch).map fun i => q + MvPoly.C ((trial*batch+i+1 : Nat) : Rat)
      let results ← IO.mkRef (#[] : Array P)
      let start ← IO.monoNanosNow
      for operand in inputs do
        let product := multiply p operand
        results.modify (·.push product)
      let stop ← IO.monoNanosNow
      let jsonSeconds := Json.num ⟨(stop-start : Nat), 9⟩
      samples := samples.push (Json.mkObj [("seconds", jsonSeconds),
        ("outputs", toJson ((← results.get).map encode))])
    IO.println s!"CSBENCH_VERSION:{Lean.versionString}"
    IO.println ("CSBENCH_RESULT:" ++ (Json.mkObj [("terms", encode (← warmup.get)),
      ("samples", toJson samples)]).compress)
    return 0
end CharacteristicSetBench.CasSmoke
