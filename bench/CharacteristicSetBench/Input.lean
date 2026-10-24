import CharacteristicSet

namespace CharacteristicSetBench
open Hex

/-- Exhaustive consumption of the comparator result; Ordering has no stock Hashable. -/
instance : Hashable Ordering where
  hash
    | .lt => hash (0 : Nat)
    | .eq => hash (1 : Nat)
    | .gt => hash (2 : Nat)

/-- Bench-local wrapper: hash every exponent and coefficient, never `sizeOf`. -/
structure Poly (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  value : MvPoly n Int cmp

instance {n : Nat} {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : Hashable (Poly n cmp) where
  hash p := hash (p.value.termsList.map fun (m, c) => (m.toList, c))

structure Input (n : Nat) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  p : Poly n cmp
  q : Poly n cmp
  i : Fin n

instance {n : Nat} {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] : Hashable (Input n cmp) where
  hash s := hash (hash s.p, hash s.q, s.i.val)

/-- Coordinate 0 encodes the row; the selected nonzero coordinate selects the layer. -/
def terms (n t k high degree offset : Nat) : List (Mono n × Int) :=
  (List.range t).map fun j =>
    (Vector.ofFn fun i : Fin n =>
      if i.val == 0 then j + 1 else
      if i.val == high then (if j < k then degree else 3) else 0,
     Int.ofNat (j % 7 + 1 + offset))

/-- Construct the two polynomials and selected variable outside the timer. -/
def prepare (n : Nat) (h : 2 ≤ n) (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] (mode path t : Nat) : Input n cmp := Id.run do
  let t := max 1 t -- lean-bench verify also invokes parameter 0.
  let k := if mode == 0 then 1 else if mode == 1 then max 1 (t / 2) else t
  let i : Fin n := ⟨n - 1, by omega⟩
  let p : MvPoly n Int cmp := MvPoly.ofTerms (terms n t k i.val 7 0)
  let qi : Fin n := if path == 1 then ⟨n - 2, by omega⟩ else i
  let qd := if path == 2 then 9 else 7
  let q : MvPoly n Int cmp := MvPoly.ofTerms (terms n t k qi.val qd 1)
  return ⟨⟨p⟩, ⟨q⟩, i⟩

end CharacteristicSetBench
