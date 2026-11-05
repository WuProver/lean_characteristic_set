import CharacteristicSetBench.Benchmarks
import CharacteristicSetBench.PseudoDivision
import CharacteristicSetBench.Reduced
import CharacteristicSetBench.AscendingSet
import CharacteristicSetBench.TriangularSet
import CharacteristicSetBench.CasSmoke

def main (args : List String) : IO UInt32 :=
  match args with
  | ["cas-smoke", input] => CharacteristicSetBench.CasSmoke.run input
  | _ => LeanBench.Cli.dispatch args
