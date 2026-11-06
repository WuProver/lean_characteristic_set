import CharacteristicSetBench.Benchmarks
import CharacteristicSetBench.PseudoDivision
import CharacteristicSetBench.Reduced
import CharacteristicSetBench.AscendingSet
import CharacteristicSetBench.TriangularSet
import CharacteristicSetBench.CasSmoke
import CharacteristicSetBench.BasicVariants

def main (args : List String) : IO UInt32 :=
  match args with
  | ["basic-variants", "--verify"] => CharacteristicSetBench.BasicVariants.verify
  | ["basic-variants", output] => CharacteristicSetBench.BasicVariants.run output
  | ["cas-smoke", input] => CharacteristicSetBench.CasSmoke.run input
  | _ => LeanBench.Cli.dispatch args
