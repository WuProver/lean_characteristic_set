import CharacteristicSetBench.Benchmarks
import CharacteristicSetBench.PseudoDivision
import CharacteristicSetBench.Reduced
import CharacteristicSetBench.TriangularSet

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
