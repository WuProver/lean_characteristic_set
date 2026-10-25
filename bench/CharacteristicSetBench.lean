import CharacteristicSetBench.Benchmarks
import CharacteristicSetBench.PseudoDivision

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
