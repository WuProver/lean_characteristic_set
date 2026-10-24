import CharacteristicSetBench.Benchmarks

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
