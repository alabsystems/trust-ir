/-
  Runtime-mutant entry point. The same I/O implementation as production runs
  intentional semantic mutants without importing the proofs that reject them.
  Named kernel-negative tests build those proofs independently.
-/
import SemRRuntimeMain

def main (argv : List String) : IO UInt32 := semrEvalMain argv
