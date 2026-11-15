/-
  Production SemR oracle entry point. Keep the complete audit/check dependency
  graph here; the shared I/O implementation also serves the runtime-mutant target.
-/
import SemR
import SemRStorage
import ClosureAxiomAudit
import TensorContraction
import MetadataCheck
import U64AdditionAudit
import SemREntryAxiomAudit
import SemREntryCheck
import SemREntryBodyAxiomAudit
import SemREntryBodyCheck
import SemRSourceBodyCheck
import SemRSourceBodyAxiomAudit

import SemRRuntimeMain

def main (argv : List String) : IO UInt32 := semrEvalMain argv
