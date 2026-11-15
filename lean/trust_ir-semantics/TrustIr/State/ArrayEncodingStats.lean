-- Copyright 2026 Andrew Yates | Apache-2.0
import Init

namespace TrustIr.AggregateMemory.ArrayEncodingRuntime

/-- Observational counters shared by logical tooling and the native provider.
    These counters carry no runtime correspondence or layout evidence. -/
structure Stats where
  visits : Nat := 0
  hits : Nat := 0
  deriving Repr

end TrustIr.AggregateMemory.ArrayEncodingRuntime
