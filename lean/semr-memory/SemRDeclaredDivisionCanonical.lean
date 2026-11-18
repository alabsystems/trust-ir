-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemRDeclaredDivisionPacket

namespace SemR.CanonicalDeclaredDivision.Packet
open TrustIr

/-- The canonical executor answers a return predicate on the original decoded
    packet. A typed caller supplies the normalized U64 argument. Even the
    always-true predicate requires a successful execution, so zero is excluded
    by the body's division rather than by a supplied postcondition. -/
theorem original_canonical_return_iff (divisor depth fuel : Nat)
    (range : divisor < 2 ^ 64) (post : List Value → Prop) :
    (∃ returned after,
      Sem.run (evalFunctionInContext (context depth) ⟨0⟩ [.int 64 (divisor : Int)]
        (fuel + 1) .abort) MachineState.empty = .ok (returned, after) ∧ post returned) ↔
      divisor ≠ 0 ∧ post [.int 64 ((1 / divisor : Nat) : Int)] := by
  rcases original_canonical_shape depth with ⟨found, params, returns, abi, entry, const, div⟩
  rw [target_function (context depth) ⟨0⟩ (canonicalFunction depth) divisor fuel
    found params returns abi entry const div range]
  by_cases zero : divisor = 0 <;> simp [zero]

end SemR.CanonicalDeclaredDivision.Packet
