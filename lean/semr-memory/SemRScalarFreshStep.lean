-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemRScalarStep
import TrustIr.Proofs.SSAFreshFrames

namespace SemR.CanonicalScalarStep

open TrustIr in
/-- Use the canonical high-water invariant, whose initial-state and execution
preservation laws already belong to SSAFreshFrames/SSAFreshStep. This theorem
adds no replacement freshness predicate or assumed translation premise. -/
theorem division_step_fresh_registers_iff (m : SemR.Module) (source : SemR.Core)
    (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (target : MachineState)
    (left right destination dividend divisor : Nat)
    (atNode : SemR.nth? source.block.body source.pc =
      some (divisionNode left right destination))
    (leftLookup : SemR.lookupEnv source.env left = some (.int .u64 dividend))
    (rightLookup : SemR.lookupEnv source.env right = some (.int .u64 divisor))
    (related : RegistersAgree source target)
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩)
      [⟨destination⟩] 1 = .ok [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64)
    (fresh : SSAFreshFrames.FreshState target) :
    (∃ sourceNext targetNext,
      SemR.stepCore m source = .cont sourceNext ∧
      Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy
        (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩, [⟨destination⟩])) target =
          .ok (.yield (), targetNext) ∧ RegistersAgree sourceNext targetNext) ↔
      divisor ≠ 0 := by
  exact division_step_registers_iff m source recurse ctx depth strategy target
    left right destination dividend divisor atNode leftLookup rightLookup related
    declarations leftRange rightRange (fresh ⟨target.nextValueId⟩ (Nat.le_refl _))

end SemR.CanonicalScalarStep
