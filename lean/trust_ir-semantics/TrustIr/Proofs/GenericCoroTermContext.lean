-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroInvoke

namespace TrustIr.GenericCoro

/-- Terminator closure resolution observes the complete resolvers and its
    fallback. All errors, physical arguments and calling conventions remain. -/
theorem closureTermWithContext_congr (source target : EvalContext) (depth : Nat) (term : Inst)
    (sourceFallback targetFallback : Sem InstrResult)
    (functions : ∀ held function signature,
      functionCall source held function signature = functionCall target held function signature)
    (closures : ∀ cid function captures signature args convention,
      closureCall source cid function captures signature args convention =
        closureCall target cid function captures signature args convention)
    (fallbacks : sourceFallback = targetFallback) :
    closureTermWithContext source depth term sourceFallback =
      closureTermWithContext target depth term targetFallback := by
  cases term <;> simp only [closureTermWithContext, functions, closures, fallbacks]

/-- The actual strategy-directed terminator adds only the target byte model
    to the complete closure/function resolution observations. -/
theorem stepTermWithContext_congr (source target : EvalContext) (depth : Nat) (cfg : CFG)
    (term : Inst) (strategy : PanicStrategy)
    (models : source.byteModel = target.byteModel)
    (functions : ∀ held function signature,
      functionCall source held function signature = functionCall target held function signature)
    (closures : ∀ cid function captures signature args convention,
      closureCall source cid function captures signature args convention =
        closureCall target cid function captures signature args convention) :
    stepTermWithContext source depth cfg term strategy =
      stepTermWithContext target depth cfg term strategy := by
  cases strategy <;> unfold stepTermWithContext <;>
    apply closureTermWithContext_congr source target depth term _ _ functions closures <;>
    rw [models]

end TrustIr.GenericCoro
