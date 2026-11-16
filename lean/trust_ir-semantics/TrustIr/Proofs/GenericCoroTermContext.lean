-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroInvoke

namespace TrustIr.GenericCoro

private theorem ignoreMemoryExcept_congr {α β : Type} (source target : Except SemError α)
    (observation : source.map (fun _ => ()) = target.map (fun _ => ())) (next : Sem β) :
    (do let _ ← Sem.fromMemoryExcept source; next) =
      (do let _ ← Sem.fromMemoryExcept target; next) := by
  cases source <;> cases target <;> cases observation <;> rfl

/-- Terminator closure resolution observes the complete resolvers and its
    fallback. Nominal calls additionally observe only their source callee
    operand, call contract, and body-resolution success/error; the resolved
    body is executed separately and is not required to be identical.
    All errors, physical arguments and calling conventions remain. -/
theorem closureTermWithContext_congr (source target : EvalContext) (depth : Nat) (term : Inst)
    (sourceFallback targetFallback : Sem InstrResult)
    (functions : ∀ held function signature convention,
      functionCallWithConvention source held function signature convention =
        functionCallWithConvention target held function signature convention)
    (closures : ∀ cid function captures signature args convention,
      closureCall source cid function captures signature args convention =
        closureCall target cid function captures signature args convention)
    (calleeTypes : ∀ operand ∈ operandIds term, ∀ value,
      checkFunctionItemCalleeType source operand value = checkFunctionItemCalleeType target operand value)
    (items : ∀ function signature convention,
      functionItemCall source function signature convention = functionItemCall target function signature convention)
    (bodies : ∀ function,
      (resolveFunctionItemBody source function).map (fun _ => ()) =
        (resolveFunctionItemBody target function).map (fun _ => ()))
    (fallbacks : sourceFallback = targetFallback) :
    closureTermWithContext source depth term sourceFallback =
      closureTermWithContext target depth term targetFallback := by
  have bodyChecks (function : FuncId) (next : Sem InstrResult) :
      (do let _ ← Sem.fromMemoryExcept (resolveFunctionItemBody source function); next) =
        (do let _ ← Sem.fromMemoryExcept (resolveFunctionItemBody target function); next) :=
    ignoreMemoryExcept_congr _ _ (bodies function) next
  cases term <;> simp only [closureTermWithContext, functions, closures, fallbacks]
  case CallIndirect callee sig args convention =>
    have calleeCheck : checkFunctionItemCalleeType source callee = checkFunctionItemCalleeType target callee :=
      funext (calleeTypes callee (by exact (trustIrListMemConsSelf) _ _))
    simp only [calleeCheck, items, bodyChecks]
  case InvokeIndirect callee sig args convention normal normalArgs unwind =>
    have calleeCheck : checkFunctionItemCalleeType source callee = checkFunctionItemCalleeType target callee :=
      funext (calleeTypes callee (by exact (trustIrListMemConsSelf) _ _))
    simp only [calleeCheck, items, bodyChecks]

/-- The actual strategy-directed terminator adds only the target byte model
    to the complete closure/function resolution observations. -/
theorem stepTermWithContext_congr (source target : EvalContext) (depth : Nat) (cfg : CFG)
    (term : Inst) (strategy : PanicStrategy)
    (models : source.byteModel = target.byteModel)
    (functions : ∀ held function signature convention,
      functionCallWithConvention source held function signature convention =
        functionCallWithConvention target held function signature convention)
    (closures : ∀ cid function captures signature args convention,
      closureCall source cid function captures signature args convention =
        closureCall target cid function captures signature args convention)
    (calleeTypes : ∀ operand ∈ operandIds term, ∀ value,
      checkFunctionItemCalleeType source operand value = checkFunctionItemCalleeType target operand value)
    (items : ∀ function signature convention,
      functionItemCall source function signature convention = functionItemCall target function signature convention)
    (bodies : ∀ function,
      (resolveFunctionItemBody source function).map (fun _ => ()) =
        (resolveFunctionItemBody target function).map (fun _ => ())) :
    stepTermWithContext source depth cfg term strategy =
      stepTermWithContext target depth cfg term strategy := by
  cases strategy <;> unfold stepTermWithContext <;>
    apply closureTermWithContext_congr source target depth term _ _ functions closures calleeTypes items bodies <;>
    rw [models]

end TrustIr.GenericCoro
