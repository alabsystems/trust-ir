-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixInduction

namespace TrustIr.GenericCoro.Prefix

/-- The selected-entry relation at every fuel lifts through the real call
    header and saved-frame protocol. Caller states and both budgets are
    unrestricted; the relation includes exact errors and non-SSA worlds. -/
theorem runCallEquivalent_of_selectedEffects (source target : EvalFunction)
    (body : source.body = target.body)
    (effects : ∀ (ctx : EvalContext) (selected : FuncId) (fuel : Nat),
      SelectedEffects (evaluatorAt fuel) (evaluatorAt fuel) ctx
        (withFunction ctx selected source).functions
        (withFunction ctx selected target).functions source target) :
    RunCallEquivalent source target := by
  intro ctx selected fuel depth args strategy
  apply runCallReq_eq_of_effectRelation
    (withFunction ctx selected source) (withFunction ctx selected target)
    fuel depth selected args strategy source target
    (withFunction_found ctx selected source) (withFunction_found ctx selected target) body
  intro world
  simpa only [evaluatorAt, scopedContext, withFunction, EvalContext.forFunction] using
    effects ctx selected fuel depth args strategy world

/-- Complete helper equality preserves the actual caller-entry computation,
    including zero fuel, zero call depth and arbitrary operand lookups. -/
theorem callEquivalent_of_runCallEquivalent (source target : EvalFunction)
    (calls : RunCallEquivalent source target) : CallEquivalent source target := by
  intro ctx selected cfg pc params args argIds strategy found fuel depth
  apply callEntry_eq_of_runCallReq _ _ selected cfg pc params args argIds strategy found
    (fuel := fuel) (depth := depth)
  intro calleeFuel calleeDepth values
  exact calls ctx selected calleeFuel calleeDepth values strategy

theorem callEquivalent_of_selectedEffects (source target : EvalFunction)
    (body : source.body = target.body)
    (effects : ∀ (ctx : EvalContext) (selected : FuncId) (fuel : Nat),
      SelectedEffects (evaluatorAt fuel) (evaluatorAt fuel) ctx
        (withFunction ctx selected source).functions
        (withFunction ctx selected target).functions source target) :
    CallEquivalent source target :=
  callEquivalent_of_runCallEquivalent source target
    (runCallEquivalent_of_selectedEffects source target body effects)

end TrustIr.GenericCoro.Prefix
