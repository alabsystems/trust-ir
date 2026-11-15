-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.ProgramRefinement

namespace TrustIr

/-- Erase ghost input/consumption while retaining every program value and
    world field, including the actual sign of a returned min/max zero. -/
def Outcome.eraseFloatZeroChoices : Outcome → Outcome
  | .returns (values, state) => .returns (values, state.eraseFloatZeroChoices)
  | outcome => outcome

/-- Full function behavior over all infinite choice streams. The original
    behavior relation retains its complete fuel, depth and refusal scope. -/
def BehavesFnWithFloatChoices (ctx : EvalContext) (strategy : PanicStrategy)
    (entry : FuncId) (args : List Value) (state : MachineState) (outcome : Outcome) : Prop :=
  ∃ choices internal,
    BehavesFn ctx strategy entry args (state.withFloatZeroChoices choices) internal ∧
      internal.eraseFloatZeroChoices = outcome

/-- Refinement of the full choice-union denotation. Source UB freedom ranges
    over all streams, including streams that make a later sign observation UB. -/
def program_refinesWithFloatChoices (strategy : PanicStrategy)
    (transform : EvalContext → EvalContext) : Prop :=
  ∀ ctx entry args state,
    ¬ BehavesFnWithFloatChoices ctx strategy entry args state .ub →
    ∀ outcome, BehavesFnWithFloatChoices (transform ctx) strategy entry args state outcome →
      BehavesFnWithFloatChoices ctx strategy entry args state outcome

theorem program_refines_withFloatChoices {strategy : PanicStrategy}
    {transform : EvalContext → EvalContext} (refines : program_refines strategy transform) :
    program_refinesWithFloatChoices strategy transform := by
  intro ctx entry args state noUB outcome target
  rcases target with ⟨choices, internal, target, erased⟩
  have noUBAtChoices : ¬ BehavesFn ctx strategy entry args
      (state.withFloatZeroChoices choices) .ub := by
    intro sourceUB
    exact noUB ⟨choices, .ub, sourceUB, rfl⟩
  exact ⟨choices, internal, refines ctx entry args _ noUBAtChoices internal target, erased⟩

theorem unreachableToReturn_program_refinesWithFloatChoices :
    program_refinesWithFloatChoices .abort (mapFunctionCFGs unreachableToReturn) :=
  program_refines_withFloatChoices unreachableToReturn_program_refines

end TrustIr
