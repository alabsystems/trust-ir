-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameCallExits
import TrustIr.DecodedContext

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- Static function lookup failures contain diagnostics, never runtime states. -/
def StaticLookupError : SemError → Prop
  | .typeError _ | .unsupported _ _ => True
  | _ => False

def StaticFunctionErrors (ctx : EvalContext) : Prop :=
  ∀ id error, ctx.functionErrors id = some error → StaticLookupError error

theorem StaticFunctionErrors.no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (id : FuncId) (exception : Addr) (after : MachineState) :
    ctx.functionErrors id ≠ some (.unwinding exception after) := by
  intro found
  exact safe id _ found

theorem static_function_errors_empty : StaticFunctionErrors EvalContext.empty := by
  intro id error found
  cases found

theorem StaticFunctionErrors.forFunction (ctx : EvalContext) (function : EvalFunction)
    (safe : StaticFunctionErrors ctx) : StaticFunctionErrors (ctx.forFunction function) := safe

theorem StaticFunctionErrors.scoped (ctx : EvalContext) (functions : FuncId → Option EvalFunction)
    (types : Option LocalTypeTable) (safe : StaticFunctionErrors ctx) :
    StaticFunctionErrors (scopedContext ctx functions types) := safe

/-- The actual prepared lookup representation can store only decoded static
errors. This holds for every prepared table, not only well-formed modules. -/
theorem prepared_function_errors_static (prepared : TrustIrEval.FunctionLookup.Prepared)
    (id : FuncId) (error : SemError)
    (found : TrustIrEval.FunctionLookup.findError prepared id = some error) : StaticLookupError error := by
  unfold TrustIrEval.FunctionLookup.findError at found
  repeat' first
    | (solve | cases found; exact True.intro)
    | (solve | cases found)
    | split at found

/-- Successful assembly by original contextOf discharges the context-error
premise even for raw malformed/duplicate/declaration rows retained lazily. -/
theorem decoded_context_errors_static (source : TrustIrEval.Module) (depth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source depth = .ok ctx) : StaticFunctionErrors ctx := by
  unfold TrustIrEval.contextOf at assembled
  simp only [bind,pure,Except.bind,Except.pure,TrustIrEval.unsupported,
    throw,throwThe,MonadExceptOf.throw] at assembled
  repeat' first
    | (solve | cases assembled; intro id error found; exact prepared_function_errors_static _ id error found)
    | (solve | cases assembled)
    | split at assembled

/-- Original FnDef application retains all signature/ABI/body checks. The
static-error premise rules out precisely the injected unwind counterexample. -/
theorem function_call_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : FuncTyId) (target : FuncId) (sig : FuncTyId) (exception : Addr) (after : MachineState) :
    functionCall ctx held target sig ≠ .error (.unwinding exception after) := by
  intro run
  unfold functionCall at run
  simp only [bind,pure,Except.bind,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
  repeat' first
    | (solve | cases run)
    | (solve | cases run; exact safe.no_unwind ctx target _ _ (by assumption))
    | split at run

/-- The additional guard returns a type error, never an unwind state. -/
theorem function_call_with_convention_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : FuncTyId) (target : FuncId) (sig : FuncTyId) (convention : CallingConv)
    (exception : Addr) (after : MachineState) :
    functionCallWithConvention ctx held target sig convention ≠ .error (.unwinding exception after) := by
  intro run
  unfold functionCallWithConvention at run
  cases checked : functionCall ctx held target sig with
  | error error =>
    rw [checked] at run
    cases run
    exact function_call_no_unwind ctx safe held target sig exception after checked
  | ok resolved =>
    rw [checked] at run
    cases found : ctx.functions resolved with
    | none => simp only [found] at run; cases run
    | some callee =>
      simp only [found] at run
      split at run <;> cases run

theorem function_arguments_no_unwind (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : FuncTyId) (target : FuncId) (address : Addr) (sig : FuncTyId)
    (args : List Value) (conv : CallingConv) :
    CallCheckNoUnwind (indirectArguments ctx (.fnDef held target) address sig args conv) := by
  intro state exception after run
  cases checked : functionCallWithConvention ctx held target sig conv with
  | ok id => simp only [indirectArguments,checked] at run; cases run
  | error error =>
    simp only [indirectArguments,checked] at run
    cases run
    exact function_call_with_convention_no_unwind ctx safe held target sig conv exception after checked

/-- State-specific FnDef argument preparation consumes actual original checks
and transports already-minted arguments without modifying the caller state. -/
theorem function_arguments_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (held : FuncTyId) (target : FuncId) (address : Addr) (sig : FuncTyId)
    (args : List Value) (conv : CallingConv) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun bound call => MintedArgs bound call.2) state
      (Sem.run (indirectArguments ctx (.fnDef held target) address sig args conv) state) := by
  cases executed : Sem.run (indirectArguments ctx (.fnDef held target) address sig args conv) state with
  | ok pair =>
    obtain ⟨resolved,after⟩ := pair
    have heldValid : MintedValue state.nextFrameLineage (.fnDef held target) := by
      intro lineage occurrence
      cases occurrence
    obtain ⟨same,returned⟩ := indirect_arguments_success state.nextFrameLineage ctx (.fnDef held target) address sig args conv state after resolved heldValid incoming executed
    subst after
    exact ⟨valid,returned,.refl _⟩
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (function_arguments_no_unwind ctx safe held target address sig args conv state _ _ executed)

/-- Direct target lookup never forwards the dynamic function-error field:
its unchanged bodyless/missing refusals cannot carry an unwind state. -/
theorem direct_lookup_no_unwind (ctx : EvalContext) (id : FuncId) (declaredMessage missingMessage : String) :
    CallCheckNoUnwind (ctx.lookupDirectCallee id declaredMessage missingMessage) := by
  intro state exception after run
  cases found : ctx.functions id with
  | some function => simp only [EvalContext.lookupDirectCallee,found] at run; cases run
  | none =>
    cases declared : ctx.declared id <;>
      simp [EvalContext.lookupDirectCallee,found,declared,Sem.throwTypeError,Sem.throwUnsupported,
        Sem.run,StateT.run,StateT.lift,throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run

theorem direct_lookup_frame_action (ctx : EvalContext) (id : FuncId) (declaredMessage missingMessage : String) :
    FrameActionValid (fun _ _ => True) (ctx.lookupDirectCallee id declaredMessage missingMessage) := by
  apply frame_action_of_success_no_unwind _ _ (direct_lookup_no_unwind ctx id declaredMessage missingMessage)
  intro state after function valid run
  cases found : ctx.functions id with
  | some callee =>
    simp only [EvalContext.lookupDirectCallee,found] at run
    cases run
    exact ⟨valid,True.intro,.refl _⟩
  | none =>
    cases declared : ctx.declared id <;>
      simp [EvalContext.lookupDirectCallee,found,declared,Sem.throwTypeError,Sem.throwUnsupported,
        Sem.run,StateT.run,StateT.lift,throw,throwThe,MonadExceptOf.throw,bind,pure,Except.bind,Except.pure] at run

end TrustIr.FrameLifetime
