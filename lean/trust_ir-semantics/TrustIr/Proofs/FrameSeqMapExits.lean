-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameMemoryRecursion
import TrustIr.Proofs.GenericCoroPrefixBody
import TrustIr.Proofs.NatRBMapInsert

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

private theorem check_action {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,True.intro,.refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

/-- A manual header cache must not inject an unrelated runtime unwind state. -/
def HeaderContextErrors (ctx : EvalContext) : Prop :=
  ∀ id result, ctx.functionHeaders id = some result → ExceptNoUnwind result

theorem HeaderContextErrors.forFunction (ctx : EvalContext) (function : EvalFunction)
    (safe : HeaderContextErrors ctx) : HeaderContextErrors (ctx.forFunction function) := safe

theorem HeaderContextErrors.no_unwind (ctx : EvalContext) (safe : HeaderContextErrors ctx)
    (id : FuncId) (exception : Addr) (state : MachineState) :
    ctx.functionHeaders id ≠ some (.error (.unwinding exception state)) := by
  intro found
  exact safe id _ found exception state rfl

theorem header_context_errors_empty : HeaderContextErrors EvalContext.empty := by
  intro id result found
  cases found

/-- The original first-wins header fold retains only supplied static results,
including malformed and duplicate source rows. -/
theorem decoded_header_fold_errors (signatures : Array FuncTyDef)
    (functions : List TrustIrEval.Function) (id : FuncId) (result : Except SemError FunctionHeader)
    (found : (functions.foldl (fun table function =>
      if table.contains function.id.index then table
      else table.insert function.id.index (match (trustIrArrayGet? signatures function.ty.index) with
        | some signature => .ok { signature, callingConv := function.callingConvention }
        | none => .error (.typeError s!"function {function.id.index}: original signature is absent")))
      (Lean.mkRBMap Nat (Except SemError FunctionHeader) compare)).find? id.index = some result) :
    ExceptNoUnwind result := by
  change (NatRBMapInsert.firstWinsFrom (fun function : TrustIrEval.Function => function.id.index)
    (fun function => match (trustIrArrayGet? signatures function.ty.index) with
      | some signature => .ok { signature, callingConv := function.callingConvention }
      | none => .error (.typeError s!"function {function.id.index}: original signature is absent"))
    functions (Lean.mkRBMap ..)).find? id.index = some result at found
  rw [NatRBMapInsert.firstWins_empty_find] at found
  induction functions with
  | nil => cases found
  | cons head tail ih =>
    simp only [NatRBMapInsert.firstValue] at found
    split at found
    · cases selected : (trustIrArrayGet? signatures head.ty.index) <;> rw [selected] at found <;> cases found <;>
        intro exception after same <;> cases same
    · exact ih found

/-- Successful original context assembly discharges header error safety;
no body availability or eager signature validation is introduced. -/
theorem decoded_context_header_errors (source : TrustIrEval.Module) (depth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source depth = .ok ctx) : HeaderContextErrors ctx := by
  unfold TrustIrEval.contextOf at assembled
  simp only [bind,pure,Except.bind,Except.pure,TrustIrEval.unsupported,
    throw,throwThe,MonadExceptOf.throw] at assembled
  repeat' first
    | (solve | cases assembled; intro id result found; exact decoded_header_fold_errors _ _ id result found)
    | (solve | cases assembled)
    | split at assembled

/-- The actual decoder installs the already-qualified aggregate preparer. -/
theorem decoded_context_memory_errors (source : TrustIrEval.Module) (depth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source depth = .ok ctx) : MemoryContextErrors ctx := by
  unfold TrustIrEval.contextOf at assembled
  simp only [bind,pure,Except.bind,Except.pure,TrustIrEval.unsupported,
    throw,throwThe,MonadExceptOf.throw] at assembled
  repeat' first
    | (solve | cases assembled; apply prepared_memory_context_errors; exact congrArg some (TrustIrEval.memoryServiceOf_eq _ _))
    | (solve | cases assembled)
    | split at assembled

/-- Allocate the original mutable cell without publishing an SSA alias. -/
theorem seqmap_cell_world_exit (model : ByteModel) (size alignment : Nat) :
    FrameActionValid (fun _ pointer => MintedValue 0 pointer) (do
      let before ← Sem.getState
      Sem.checkTargetAllocation model before.memory size alignment 0
      let (address,memory) := before.memory.alloc size alignment 0 .rustStack
      let id := AllocId.mk before.memory.nextAllocId
      Sem.setState {before with memory,permissions := before.permissions.set id .owned}
      pure (.ptr address (some id))) := by
  intro state valid
  apply frame_get_bind_exit
  cases checked : checkWordAllocation model state.memory size alignment 0 with
  | error error =>
    simp only [Sem.checkTargetAllocation,Sem.fromMemoryExcept,checked,throw_bind_sem]
    cases error <;> first
      | exact True.intro
      | exact False.elim (word_allocation_no_unwind _ _ _ _ _ _ _ checked)
  | ok unit =>
    cases unit
    simp only [Sem.checkTargetAllocation,Sem.fromMemoryExcept,checked,pure_bind]
    cases allocated : state.memory.alloc size alignment 0 .rustStack with
    | mk address memory =>
      exact ⟨⟨valid.table,valid.values⟩,(mintedValue_iff_shape _ _).2 True.intro,
        ⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

/-- Full cell lifecycle, with the actual opaque callback's exits explicit.
Store never publishes the input value; read-back supplies its own mint receipt. -/
theorem seqmap_element_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (invoke : Value → Sem (List Value)) (element : Value)
    (callback : ∀ pointer, MintedValue 0 pointer → FrameActionValid (fun _ _ => True) (invoke pointer)) :
    FrameActionValid MintedValue (seqMapElement ctx ty invoke element) := by
  have normalize : seqMapElement ctx ty invoke element = (do
      let layout ← Sem.fromMemoryExcept (ctx.memoryLayout ty)
      let pointer ← (do
        let before ← Sem.getState
        Sem.checkTargetAllocation ctx.byteModel before.memory layout.size layout.alignment 0
        let (address,memory) := before.memory.alloc layout.size layout.alignment 0 .rustStack
        let id := AllocId.mk before.memory.nextAllocId
        Sem.setState {before with memory,permissions := before.permissions.set id .owned}
        pure (.ptr address (some id)))
      ctx.storeMemoryValue ty pointer element
      let _ ← invoke pointer
      ctx.loadMemoryValue ty pointer) := by
    simp only [seqMapElement,bind_assoc,pure_bind]
  rw [normalize]
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state
    (check_action _ (context_memory_layout_no_unwind ctx safe ty) state valid)
  intro layout state valid _
  apply FrameActionExit.bind (fun _ pointer => MintedValue 0 pointer) MintedValue _ _ state
    (seqmap_cell_world_exit ctx.byteModel layout.size layout.alignment state valid)
  intro pointer state valid pointerMinted
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state
    (context_store_value_frame_exit ctx safe ty pointer element false state valid)
  intro unit state valid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state (callback pointer pointerMinted state valid)
  intro returned state valid _
  exact context_load_value_frame_exit ctx safe ty pointer false state valid

local macro "static_errors" : tactic => `(tactic|
  repeat' first
    | (solve | intro exception after same; cases same)
    | (simp only [Except.bind,pure_bind])
    | split
    | (dsimp only; split))

theorem seqmap_element_check_no_unwind (ctx : EvalContext) (inst : Inst) (ty : Ty) (element : Value) :
    ExceptNoUnwind (ctx.checkSeqMapElement inst ty element) := by
  unfold EvalContext.checkSeqMapElement
  static_errors



private theorem pure_exit {α : Type} (value : α) :
    FrameActionValid (fun _ _ => True) (pure value : Sem α) := by
  intro state valid
  exact ⟨valid,True.intro,.refl _⟩

private theorem throw_exit {α : Type} (error : SemError) (safe : StaticLookupError error) :
    FrameActionValid (fun _ _ => True) (throw error : Sem α) := by
  intro state valid
  cases error <;> first | exact True.intro | exact False.elim safe

private theorem abi_exit (abi : Option SignatureAbi) :
    FrameActionValid (fun _ _ => True) (requireUntypedAbi abi) := by
  unfold requireUntypedAbi
  split
  · intro state valid; exact True.intro
  · exact pure_exit _

/-- The compiled original guard distributes its continuation into both
branches. Its refusal and its actual ABI/body continuation are both covered. -/
private theorem header_then_exit (header : FunctionHeader) (callee : EvalFunction)
    (next : Sem (List Value)) (safe : FrameActionValid (fun _ _ => True) next) :
    FrameActionValid (fun _ _ => True)
      (if !(header.matches callee) then do
        let _ ← (Sem.throwTypeError "SeqMap: original header does not match executable function metadata" : Sem Unit)
        next
      else do
        let _ ← pure ()
        next) := by
  rw [HistoryEffects.conditional_property_iff (FrameActionValid (fun _ _ => True))]
  constructor
  · intro selected state valid
    exact True.intro
  · intro selected state valid
    exact safe state valid

/-- Lazy function errors and real executable lookup, after the cell store. -/
theorem seqmap_invoke_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (header : FunctionHeader) (id : FuncId) (invoke : EvalFunction → Value → Sem (List Value))
    (callback : ∀ callee, ctx.functions id = some callee → ∀ pointer, MintedValue 0 pointer →
      FrameActionValid (fun _ _ => True) (invoke callee pointer)) (pointer : Value) (pointerMinted : MintedValue 0 pointer) :
    FrameActionValid (fun _ _ => True) (seqMapInvoke ctx header id invoke pointer) := by
  intro state valid
  dsimp only [seqMapInvoke, Sem.run, StateT.run, StateT.bind, StateT.pure]
  cases failure : ctx.functionErrors id with
  | some error =>
    simp only [failure]
    exact throw_exit error (safe id error failure) state valid
  | none =>
    simp only [failure]
    unfold EvalContext.lookupDirectCallee
    cases found : ctx.functions id with
    | none =>
      cases ctx.declared id <;> exact True.intro
    | some callee =>
      simp only [found]
      change FrameActionExit (fun _ _ => True) state (Sem.run (do
        if !(header.matches callee) then
          Sem.throwTypeError "SeqMap: original header does not match executable function metadata"
        requireUntypedAbi callee.body.abi
        invoke callee pointer) state)
      apply header_then_exit header callee _ ?_ state valid
      intro state valid
      apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (abi_exit _ state valid)
      intro unit state valid _
      cases unit
      exact callback callee found pointer pointerMinted state valid

theorem seqmap_apply_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (memory : MemoryContextErrors ctx) (inst : Inst) (header : FunctionHeader) (id : FuncId) (ty : Ty)
    (invoke : EvalFunction → Value → Sem (List Value))
    (callback : ∀ callee, ctx.functions id = some callee → ∀ pointer, MintedValue 0 pointer →
      FrameActionValid (fun _ _ => True) (invoke callee pointer)) (element : Value) :
    FrameActionValid MintedValue (seqMapApply ctx inst header id ty invoke element) := by
  unfold seqMapApply
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state
    (check_action _ (seqmap_element_check_no_unwind ctx inst ty element) state valid)
  intro unit state valid _
  cases unit
  exact seqmap_element_frame_exit ctx memory ty _ element
    (seqmap_invoke_frame_exit ctx safe header id invoke callback) state valid

/-- The accumulator remains minted at the actual growing frame counter. -/
theorem seqmap_elements_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (memory : MemoryContextErrors ctx) (inst : Inst) (header : FunctionHeader) (id : FuncId) (ty : Ty)
    (invoke : EvalFunction → Value → Sem (List Value))
    (callback : ∀ callee, ctx.functions id = some callee → ∀ pointer, MintedValue 0 pointer →
      FrameActionValid (fun _ _ => True) (invoke callee pointer)) (elements mapped : List Value)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage mapped) :
    FrameActionExit MintedArgs state (Sem.run (forIn elements mapped (fun element accumulated => do
      let value ← seqMapApply ctx inst header id ty invoke element
      pure (.yield (accumulated ++ [value])))) state) := by
  induction elements generalizing mapped state with
  | nil => exact ⟨valid,incoming,.refl _⟩
  | cons element rest ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc,pure_bind]
    apply FrameActionExit.bind (fun bound value => MintedValue bound value ∧ MintedArgs bound mapped) MintedArgs _ _ state
    · have step := seqmap_apply_frame_exit ctx safe memory inst header id ty invoke callback element state valid
      cases result : Sem.run (seqMapApply ctx inst header id ty invoke element) state with
      | error error => rw [result] at step; cases error <;> exact step
      | ok pair =>
        rw [result] at step
        exact ⟨step.1,⟨step.2.1,fun value member => (incoming value member).mono step.2.2.monotone⟩,step.2.2⟩
    · intro value after afterValid transported
      apply ih (mapped ++ [value]) after afterValid
      intro held member
      rcases mem_append_iff'.mp member with old | fresh
      · exact transported.2 held old
      · have same : held = value := by simpa using fresh
        subst held
        exact transported.1

private theorem header_exit (ctx : EvalContext) (safe : HeaderContextErrors ctx) (id : FuncId) :
    FrameActionValid (fun _ _ => True) (ctx.lookupFunctionHeader id) := by
  unfold EvalContext.lookupFunctionHeader
  cases found : ctx.functionHeaders id with
  | some result => exact check_action result (safe id result found)
  | none => cases ctx.functions id with
    | some fn => exact pure_exit _
    | none => intro state valid; exact True.intro

/-- Complete original loop and checked result publication, for actual callbacks
with full error exits; empty maps retain their original lazy per-element checks. -/
theorem seqmap_run_frame_exit (ctx : EvalContext) (safe : StaticFunctionErrors ctx)
    (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx) (inst : Inst)
    (dests : List ValueId) (id : FuncId) (elements : List Value)
    (invoke : EvalFunction → Value → Sem (List Value))
    (callback : ∀ callee, ctx.functions id = some callee → ∀ pointer, MintedValue 0 pointer →
      FrameActionValid (fun _ _ => True) (invoke callee pointer)) :
    FrameActionValid (fun _ _ => True) (seqMapRun ctx inst dests id elements invoke) := by
  unfold seqMapRun
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (header_exit ctx headers id state valid)
  intro header state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (abi_exit _ state valid)
  intro unit state valid _
  cases unit
  repeat' first
    | (solve | exact True.intro)
    | (simp only [pure_bind])
    | (apply FrameActionExit.bind MintedArgs (fun _ _ => True) _ _ state
        (seqmap_elements_frame_exit ctx safe memory inst header id _ invoke callback elements [] state valid
          (fun _ member => nomatch member)); intro mapped state valid minted)
    | (apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
        (call_results_frame_exit ctx inst dests [.sequence mapped] state valid (by
          intro value member
          have same : value = .sequence mapped := by simpa using member
          subst value
          exact (mintedValue_iff_shape _ _).2 minted)); intro unit state valid _; cases unit)
    | (solve | exact ⟨valid,True.intro,.refl _⟩)
    | split
    | (dsimp only; split)



theorem seqmap_returns_readonly (types : List Ty) (values : List Value) :
    CallCheckReadOnly (seqMapReturns types values) := by
  intro state pair run
  unfold seqMapReturns at run
  cases arity : checkReturnArity values types with
  | error message => simp only [arity,Sem.throwTypeError,throw_bind_sem] at run; cases run
  | ok unit =>
    cases unit
    simp only [arity,pure_bind] at run
    unfold Sem.rejectPoisonValues at run
    split at run
    · cases run
    · cases run; rfl

theorem seqmap_returns_no_unwind (types : List Ty) (values : List Value) :
    CallCheckNoUnwind (seqMapReturns types values) := by
  intro state exception after run
  unfold seqMapReturns at run
  cases arity : checkReturnArity values types with
  | error message => simp only [arity,Sem.throwTypeError,throw_bind_sem] at run; cases run
  | ok unit =>
    cases unit
    simp only [arity,pure_bind] at run
    unfold Sem.rejectPoisonValues at run
    split at run <;> cases run

/-- The actual original call-frame protocol discharges the opaque callback
premise using its checked return and the recursive callee exit contract. -/
theorem seqmap_step_frame_exit (recurse : Recurse) (ctx : EvalContext)
    (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx)
    (depth : Nat) (strategy : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elements : List Value) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (seqMapStep recurse ctx depth strategy inst dests id elements) := by
  cases depth with
  | zero => intro state valid; exact True.intro
  | succ depth =>
    rw [seqMapStep_framed]
    apply seqmap_run_frame_exit ctx safe headers memory inst dests id elements
    intro callee found pointer pointerMinted state valid
    have execution := callees id callee found depth [pointer] (callerWorld state)
      ⟨valid.table,values_empty _⟩ (by
        intro value member
        have same : value = pointer := by simpa using member
        subst value
        exact pointerMinted.mono (Nat.zero_le _))
    have framed := (FrameActionExit.callee state _).2 (call_frame_with_exit _ _ state valid
      (seqmap_returns_readonly callee.body.returnTys) (seqmap_returns_no_unwind callee.body.returnTys) execution)
    cases result : Sem.run (callFrameWith (seqMapReturns callee.body.returnTys)
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock [pointer] strategy)) state with
    | error error => rw [result] at framed; cases error <;> exact framed
    | ok pair => rw [result] at framed; exact ⟨framed.1,True.intro,framed.2.2⟩

/-- Original request production and complete body dispatch, including the
actual lookup errors and original result destinations. -/
theorem seqmap_body_frame_exit (recurse : Recurse) (ctx : EvalContext)
    (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx)
    (depth : Nat) (strategy : PanicStrategy) (ty : Ty) (operand : ValueId) (id : FuncId)
    (dests : List ValueId) (callees : FrameCalleeExitContract recurse ctx strategy) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.SeqMap ty operand id,dests)) := by
  rw [evalBodyStep_dispatch]
  simp only [bodyDispatch,stepInstWithContext,stepInst,bind_assoc]
  intro state valid
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action operand state valid)
  intro value state valid _
  cases value <;> simp only [pure_bind,producedStep]
  case sequence elements incoming =>
    exact seqmap_step_frame_exit recurse ctx safe headers memory depth strategy (.SeqMap ty operand id) dests id elements callees state valid
  all_goals exact True.intro

end TrustIr.FrameLifetime
