-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroModuleContext
import TrustIr.Proofs.CoroutineProps

namespace TrustIr.GenericCoro.ModuleContext.Controls
open TrustIrEval ModuleFactory GenericCoroAllBlocksPlanner

private def signature : FuncTyDef :=
  {params := [.Ptr, .I32, .Bool, .Bool], returns := [.I32], isVararg := false}

/-- The fourth argument supplies the base-case flag to the recursive call.
    Both graphs retain real edges to each other; the control needs no Const
    conversion in its source execution. -/
private def mutualGraph (callee : FuncId) : Rows := [
  (⟨0⟩, {
    params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .Bool), (⟨3⟩, .Bool)],
    body := [], terminator := .CondBr ⟨2⟩ ⟨1⟩ [] ⟨2⟩ []}),
  (⟨1⟩, {
    params := [], body := [.Call callee [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩]],
    bodyResultDests := [[⟨4⟩]], terminator := .CoroSuspend ⟨0⟩ 1 19 ⟨4⟩}),
  (⟨2⟩, {params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩})]

private def definition (id callee : Nat) : Function :=
  {id := ⟨id⟩, name := "mutual", ty := ⟨0⟩, entry := ⟨0⟩,
   isDeclaration := false, blocks := .ok (mutualGraph ⟨callee⟩)}

trustIrDenseMatch
private def lowered (id callee : Nat) : Function :=
  let rows := match mutualGraph ⟨callee⟩ with
    | [entry, (firstId, first), (secondId, second)] =>
      [entry, (firstId, expandedEntry ⟨⟨5⟩, ⟨6⟩, ⟨7⟩⟩ first),
        (secondId, expandedEntry ⟨⟨8⟩, ⟨9⟩, ⟨10⟩⟩ second)]
    | _ => []
  {definition id callee with blocks := .ok rows}

def source : Module :=
  {functions := [definition 0 1, definition 1 0],
   funcTys := [signature], globals := [], enums := [], structs := [], types := []}

def target : Module := {source with functions := [lowered 0 1, lowered 1 0]}

/-- Two actual successful factory outputs, with a finite recursive path. -/
theorem actual_mutual_publication : transform source = .ready target := rfl

theorem actual_mutual_tables_preserve_every_entry (maxDepth : Nat) :
    ContextCallsEquivalent (contextOf source maxDepth) (contextOf target maxDepth) :=
  transform_ready_context_calls source target actual_mutual_publication maxDepth

def sourceContext : EvalContext :=
  match contextOf source 4 with | .ok context => context | .error _ => EvalContext.empty

def targetContext : EvalContext :=
  match contextOf target 4 with | .ok context => context | .error _ => EvalContext.empty

theorem actual_source_context_built : contextOf source 4 = .ok sourceContext := rfl

theorem actual_target_context_built : contextOf target 4 = .ok targetContext := rfl

/-- A live 16-byte frame, plus a caller binding that must survive both calls. -/
def caller : MachineState :=
  let (_, memory) := Memory.empty.alloc 16 8 0 .rustStack
  { MachineState.empty with
    memory := memory
    locals := MachineState.empty.locals.set ⟨200⟩ (.int 32 99)
    nextValueId := 201 }

def arguments : List Value := [.ptr 1024 (some ⟨0⟩), .int 32 42, .bool true, .bool false]

/-- This observes an actual finite-budget Sem.run, not just factory success
    or an instantiation of universal equality. Both suspends must store. -/
private def observeRun (outcome : Except SemError (List Value × MachineState)) : Except SemError
    (List Value × Option (List UInt8) × Option Value × Nat × Nat × Nat) :=
  match outcome with
  | .error error => .error error
  | .ok (values, state) => .ok (values, state.memory.readBytes 1024 16,
      state.lookupValue ⟨200⟩, state.nextValueId, state.memory.nextAddr, state.memory.nextAllocId)

def observation (context : EvalContext) : Except SemError
    (List Value × Option (List UInt8) × Option Value × Nat × Nat × Nat) :=
  observeRun (Sem.run (runCallReq context 4 2 ⟨0⟩ arguments .abort) caller)

private def expected : List Value × Option (List UInt8) × Option Value × Nat × Nat × Nat :=
  ([.int 32 42], some [17, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0], some (.int 32 99), 201, 1040, 1)

private def entered (choice : Bool) : MachineState :=
  { caller with
    locals := (((ValueMap.empty.set ⟨0⟩ (.ptr 1024 (some ⟨0⟩))).set ⟨1⟩ (.int 32 42)).set ⟨2⟩ (.bool choice)).set ⟨3⟩ (.bool false)
    nextValueId := 4 }

private theorem enter_true (ctx : EvalContext) (fuel depth : Nat) (callee : FuncId) :
    StateT.run (stepNWithContext ctx (fuel + 1) depth (TrustIrEval.cfgOf (mutualGraph callee)) ⟨0⟩
      arguments .abort) {caller with locals := ValueMap.empty, nextValueId := 0} =
    StateT.run (stepNWithContext ctx fuel depth (TrustIrEval.cfgOf (mutualGraph callee)) ⟨1⟩ [] .abort)
      (entered true) := rfl

private theorem enter_false (ctx : EvalContext) (fuel depth : Nat) (callee : FuncId) :
    StateT.run (stepNWithContext ctx (fuel + 1) depth (TrustIrEval.cfgOf (mutualGraph callee)) ⟨0⟩
      [.ptr 1024 (some ⟨0⟩), .int 32 42, .bool false, .bool false] .abort)
      {caller with locals := ValueMap.empty, nextValueId := 0} =
    StateT.run (stepNWithContext ctx fuel depth (TrustIrEval.cfgOf (mutualGraph callee)) ⟨2⟩ [] .abort)
      (entered false) := rfl

private def baseStored : MachineState :=
  {entered false with memory := caller.memory.writeBytes 1024 [17, 0, 0, 0, 0, 0, 0, 0]}

private theorem frame_ok : FrameOk (entered false).memory 1024 ⟨0⟩ .le64 := by
  refine ⟨{id := ⟨0⟩, base := 1024, size := 16, alive := true, origin := .rustStack, requested := 16},
    rfl, rfl, rfl, by decide, by decide, by decide, ?_⟩
  intro impossible; cases impossible

private theorem intrinsic_base :
    StateT.run (semCoroSuspend ⟨0⟩ 0 17 ⟨1⟩ .le64) (entered false) = .ok (.Ret [.int 32 42], baseStored) := by
  unfold semCoroSuspend
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_lookupValue_some ⟨0⟩ (entered false) (.ptr 1024 (some ⟨0⟩)) rfl]
  dsimp only
  simp only [Int.ofNat_zero]
  rw [sr_semGEPValues_i64_zero (fun (_ : Unit) value => typedIntegerValue .le64 .I64 value)
    () (entered false) 1024 ⟨0⟩ .le64 frame_ok rfl]
  dsimp only
  rw [sr_semStoreValue_i64_ok (entered false) 1024 ⟨0⟩ (Value.intAt 64 17)
    [17, 0, 0, 0, 0, 0, 0, 0] .le64 frame_ok rfl rfl rfl]
  dsimp only
  change StateT.run (semReturn [⟨1⟩]) baseStored = .ok (.Ret [.int 32 42], baseStored)
  exact sr_semReturn_one ⟨1⟩ baseStored (.int 32 42) rfl

private theorem suspend_base (ctx : EvalContext) (fuel depth : Nat) (callee : FuncId) :
    StateT.run (stepNWithContext {ctx with byteModel := .le64} (fuel + 1) depth
      (TrustIrEval.cfgOf (mutualGraph callee)) ⟨2⟩ [] .abort) (entered false) =
      .ok ([.int 32 42], baseStored) := by
  trustIrCompilerProof {
    have found : TrustIrEval.cfgOf (mutualGraph callee) ⟨2⟩ = some
      {params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩} := rfl
    unfold stepNWithContext
    rw [found]
    simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, bodyInstsWithResultDests,
      show bindBlockParamsChecked [] [] = bindBlockParams [] [] from rfl,
      forIn, List.forIn, List.forIn.loop, stepTermWithContext, closureTermWithContext, stepInst,
      pure_bind, bind_assoc]
    simp only [Sem.run, sr_bind, Except.bind]
    rw [sr_bindBlockParams_nil]
    dsimp only
    rw [intrinsic_base]
    rfl
  } {
    have found : TrustIrEval.cfgOf (mutualGraph callee) ⟨2⟩ = some
      {params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩} := rfl
    unfold stepNWithContext
    rw [found]
    simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, bodyInstsWithResultDests,
      show bindBlockParamsChecked [] [] = bindBlockParams [] [] from rfl,
      List.forIn_nil, List.forIn_cons, stepTermWithContext, closureTermWithContext, stepInst,
      pure_bind, bind_assoc]
    simp only [Sem.run, sr_bind, Except.bind]
    rw [sr_bindBlockParams_nil]
    dsimp only
    rw [intrinsic_base]
    rfl
  }

private def getFunction (id : FuncId) : EvalFunction :=
  match sourceContext.functions id with
  | some function => function
  | none => {body := {paramTys := [], returnTys := []}, cfg := fun _ => none, entryBlock := ⟨0⟩}

private theorem found_zero : sourceContext.functions ⟨0⟩ = some (getFunction ⟨0⟩) := rfl
private theorem found_one : sourceContext.functions ⟨1⟩ = some (getFunction ⟨1⟩) := rfl
private theorem function_zero_cfg : (getFunction ⟨0⟩).cfg = TrustIrEval.cfgOf (mutualGraph ⟨1⟩) := by
  change (IndexedCFG.indexedCFG (mutualGraph ⟨1⟩)).cfg = _
  exact DecodedCFG.indexedCFG_eq_cfgOf _
private theorem function_one_cfg : (getFunction ⟨1⟩).cfg = TrustIrEval.cfgOf (mutualGraph ⟨0⟩) := by
  change (IndexedCFG.indexedCFG (mutualGraph ⟨0⟩)).cfg = _
  exact DecodedCFG.indexedCFG_eq_cfgOf _
private theorem function_one_entry : (getFunction ⟨1⟩).entryBlock = ⟨0⟩ := rfl

private theorem callee_inline :
    StateT.run (stepNWithContext (sourceContext.forFunction (getFunction ⟨1⟩)) 2 1
      (getFunction ⟨1⟩).cfg (getFunction ⟨1⟩).entryBlock
      [.ptr 1024 (some ⟨0⟩), .int 32 42, .bool false, .bool false] .abort)
      {caller with locals := ValueMap.empty, nextValueId := 0} = .ok ([.int 32 42], baseStored) := by
  rw [function_one_cfg, function_one_entry, enter_false]
  exact suspend_base (sourceContext.forFunction (getFunction ⟨1⟩)) 0 1 ⟨0⟩

private def suspendValues (slot : Nat) (next : Int) (value : ValueId) (model : ByteModel) : Sem (List Value) := do
  let frame ← Sem.lookupValue ⟨0⟩
  let pointer ← semGEPValuesUsing (scalarMemoryLayout model)
    (fun (_ : Unit) held => typedIntegerValue model .I64 held)
    .I64 frame [((), Value.intAt 64 slot)] model
  semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model .I64)
    .I64 pointer (Value.intAt 64 next) false none model
  [value].mapM Sem.lookupValue

private theorem call_suspend_block (ctx : EvalContext) (fuel depth : Nat) (callee : FuncId) :
    stepNWithContext ctx (fuel + 1) (depth + 1) (TrustIrEval.cfgOf (mutualGraph callee)) ⟨1⟩ [] .abort = (do
      bindBlockParamsChecked [] []
      let args ← [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩].mapM Sem.lookupValue
      let returns ← runCallReq ctx fuel depth callee args
      ctx.bindCallResults (.Call callee [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩]) [⟨4⟩] returns
      suspendValues 1 19 ⟨4⟩ ctx.byteModel) := by
  trustIrCompilerProof {
    have found : TrustIrEval.cfgOf (mutualGraph callee) ⟨1⟩ = some
      {params := [], body := [.Call callee [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩]], bodyResultDests := [[⟨4⟩]],
       terminator := .CoroSuspend ⟨0⟩ 1 19 ⟨4⟩} := rfl
    unfold stepNWithContext
    rw [found]
    simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
      bodyInstsWithResultDests, forIn, List.forIn, List.forIn.loop,
      stepTermWithContext, closureTermWithContext, stepInst, semCoroSuspend, semReturn, suspendValues,
      runCallReq, EvalContext.lookupDirectCallee, pure_bind, bind_assoc, bind_pure]
    refine Prefix.bind_same _ fun _ => ?_
    refine Prefix.bind_same _ fun args => ?_
    cases _found : ctx.functions callee with
    | none => simp only [Sem.throwTypeError, Prefix.throw_bind_sem, Sem.throwUnsupported, Prefix.bind_ite_sem]
    | some function =>
      dsimp only
      simp only [pure_bind, bind_assoc]
      refine Prefix.bind_same _ fun _ => ?_
      cases arity : checkCallArity args function.body.paramTys with
      | error message => simp only [Sem.throwTypeError, Prefix.throw_bind_sem]
      | ok unit =>
        cases unit
        dsimp only
        simp only [bind_assoc]
        refine Prefix.bind_same _ fun _ => ?_
        refine Prefix.bind_same _ fun callerState => ?_
        refine Prefix.bind_same _ fun _ => ?_
        refine Prefix.bind_same _ fun returns => ?_
        cases returned : checkReturnArity returns function.body.returnTys with
        | error message => simp only [Sem.throwTypeError, Prefix.throw_bind_sem]
        | ok unit =>
          cases unit
          simp only [bind_assoc, pure_bind, bind_pure]
  } {
    have found : TrustIrEval.cfgOf (mutualGraph callee) ⟨1⟩ = some
      {params := [], body := [.Call callee [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩]], bodyResultDests := [[⟨4⟩]],
       terminator := .CoroSuspend ⟨0⟩ 1 19 ⟨4⟩} := rfl
    unfold stepNWithContext
    rw [found]
    simp only [EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
      bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
      stepTermWithContext, closureTermWithContext, stepInst, semCoroSuspend, semReturn, suspendValues,
      runCallReq, EvalContext.lookupDirectCallee, pure_bind, bind_assoc, bind_pure]
    refine Prefix.bind_same _ fun _ => ?_
    refine Prefix.bind_same _ fun args => ?_
    cases _found : ctx.functions callee with
    | none => simp only [Sem.throwTypeError, Prefix.throw_bind_sem, Sem.throwUnsupported, Prefix.bind_ite_sem]
    | some function =>
      dsimp only
      simp only [pure_bind, bind_assoc]
      refine Prefix.bind_same _ fun _ => ?_
      cases arity : checkCallArity args function.body.paramTys with
      | error message => simp only [Sem.throwTypeError, Prefix.throw_bind_sem]
      | ok unit =>
        cases unit
        dsimp only
        simp only [bind_assoc]
        refine Prefix.bind_same _ fun _ => ?_
        refine Prefix.bind_same _ fun callerState => ?_
        refine Prefix.bind_same _ fun _ => ?_
        refine Prefix.bind_same _ fun returns => ?_
        cases returned : checkReturnArity returns function.body.returnTys with
        | error message => simp only [Sem.throwTypeError, Prefix.throw_bind_sem]
        | ok unit =>
          cases unit
          simp only [bind_assoc, pure_bind, bind_pure]
  }

private def active : EvalContext := sourceContext.forFunction (getFunction ⟨0⟩)
private def baseArguments : List Value := [.ptr 1024 (some ⟨0⟩), .int 32 42, .bool false, .bool false]
private def returned : MachineState := restoreFrame baseStored (saveFrame (entered true) none) []

private theorem callee_call :
    StateT.run (runCallReq active 2 1 ⟨1⟩ baseArguments .abort) (entered true) =
      .ok ([.int 32 42], returned) := by
  apply runCallReq_ok_of_inline active 2 1 ⟨1⟩ (getFunction ⟨1⟩) baseArguments
    (entered true) baseStored [.int 32 42]
  · exact found_one
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact callee_inline

private def called : MachineState :=
  {returned with locals := returned.locals.set ⟨4⟩ (.int 32 42), nextValueId := max returned.nextValueId 5}

private theorem call_result_types :
    active.instructionResultTypes (.Call ⟨1⟩ [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩]) [⟨4⟩] 1 = .ok [.I32] := rfl

private theorem call_result_published :
    StateT.run (active.bindCallResults (.Call ⟨1⟩ [⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩]) [⟨4⟩] [.int 32 42]) returned =
      .ok ((), called) := by
  unfold EvalContext.bindCallResults EvalContext.checkInstructionResults
  simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, if_false,
    call_result_types, pure_bind]
  exact sr_bindResultDests_one ⟨4⟩ (.int 32 42) returned

private theorem frame_second_ok : FrameOk called.memory 1032 ⟨0⟩ .le64 := by
  refine ⟨{id := ⟨0⟩, base := 1024, size := 16, alive := true, origin := .rustStack, requested := 16},
    rfl, rfl, rfl, by decide, by decide, by decide, ?_⟩
  intro impossible; cases impossible

private theorem gep_second :
    StateT.run (semGEPValuesUsing (scalarMemoryLayout .le64)
      (fun (_ : Unit) held => typedIntegerValue .le64 .I64 held) .I64 (.ptr 1024 (some ⟨0⟩))
      [((), Value.intAt 64 1)] .le64) called = .ok (.ptr 1032 (some ⟨0⟩), called) := rfl

private def finalInline : MachineState :=
  {called with memory := called.memory.writeBytes 1032 [19, 0, 0, 0, 0, 0, 0, 0]}

private theorem final_suspend : StateT.run (suspendValues 1 19 ⟨4⟩ .le64) called =
    .ok ([.int 32 42], finalInline) := by
  unfold suspendValues
  simp only [sr_bind, Except.bind]
  rw [sr_lookupValue_some ⟨0⟩ called (.ptr 1024 (some ⟨0⟩)) rfl]
  dsimp only
  simp only [Int.ofNat_one]
  rw [gep_second]
  dsimp only
  rw [sr_semStoreValue_i64_ok called 1032 ⟨0⟩ (Value.intAt 64 19)
    [19, 0, 0, 0, 0, 0, 0, 0] .le64 frame_second_ok rfl rfl rfl]
  rfl

private theorem call_arguments_read :
    StateT.run ([⟨0⟩, ⟨1⟩, ⟨3⟩, ⟨3⟩].mapM Sem.lookupValue) (entered true) =
      .ok (baseArguments, entered true) := rfl

private theorem caller_inline :
    StateT.run (stepNWithContext active 4 2 (TrustIrEval.cfgOf (mutualGraph ⟨1⟩)) ⟨0⟩ arguments .abort)
      {caller with locals := ValueMap.empty, nextValueId := 0} = .ok ([.int 32 42], finalInline) := by
  rw [enter_true, call_suspend_block]
  simp only [show bindBlockParamsChecked [] [] = bindBlockParams [] [] from rfl,
    sr_bind, Except.bind]
  rw [sr_bindBlockParams_nil]
  dsimp only
  rw [call_arguments_read]
  dsimp only
  rw [callee_call]
  dsimp only
  rw [call_result_published]
  dsimp only
  exact final_suspend

private def finalWorld : MachineState := restoreFrame finalInline (saveFrame caller none) []

private theorem source_complete_run :
    Sem.run (runCallReq sourceContext 4 2 ⟨0⟩ arguments .abort) caller =
      .ok ([.int 32 42], finalWorld) := by
  apply runCallReq_ok_of_inline sourceContext 4 2 ⟨0⟩ (getFunction ⟨0⟩) arguments caller finalInline [.int 32 42]
  · exact found_zero
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [function_zero_cfg]
    exact caller_inline

theorem concrete_source_mutual_call_succeeds : observation sourceContext = .ok expected := by
  exact congrArg observeRun source_complete_run

theorem concrete_complete_runs_equal :
    Sem.run (runCallReq sourceContext 4 2 ⟨0⟩ arguments .abort) caller =
      Sem.run (runCallReq targetContext 4 2 ⟨0⟩ arguments .abort) caller :=
  transform_ready_runCallReq source target actual_mutual_publication 4 sourceContext targetContext
    actual_source_context_built actual_target_context_built ⟨0⟩ 4 2 arguments .abort caller

theorem concrete_target_mutual_call_succeeds : observation targetContext = .ok expected := by
  have observed := congrArg observeRun concrete_complete_runs_equal
  exact observed.symm.trans concrete_source_mutual_call_succeeds

end TrustIr.GenericCoro.ModuleContext.Controls

/-- info: 'TrustIr.GenericCoro.ModuleContext.Controls.target' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.Controls.target
