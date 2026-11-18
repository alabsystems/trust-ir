-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemRScalarFreshStep
import TrustIr.Proofs.ReturnBlockLayer
import TrustIr.Proofs.FunctionEntryLayer
import TrustIr.Proofs.GenericCoroPrefixLoop

/-! A complete call-free U64 division/return block, through the two actual
executors. This is a block correspondence, not a decoder, module-entry,
whole-CFG or source/ABI translation theorem. -/

namespace SemR.CanonicalScalarReturn
open SemR.CanonicalScalarStep

def returnNode (destination : Nat) : SemR.Node :=
  { inst := .ret [destination], results := [] }

theorem source_return_step (m : SemR.Module) (before : SemR.Core)
    (destination returned : Nat)
    (atNode : SemR.nth? before.block.body before.pc = some (returnNode destination))
    (lookup : SemR.lookupEnv before.env destination = some (.int .u64 returned))
    (returns : before.sig.returns = [.int .u64]) (outermost : before.stack = [])
    (range : returned < 2 ^ 64) :
    SemR.stepCore m before = .done (.ret [.int .u64 returned]) := by
  simp [SemR.stepCore, atNode, SemR.execNode, returnNode, SemR.retStep,
    SemR.getVs, SemR.getV, lookup, SemR.checkSig, returns, SemR.rejectPoison,
    SemR.Val.ty, SemR.Ty.beq, SemR.IntTy.code, SemR.expectTy,
    SemR.IntTy.bits, SemR.modulus, range, SemR.returnTo, outermost,
    SemR.ofR, bind, SemR.R.bind, pure]

/-- Both original nodes are executed; a zero divisor ends before the return.
The result is independent of extra fuel and unused call depth or module data. -/
theorem source_division_return (m : SemR.Module) (before : SemR.Core)
    (left right destination dividend divisor extra : Nat)
    (body : before.block.body =
      [divisionNode left right destination, returnNode destination])
    (entry : before.pc = 0)
    (leftLookup : SemR.lookupEnv before.env left = some (.int .u64 dividend))
    (rightLookup : SemR.lookupEnv before.env right = some (.int .u64 divisor))
    (returns : before.sig.returns = [.int .u64]) (outermost : before.stack = [])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    SemR.run m (extra + 2) before =
      if divisor = 0 then .ub "unsigned division by zero"
      else .ret [.int .u64 (dividend / divisor)] := by
  have first := source_step m before left right destination dividend divisor
    (by simp [body, entry, SemR.nth?]) leftLookup rightLookup leftRange rightRange
  have quotientRange : dividend / divisor < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leftRange
  have second := source_return_step m (sourceAfter before destination (dividend / divisor))
    destination (dividend / divisor)
    (by simp [sourceAfter, body, entry, SemR.nth?])
    (by simp [source_after_lookup]) returns outermost quotientRange
  by_cases zero : divisor = 0 <;> simp [SemR.run, first, second, zero]

open TrustIr in
private theorem scalar_has_no_function_items (prepared : FunctionItemPresence.Prepared) :
    prepared.hasFnItem .U64 = false := by
  exact prepared.hasFnItem_u64

open TrustIr in
private theorem scalar_return_check (ctx : EvalContext) (returned : Int) :
    checkFunctionItemValues ctx [.U64] [.int 64 returned] = .ok () := by
  simp [checkFunctionItemValues, List.forM_cons, List.forM_nil, checkFunctionItemLanes,
    checkFunctionItemLayer, Value.depth, Value.depthSpec, Value.isUninit,
    scalar_has_no_function_items, bind, Except.bind, pure, Except.pure]

open TrustIr in
theorem target_return (ctx : EvalContext) (before : MachineState)
    (destination : Nat) (returned : Int)
    (lookup : before.lookupValue ⟨destination⟩ = some (.int 64 returned))
    (returns : ctx.functionReturnTypes = some [.U64]) :
    Sem.run (AYUnaryReplay.checkedReturnValues ctx [⟨destination⟩]) before =
      .ok ([.int 64 returned], before) := by
  simp [AYUnaryReplay.checkedReturnValues, AYUnaryReplay.returnValues,
    GenericCoro.checkedReturn, returns, List.mapM, List.mapM.loop,
    Sem.run, sr_bind, sr_lookup, lookup, sr_memoryExcept, scalar_return_check,
    sr_pure, bind, pure, Functor.map, Except.bind, Except.map, Except.pure,
    StateT.bind, StateT.map, StateT.pure, StateT.run, StateT.lift, Sem.fromMemoryExcept,
    Sem.lookupValue, Sem.getState, StateT.get]

open TrustIr in
theorem target_body_singleton (recurse : GenericCoro.Prefix.Recurse)
    (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (row : TrustIr.Inst × List ValueId) (before : MachineState) :
    Sem.run (GenericCoro.Prefix.evalBody recurse ctx depth strategy [row]) before =
      (Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy row) before).bind
        (fun pair => .ok ((), pair.2)) := by
  rw [GenericCoro.Prefix.evalBody_cons, GenericCoro.Prefix.evalBody_nil, Sem.run_bind]
  rfl

open TrustIr in
def canonicalBlock (left right destination : Nat) : BasicBlock :=
  { params := [], body := [.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩],
    bodyResultDests := [[⟨destination⟩]], terminator := .Return [⟨destination⟩] }

open TrustIr in
private theorem target_no_parameters (ctx : EvalContext) (before : MachineState)
    (left right destination : Nat) :
    Sem.run (AYUnaryReplay.bindParameters ctx
      (ctx.resolveBlock (canonicalBlock left right destination)) []) before =
      .ok ((), before) := rfl

open TrustIr in
theorem target_body_return (ctx : EvalContext) (before : MachineState)
    (recurse : GenericCoro.Prefix.Recurse) (depth : Nat)
    (left right destination dividend divisor : Nat)
    (leftLookup : before.lookupValue ⟨left⟩ = some (.int 64 (dividend : Int)))
    (rightLookup : before.lookupValue ⟨right⟩ = some (.int 64 (divisor : Int)))
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩)
      [⟨destination⟩] 1 = .ok [.U64])
    (returns : ctx.functionReturnTypes = some [.U64])
    (fresh : SSAFreshFrames.FreshState before)
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    Sem.run (do
      GenericCoro.Prefix.evalBody recurse ctx depth .abort
        [(.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩, [⟨destination⟩])]
      AYUnaryReplay.checkedReturnValues ctx [⟨destination⟩]) before =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((dividend / divisor : Nat) : Int)],
        targetAfter before destination (dividend / divisor)) := by
  rw [Sem.run_bind, target_body_singleton,
    target_step_raw _ ctx depth .abort before left right destination dividend divisor
      leftLookup rightLookup declarations leftRange rightRange]
  have lookup : (targetAfter before destination (dividend / divisor)).lookupValue
      ⟨destination⟩ = some (.int 64 ((dividend / divisor : Nat) : Int)) := by
    simpa using target_after_lookup before destination (dividend / divisor) destination
      (fresh ⟨before.nextValueId⟩ (Nat.le_refl _))
  have finished := target_return ctx (targetAfter before destination (dividend / divisor))
    destination ((dividend / divisor : Nat) : Int) lookup returns
  by_cases zero : divisor = 0 <;> simp [zero, Except.bind, finished]

open TrustIr in
theorem target_division_return (ctx : EvalContext) (before : MachineState)
    (cfg : CFG) (pc : BlockId) (fuel depth : Nat)
    (left right destination dividend divisor : Nat)
    (found : cfg pc = some (canonicalBlock left right destination))
    (leftLookup : before.lookupValue ⟨left⟩ = some (.int 64 (dividend : Int)))
    (rightLookup : before.lookupValue ⟨right⟩ = some (.int 64 (divisor : Int)))
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩)
      [⟨destination⟩] 1 = .ok [.U64])
    (returns : ctx.functionReturnTypes = some [.U64])
    (fresh : SSAFreshFrames.FreshState before)
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    Sem.run (stepNWithContext ctx (fuel + 1) depth cfg pc [] .abort) before =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((dividend / divisor : Nat) : Int)],
        targetAfter before destination (dividend / divisor)) := by
  rw [GenericCoro.Prefix.stepNWithContext_succ_layer,
    AYUnaryReplay.evalLayer_return _ ctx depth cfg pc [] .abort
      (canonicalBlock left right destination) found [⟨destination⟩] rfl,
    Sem.run_bind, target_no_parameters, Except.bind]
  change Sem.run (do
    GenericCoro.Prefix.evalBody _ ctx depth .abort
      [(.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩, [⟨destination⟩])]
    AYUnaryReplay.checkedReturnValues ctx [⟨destination⟩]) before = _
  exact target_body_return ctx before _ depth left right destination dividend divisor
    leftLookup rightLookup declarations returns fresh leftRange rightRange

def sourceSignature : SemR.FuncTy :=
  { params := [.int .u64, .int .u64], returns := [.int .u64], vararg := false }

def sourceEntry (function : SemR.Func) (block : SemR.Block)
    (dividend divisor depth : Nat) : SemR.Core :=
  { fn := function, sig := sourceSignature, block := block, pc := 0,
    env := [(1, .int .u64 divisor), (0, .int .u64 dividend)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := .empty }

theorem source_start (m : SemR.Module) (fid : Nat) (function : SemR.Func)
    (block : SemR.Block) (dividend divisor depth : Nat)
    (functionFound : m.functions.find? (fun f => f.id == fid) = some function)
    (signature : SemR.nth? m.funcTys function.ty = some sourceSignature)
    (blockFound : SemR.findBlock function.blocks function.entry = some block)
    (params : block.params = [(0, .int .u64), (1, .int .u64)])
    (targetLayout : m.executableTarget = true)
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    SemR.start m fid [.int .u64 dividend, .int .u64 divisor] depth =
      .ok (sourceEntry function block dividend divisor depth) := by
  have nonempty : function.blocks.isEmpty = false := by
    cases blocks : function.blocks with
    | nil => simp [blocks, SemR.findBlock] at blockFound
    | cons first rest => rfl
  simp [SemR.start, functionFound, signature, sourceSignature, nonempty,
    targetLayout, SemR.checkSig, SemR.rejectPoison, SemR.Val.ty, SemR.Ty.beq,
    SemR.IntTy.code, SemR.expectTy, SemR.IntTy.bits, SemR.modulus, leftRange,
    rightRange, blockFound, params, SemR.bindParams, sourceEntry,
    bind, SemR.R.bind, pure]

theorem source_function (m : SemR.Module) (fid : Nat) (function : SemR.Func)
    (block : SemR.Block) (dividend divisor extra depth : Nat)
    (functionFound : m.functions.find? (fun f => f.id == fid) = some function)
    (signature : SemR.nth? m.funcTys function.ty = some sourceSignature)
    (blockFound : SemR.findBlock function.blocks function.entry = some block)
    (params : block.params = [(0, .int .u64), (1, .int .u64)])
    (body : block.body = [divisionNode 0 1 2, returnNode 2])
    (targetLayout : m.executableTarget = true)
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    SemR.runFunction m fid [.int .u64 dividend, .int .u64 divisor] (extra + 2) depth =
      if divisor = 0 then .ub "unsigned division by zero"
      else .ret [.int .u64 (dividend / divisor)] := by
  rw [SemR.runFunction, source_start m fid function block dividend divisor depth
    functionFound signature blockFound params targetLayout leftRange rightRange]
  exact source_division_return m (sourceEntry function block dividend divisor depth)
    0 1 2 dividend divisor extra body rfl rfl rfl rfl rfl leftRange rightRange

open TrustIr in
def entryBlock : BasicBlock :=
  { canonicalBlock 0 1 2 with params := [(⟨0⟩, .U64), (⟨1⟩, .U64)] }

open TrustIr in
def targetEntry (dividend divisor : Nat) : MachineState :=
  { MachineState.empty with
    locals := (ValueMap.empty.set ⟨0⟩ (.int 64 (dividend : Int))).set
      ⟨1⟩ (.int 64 (divisor : Int)), nextValueId := 2 }

open TrustIr in
theorem target_parameter_binding (ctx : EvalContext) (dividend divisor : Nat) :
    Sem.run (AYUnaryReplay.bindParameters ctx (ctx.resolveBlock entryBlock)
      [.int 64 (dividend : Int), .int 64 (divisor : Int)]) MachineState.empty =
        .ok ((), targetEntry dividend divisor) := by
  simp [AYUnaryReplay.bindParameters, entryBlock, canonicalBlock, EvalContext.resolveBlock,
    EvalContext.resolveDrop, checkFunctionItemValues, List.forM_cons, List.forM_nil,
    checkFunctionItemLanes, checkFunctionItemLayer, Value.depth, Value.depthSpec,
    Value.isUninit, scalar_has_no_function_items, bindBlockParamsChecked,
    bindBlockParams, checkSSACharValues, checkSSACharValue, targetEntry, MachineState.empty,
    Sem.run, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.get,
    StateT.set, StateT.lift, Sem.getState, Sem.setState, Sem.fromMemoryExcept,
    bind, pure, Except.bind, Except.pure, Functor.map, Except.map]

open TrustIr in
theorem target_entry_fresh (dividend divisor : Nat) :
    SSAFreshFrames.FreshState (targetEntry dividend divisor) :=
  SSAFreshFrames.bindBlockParamsChecked_preserves_fresh
    [(⟨0⟩, .U64), (⟨1⟩, .U64)] [.int 64 (dividend : Int), .int 64 (divisor : Int)]
    MachineState.empty (targetEntry dividend divisor)
    (SSAFreshFrames.cleared_fresh MachineState.empty) rfl

open TrustIr in
theorem target_entry_block (ctx : EvalContext) (cfg : CFG) (pc : BlockId)
    (fuel depth dividend divisor : Nat) (found : cfg pc = some entryBlock)
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩)
      [⟨2⟩] 1 = .ok [.U64])
    (returns : ctx.functionReturnTypes = some [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    Sem.run (stepNWithContext ctx (fuel + 1) depth cfg pc
      [.int 64 (dividend : Int), .int 64 (divisor : Int)] .abort) MachineState.empty =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((dividend / divisor : Nat) : Int)],
        targetAfter (targetEntry dividend divisor) 2 (dividend / divisor)) := by
  rw [GenericCoro.Prefix.stepNWithContext_succ_layer,
    AYUnaryReplay.evalLayer_return _ ctx depth cfg pc _ .abort entryBlock found [⟨2⟩] rfl,
    Sem.run_bind, target_parameter_binding, Except.bind]
  change Sem.run (do
    GenericCoro.Prefix.evalBody _ ctx depth .abort [(.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩, [⟨2⟩])]
    AYUnaryReplay.checkedReturnValues ctx [⟨2⟩]) (targetEntry dividend divisor) = _
  exact target_body_return ctx (targetEntry dividend divisor) _ depth 0 1 2 dividend divisor
    rfl rfl declarations returns (target_entry_fresh dividend divisor) leftRange rightRange

open TrustIr in
private theorem scalar_argument_check (ctx : EvalContext) (left right : Int) :
    checkFunctionItemValues ctx [.U64, .U64] [.int 64 left, .int 64 right] = .ok () := by
  simp [checkFunctionItemValues, List.forM_cons, List.forM_nil, checkFunctionItemLanes,
    checkFunctionItemLayer, Value.depth, Value.depthSpec, Value.isUninit,
    scalar_has_no_function_items, bind, Except.bind, pure, Except.pure]

open TrustIr in
theorem target_entry_checks (ctx : EvalContext) (fid : FuncId) (function : EvalFunction)
    (before : MachineState) (dividend divisor : Nat)
    (found : ctx.functions fid = some function)
    (params : function.body.paramTys = [.U64, .U64]) (abi : function.body.abi = none) :
    Sem.run (AYUnaryReplay.entryChecks ctx fid
      [.int 64 (dividend : Int), .int 64 (divisor : Int)]) before = .ok (function, before) := by
  simp [AYUnaryReplay.entryChecks, found, params, abi, requireUntypedAbi,
    checkCallArity, Sem.rejectPoisonValues, Value.isPoison, scalar_argument_check,
    Sem.run, StateT.run, StateT.bind, StateT.pure, StateT.lift, Sem.fromMemoryExcept,
    bind, pure, Except.bind, Except.pure]

open TrustIr in
theorem target_finish_value (ctx : EvalContext) (before after : MachineState) (returned : Int) :
    Sem.run (AYUnaryReplay.checkedFinishEntry ctx [.U64] .abort
      (fun _ => .ok ([.int 64 returned], after))) before = .ok ([.int 64 returned], after) := by
  simp [AYUnaryReplay.checkedFinishEntry, AYUnaryReplay.finishEntry, exitUnwinding,
    Sem.rejectPoisonValues, Value.isPoison, scalar_return_check, Sem.fromMemoryExcept,
    Sem.run, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.lift,
    bind, pure, Except.bind, Except.pure, Functor.map, Except.map]

open TrustIr in
theorem target_finish_error (ctx : EvalContext) (before : MachineState) (error : SemError) :
    Sem.run (AYUnaryReplay.checkedFinishEntry ctx [.U64] .abort
      (fun _ => .error error)) before = .error error := rfl

open TrustIr in
theorem target_function (ctx : EvalContext) (fid : FuncId) (function : EvalFunction)
    (dividend divisor fuel : Nat)
    (functionFound : ctx.functions fid = some function)
    (params : function.body.paramTys = [.U64, .U64])
    (returns : function.body.returnTys = [.U64]) (abi : function.body.abi = none)
    (found : function.cfg function.entryBlock = some entryBlock)
    (declarations : (ctx.forFunction function).instructionResultTypes
      (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩) [⟨2⟩] 1 = .ok [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    Sem.run (evalFunctionInContext ctx fid [.int 64 (dividend : Int), .int 64 (divisor : Int)]
      (fuel + 1) .abort) MachineState.empty =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((dividend / divisor : Nat) : Int)],
        targetAfter (targetEntry dividend divisor) 2 (dividend / divisor)) := by
  have body := target_entry_block (ctx.forFunction function) function.cfg function.entryBlock
    fuel ctx.maxCallDepth dividend divisor found declarations (by simp [EvalContext.forFunction, returns])
    leftRange rightRange
  rw [AYUnaryReplay.entry_decomposition, Sem.run_bind,
    target_entry_checks ctx fid function MachineState.empty dividend divisor functionFound params abi,
    Except.bind]
  dsimp only
  rw [AYUnaryReplay.checkedFinishEntry_congr ctx function.body.returnTys .abort _
    (fun _ => if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((dividend / divisor : Nat) : Int)],
        targetAfter (targetEntry dividend divisor) 2 (dividend / divisor))) MachineState.empty body]
  rw [returns]
  by_cases zero : divisor = 0
  · simpa only [zero, if_true] using
      target_finish_error ctx MachineState.empty (.ub "unsigned division by zero")
  · simpa only [zero, if_false] using target_finish_value ctx MachineState.empty
      (targetAfter (targetEntry dividend divisor) 2 (dividend / divisor))
      ((dividend / divisor : Nat) : Int)

open TrustIr in
/-- A complete two-parameter function, including both actual entry paths and
return. The source budgets count instructions; canonical budgets count blocks.
Every canonical U64 argument is covered and the return postcondition is free.
The exact SSA interface here is 0/1 -> 2, not an assumed renaming theorem. -/
theorem function_wp_iff (m : SemR.Module) (fid : Nat) (sourceFunction : SemR.Func)
    (sourceBlock : SemR.Block) (ctx : EvalContext) (targetFunction : EvalFunction)
    (dividend divisor sourceExtra sourceDepth targetFuel : Nat)
    (sourceFound : m.functions.find? (fun f => f.id == fid) = some sourceFunction)
    (sourceSig : SemR.nth? m.funcTys sourceFunction.ty = some sourceSignature)
    (sourceEntryBlock : SemR.findBlock sourceFunction.blocks sourceFunction.entry = some sourceBlock)
    (sourceParams : sourceBlock.params = [(0, .int .u64), (1, .int .u64)])
    (sourceBody : sourceBlock.body = [divisionNode 0 1 2, returnNode 2])
    (sourceLayout : m.executableTarget = true)
    (targetFound : ctx.functions ⟨fid⟩ = some targetFunction)
    (targetParams : targetFunction.body.paramTys = [.U64, .U64])
    (targetReturns : targetFunction.body.returnTys = [.U64])
    (targetAbi : targetFunction.body.abi = none)
    (targetEntryBlock : targetFunction.cfg targetFunction.entryBlock = some entryBlock)
    (targetDeclarations : (ctx.forFunction targetFunction).instructionResultTypes
      (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩) [⟨2⟩] 1 = .ok [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64)
    (post : List SemR.Val → List TrustIr.Value → Prop) :
    (∃ sourceReturned targetReturned after,
      SemR.runFunction m fid [.int .u64 dividend, .int .u64 divisor]
        (sourceExtra + 2) sourceDepth = .ret sourceReturned ∧
      Sem.run (evalFunctionInContext ctx ⟨fid⟩
        [.int 64 (dividend : Int), .int 64 (divisor : Int)] (targetFuel + 1) .abort)
        MachineState.empty = .ok (targetReturned, after) ∧
      post sourceReturned targetReturned) ↔
      divisor ≠ 0 ∧ post [.int .u64 (dividend / divisor)]
        [.int 64 ((dividend / divisor : Nat) : Int)] := by
  rw [source_function m fid sourceFunction sourceBlock dividend divisor sourceExtra sourceDepth
    sourceFound sourceSig sourceEntryBlock sourceParams sourceBody sourceLayout leftRange rightRange,
    SemR.CanonicalScalarReturn.target_function ctx ⟨fid⟩ targetFunction dividend divisor targetFuel
      targetFound targetParams targetReturns targetAbi targetEntryBlock targetDeclarations leftRange rightRange]
  by_cases zero : divisor = 0 <;> simp [zero]

end SemR.CanonicalScalarReturn
