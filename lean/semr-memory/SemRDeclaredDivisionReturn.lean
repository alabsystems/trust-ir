-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemRScalarReturn
import SemRUnsignedSelect
import SemRStructLayout

/-! The existing one-argument declared-entry division body, without replacing
its constant with an extra argument. The module, including all original
declarations, is retained. This component proves actual execution and return;
it does not grant a guarded-consumer, source/ABI or compiler proof grade.
-/

namespace SemR.CanonicalDeclaredDivision
open SemR.CanonicalScalarStep SemR.CanonicalScalarReturn

def signature : SemR.FuncTy :=
  { params := [.int .u64], returns := [.int .u64], vararg := false }

def constantNode : SemR.Node := SemRUnsignedSelect.constUInt 1 .u64 1

def sourceEntry (function : SemR.Func) (block : SemR.Block)
    (divisor depth : Nat) : SemR.Core :=
  { fn := function, sig := signature, block := block, pc := 0,
    env := [(0, .int .u64 divisor)], depth := depth,
    stack := [], openFrames := [], nextFrame := 0, mem := .empty }

theorem source_start (m : SemR.Module) (fid : Nat) (function : SemR.Func)
    (block : SemR.Block) (divisor depth : Nat)
    (functionFound : m.functions.find? (fun f => f.id == fid) = some function)
    (declared : SemR.nth? m.funcTys function.ty = some signature)
    (blockFound : SemR.findBlock function.blocks function.entry = some block)
    (params : block.params = [(0, .int .u64)])
    (targetLayout : m.executableTarget = true) (range : divisor < 2 ^ 64) :
    SemR.start m fid [.int .u64 divisor] depth =
      .ok (sourceEntry function block divisor depth) := by
  have nonempty : function.blocks.isEmpty = false := by
    cases blocks : function.blocks with
    | nil => simp [blocks, SemR.findBlock] at blockFound
    | cons first rest => rfl
  simp [SemR.start, functionFound, declared, signature, nonempty,
    targetLayout, SemR.checkSig, SemR.rejectPoison, SemR.Val.ty, SemR.Ty.beq,
    SemR.IntTy.code, SemR.expectTy, SemR.IntTy.bits, SemR.modulus, range,
    blockFound, params, SemR.bindParams, sourceEntry, bind, SemR.R.bind, pure]

theorem source_function (m : SemR.Module) (fid : Nat) (function : SemR.Func)
    (block : SemR.Block) (divisor extra depth : Nat)
    (functionFound : m.functions.find? (fun f => f.id == fid) = some function)
    (declared : SemR.nth? m.funcTys function.ty = some signature)
    (blockFound : SemR.findBlock function.blocks function.entry = some block)
    (params : block.params = [(0, .int .u64)])
    (body : block.body = [constantNode, divisionNode 1 0 2, returnNode 2])
    (targetLayout : m.executableTarget = true) (range : divisor < 2 ^ 64) :
    SemR.runFunction m fid [.int .u64 divisor] (extra + 3) depth =
      if divisor = 0 then .ub "unsigned division by zero"
      else .ret [.int .u64 (1 / divisor)] := by
  rw [SemR.runFunction, source_start m fid function block divisor depth
    functionFound declared blockFound params targetLayout range]
  let before := sourceEntry function block divisor depth
  let middle := SemRUnsignedSelect.writeUInt before 1 .u64 1
  have first : SemR.stepCore m before = .cont middle := by
    have step := SemRUnsignedSelect.constUInt_step m before 1 .u64 1
    have atNode : SemR.nth? before.block.body before.pc = some constantNode := by
      simp [before, sourceEntry, body, SemR.nth?]
    simpa [middle, constantNode, SemR.modulus, SemR.IntTy.bits] using
      SemR.step_sound m before _ (SemRUnsignedSelect.at_pc m before _ constantNode atNode step)
  have second := SemR.CanonicalScalarStep.source_step m middle 1 0 2 1 divisor
    (by simp [middle, before, SemRUnsignedSelect.writeUInt, sourceEntry,
      SemR.next, body, SemR.nth?])
    (by rfl) (by rfl) (by decide) range
  have third := source_return_step m (sourceAfter middle 2 (1 / divisor)) 2 (1 / divisor)
    (by simp [sourceAfter, middle, before, SemRUnsignedSelect.writeUInt,
      sourceEntry, SemR.next, body, SemR.nth?])
    (by simp [source_after_lookup]) rfl rfl
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide : 1 < 2 ^ 64))
  change SemR.run m (extra + 3) before = _
  by_cases zero : divisor = 0 <;> simp only [SemR.run, first, second, third, zero, if_true, if_false]

open TrustIr in
def entryBlock : BasicBlock :=
  { params := [(⟨0⟩, .U64)]
    body := [.Const .U64 (.int 1), .BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩]
    bodyResultDests := [[⟨1⟩], [⟨2⟩]]
    terminator := .Return [⟨2⟩] }

open TrustIr in
def targetEntry (divisor : Nat) : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set ⟨0⟩ (.int 64 (divisor : Int)), nextValueId := 1 }

open TrustIr in
def targetConstant (divisor : Nat) : MachineState :=
  { targetEntry divisor with
    locals := (targetEntry divisor).locals.set ⟨1⟩ (.int 64 1), nextValueId := 2 }

open TrustIr in
theorem target_parameter_binding (ctx : EvalContext) (divisor : Nat) :
    Sem.run (AYUnaryReplay.bindParameters ctx (ctx.resolveBlock entryBlock)
      [.int 64 (divisor : Int)]) MachineState.empty = .ok ((), targetEntry divisor) := by
  simp [AYUnaryReplay.bindParameters, entryBlock, EvalContext.resolveBlock,
    EvalContext.resolveDrop, checkFunctionItemValues, List.forM_cons, List.forM_nil,
    checkFunctionItemLanes, checkFunctionItemLayer, Value.depth, Value.depthSpec,
    Value.isUninit, FunctionItemPresence.Prepared.hasFnItem_u64,
    bindBlockParamsChecked, bindBlockParams, checkSSACharValues, checkSSACharValue,
    targetEntry, MachineState.empty, Sem.run, StateT.run, StateT.bind, StateT.pure,
    StateT.map, StateT.get, StateT.set, StateT.lift, Sem.getState, Sem.setState,
    Sem.fromMemoryExcept, bind, pure, Except.bind, Except.pure, Functor.map, Except.map]

open TrustIr in
theorem target_entry_fresh (divisor : Nat) :
    SSAFreshFrames.FreshState (targetEntry divisor) :=
  SSAFreshFrames.bindBlockParamsChecked_preserves_fresh [(⟨0⟩, .U64)]
    [.int 64 (divisor : Int)] MachineState.empty (targetEntry divisor)
    (SSAFreshFrames.cleared_fresh MachineState.empty) rfl

open TrustIr in
theorem target_constant_fresh (divisor : Nat) :
    SSAFreshFrames.FreshState (targetConstant divisor) :=
  SSAFreshFrames.set_fresh (targetEntry divisor) ⟨1⟩ (.int 64 1) 2
    (target_entry_fresh divisor) (by simp [targetEntry]) (by decide)

open TrustIr in
theorem target_constant_step (ctx : EvalContext) (recurse : GenericCoro.Prefix.Recurse)
    (depth divisor : Nat)
    (declared : ctx.instructionResultTypes (.Const .U64 (.int 1)) [⟨1⟩] 1 = .ok [.U64]) :
    Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth .abort
      (.Const .U64 (.int 1), [⟨1⟩])) (targetEntry divisor) =
        .ok (.yield (), targetConstant divisor) := by
  simp [GenericCoro.Prefix.evalBodyStep, stepInstWithContext, stepInst,
    Constant.hasSymbolAddr, constValueAtChecked, constPointerFormsSupported,
    constValueAt, Ty.isInteger, Ty.bitWidthFor, Ty.bitWidth, Value.intAt,
    EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
    declared, checkSSACharValues, checkSSACharValue, bindInstrResultDests,
    bindResultDests, MachineState.bindValue, MachineState.lookupValue,
    ValueMap.get, ValueMap.set, targetEntry, targetConstant, MachineState.empty,
    Sem.run_bind, Sem.run_pure, Sem.run, StateT.run, StateT.bind, StateT.pure,
    StateT.map, StateT.get, StateT.set, StateT.lift, bind, pure, Functor.map,
    Except.bind, Except.pure, Except.map, Sem.getState, Sem.setState, Sem.bindFresh,
    Sem.lookupValue, Ty.bitWidthAtModel, Ty.bitWidthAtPointerBits,
    truncateUnsigned]
  cases ctx.byteModel <;> simp_all [Ty.bitWidthAtModel, Ty.bitWidthAtPointerBits,
    truncateUnsigned, ValueMap.set]
  all_goals
    funext id
    by_cases same : id = ⟨1⟩ <;> simp [ValueMap.set, same]
    all_goals intro yes no; exact (no yes).elim

open TrustIr in
theorem target_entry_block (ctx : EvalContext) (cfg : CFG) (pc : BlockId)
    (fuel depth divisor : Nat) (found : cfg pc = some entryBlock)
    (constantDeclaration : ctx.instructionResultTypes (.Const .U64 (.int 1))
      [⟨1⟩] 1 = .ok [.U64])
    (divisionDeclaration : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩)
      [⟨2⟩] 1 = .ok [.U64])
    (returns : ctx.functionReturnTypes = some [.U64]) (range : divisor < 2 ^ 64) :
    Sem.run (stepNWithContext ctx (fuel + 1) depth cfg pc [.int 64 (divisor : Int)] .abort)
      MachineState.empty =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((1 / divisor : Nat) : Int)],
        targetAfter (targetConstant divisor) 2 (1 / divisor)) := by
  rw [GenericCoro.Prefix.stepNWithContext_succ_layer,
    AYUnaryReplay.evalLayer_return _ ctx depth cfg pc _ .abort entryBlock found [⟨2⟩] rfl,
    Sem.run_bind, target_parameter_binding, Except.bind]
  change Sem.run (do
    GenericCoro.Prefix.evalBody _ ctx depth .abort
      [(.Const .U64 (.int 1), [⟨1⟩]), (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩, [⟨2⟩])]
    AYUnaryReplay.checkedReturnValues ctx [⟨2⟩]) (targetEntry divisor) = _
  rw [GenericCoro.Prefix.evalBody_cons]
  simp only [Sem.run_bind, target_constant_step ctx _ depth divisor constantDeclaration, Except.bind]
  exact target_body_return ctx (targetConstant divisor) _ depth 1 0 2 1 divisor
    rfl rfl divisionDeclaration returns (target_constant_fresh divisor) (by decide) range

open TrustIr in
theorem target_entry_checks (ctx : EvalContext) (fid : FuncId) (function : EvalFunction)
    (before : MachineState) (divisor : Nat)
    (found : ctx.functions fid = some function)
    (params : function.body.paramTys = [.U64]) (abi : function.body.abi = none) :
    Sem.run (AYUnaryReplay.entryChecks ctx fid [.int 64 (divisor : Int)]) before =
      .ok (function, before) := by
  simp [AYUnaryReplay.entryChecks, found, params, abi, requireUntypedAbi,
    checkCallArity, Sem.rejectPoisonValues, Value.isPoison,
    checkFunctionItemValues, List.forM_cons, List.forM_nil,
    checkFunctionItemLanes, checkFunctionItemLayer, Value.depth, Value.depthSpec,
    Value.isUninit, FunctionItemPresence.Prepared.hasFnItem_u64,
    Sem.run, StateT.run, StateT.bind, StateT.pure, StateT.lift, Sem.fromMemoryExcept,
    bind, pure, Except.bind, Except.pure]

open TrustIr in
theorem target_function (ctx : EvalContext) (fid : FuncId) (function : EvalFunction)
    (divisor fuel : Nat) (functionFound : ctx.functions fid = some function)
    (params : function.body.paramTys = [.U64])
    (returns : function.body.returnTys = [.U64]) (abi : function.body.abi = none)
    (found : function.cfg function.entryBlock = some entryBlock)
    (constantDeclaration : (ctx.forFunction function).instructionResultTypes
      (.Const .U64 (.int 1)) [⟨1⟩] 1 = .ok [.U64])
    (divisionDeclaration : (ctx.forFunction function).instructionResultTypes
      (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩) [⟨2⟩] 1 = .ok [.U64])
    (range : divisor < 2 ^ 64) :
    Sem.run (evalFunctionInContext ctx fid [.int 64 (divisor : Int)]
      (fuel + 1) .abort) MachineState.empty =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((1 / divisor : Nat) : Int)],
        targetAfter (targetConstant divisor) 2 (1 / divisor)) := by
  have body := target_entry_block (ctx.forFunction function) function.cfg function.entryBlock
    fuel ctx.maxCallDepth divisor found constantDeclaration divisionDeclaration
    (by simp [EvalContext.forFunction, returns]) range
  rw [AYUnaryReplay.entry_decomposition, Sem.run_bind,
    target_entry_checks ctx fid function MachineState.empty divisor functionFound params abi,
    Except.bind]
  dsimp only
  rw [AYUnaryReplay.checkedFinishEntry_congr ctx function.body.returnTys .abort _
    (fun _ => if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((1 / divisor : Nat) : Int)],
        targetAfter (targetConstant divisor) 2 (1 / divisor))) MachineState.empty body]
  rw [returns]
  by_cases zero : divisor = 0
  · simpa only [zero, if_true] using
      target_finish_error ctx MachineState.empty (.ub "unsigned division by zero")
  · simpa only [zero, if_false] using target_finish_value ctx MachineState.empty
      (targetAfter (targetConstant divisor) 2 (1 / divisor)) ((1 / divisor : Nat) : Int)

open TrustIr in
/-- Actual one-argument entry, Const1, UDiv and return in both executors.
The complete source module is retained; no layout declaration is erased.
The postcondition is arbitrary, and nonzero is owed even for a true post.
The two genuine fuel units differ: source instructions and canonical blocks. -/
theorem function_wp_iff (m : SemR.Module) (fid : Nat) (sourceFunction : SemR.Func)
    (sourceBlock : SemR.Block) (ctx : EvalContext) (targetFunction : EvalFunction)
    (divisor sourceExtra sourceDepth targetFuel : Nat)
    (sourceFound : m.functions.find? (fun f => f.id == fid) = some sourceFunction)
    (sourceSig : SemR.nth? m.funcTys sourceFunction.ty = some signature)
    (sourceEntryBlock : SemR.findBlock sourceFunction.blocks sourceFunction.entry = some sourceBlock)
    (sourceParams : sourceBlock.params = [(0, .int .u64)])
    (sourceBody : sourceBlock.body = [constantNode, divisionNode 1 0 2, returnNode 2])
    (sourceLayout : m.executableTarget = true)
    (targetFound : ctx.functions ⟨fid⟩ = some targetFunction)
    (targetParams : targetFunction.body.paramTys = [.U64])
    (targetReturns : targetFunction.body.returnTys = [.U64])
    (targetAbi : targetFunction.body.abi = none)
    (targetEntryBlock : targetFunction.cfg targetFunction.entryBlock = some entryBlock)
    (constantDeclaration : (ctx.forFunction targetFunction).instructionResultTypes
      (.Const .U64 (.int 1)) [⟨1⟩] 1 = .ok [.U64])
    (divisionDeclaration : (ctx.forFunction targetFunction).instructionResultTypes
      (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩) [⟨2⟩] 1 = .ok [.U64])
    (range : divisor < 2 ^ 64) (post : List SemR.Val → List TrustIr.Value → Prop) :
    (∃ sourceReturned targetReturned after,
      SemR.runFunction m fid [.int .u64 divisor] (sourceExtra + 3) sourceDepth = .ret sourceReturned ∧
      Sem.run (evalFunctionInContext ctx ⟨fid⟩ [.int 64 (divisor : Int)]
        (targetFuel + 1) .abort) MachineState.empty = .ok (targetReturned, after) ∧
      post sourceReturned targetReturned) ↔
      divisor ≠ 0 ∧ post [.int .u64 (1 / divisor)] [.int 64 ((1 / divisor : Nat) : Int)] := by
  rw [source_function m fid sourceFunction sourceBlock divisor sourceExtra sourceDepth
    sourceFound sourceSig sourceEntryBlock sourceParams sourceBody sourceLayout range,
    SemR.CanonicalDeclaredDivision.target_function ctx ⟨fid⟩ targetFunction divisor targetFuel
      targetFound targetParams targetReturns targetAbi targetEntryBlock
      constantDeclaration divisionDeclaration range]
  by_cases zero : divisor = 0 <;> simp [zero]

end SemR.CanonicalDeclaredDivision
