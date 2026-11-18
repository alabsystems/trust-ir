-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0
import SemRDeclaredDivisionReturn
import SemRStructLayoutChecks

namespace SemR.CanonicalDeclaredDivision.Checks
open SemR.CanonicalScalarStep SemR.CanonicalScalarReturn

private def sourceBlock (destination returned : Nat) : SemR.Block :=
  { id := 0, params := [(0, .int .u64)],
    body := [constantNode, divisionNode 1 0 destination, returnNode returned] }

private def sourceFunction (destination returned : Nat) : SemR.Func :=
  { id := 0, ty := 0, entry := 0, blocks := [sourceBlock destination returned] }

private def sourceModule (destination returned : Nat) : SemR.Module :=
  { funcTys := [signature], enums := [],
    functions := [sourceFunction destination returned],
    structs := [CanonicalStructLayout.Checks.pair] }

private def targetBlock (destination returned : Nat) : TrustIr.BasicBlock :=
  { entryBlock with
    bodyResultDests := [[⟨1⟩], [⟨destination⟩]]
    terminator := .Return [⟨returned⟩] }

private def targetFunction (destination returned : Nat) : TrustIr.EvalFunction :=
  { sourceId := some ⟨0⟩, body := { paramTys := [.U64], returnTys := [.U64] },
    cfg := fun id => if id.index == 0 then some (targetBlock destination returned) else none,
    entryBlock := ⟨0⟩,
    localTypes := some (fun id =>
      if id.index == 0 || id.index == 1 || id.index == destination then some .U64 else none) }

private def context (destination returned : Nat) : TrustIr.EvalContext :=
  { TrustIr.EvalContext.empty with
    functions := fun id =>
      if id.index == 0 then some (targetFunction destination returned) else none }

private theorem declarations (destination returned : Nat) :
    let ctx := (context destination returned).forFunction (targetFunction destination returned)
    ctx.instructionResultTypes (.Const .U64 (.int 1)) [⟨1⟩] 1 = .ok [.U64] ∧
    ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩)
      [⟨destination⟩] 1 = .ok [.U64] := by
  simp [context, targetFunction, TrustIr.EvalContext.forFunction,
    TrustIr.EvalContext.instructionResultTypes, TrustIr.ssaInstructionResultTypes,
    TrustIr.localResultTypes, TrustIr.ssaResultSourceType, TrustIr.closureTyEq,
    List.mapM, List.mapM.loop, bind, pure, Except.bind, Except.pure]

private theorem source_value (divisor extra depth : Nat) (range : divisor < 2 ^ 64) :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 divisor] (extra + 3) depth =
      if divisor = 0 then .ub "unsigned division by zero"
      else .ret [.int .u64 (1 / divisor)] :=
  CanonicalDeclaredDivision.source_function (sourceModule 2 2) 0 (sourceFunction 2 2)
    (sourceBlock 2 2) divisor extra depth rfl rfl rfl rfl rfl rfl range

private theorem target_value (divisor fuel : Nat) (range : divisor < 2 ^ 64) :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 (divisor : Int)] (fuel + 1) .abort) TrustIr.MachineState.empty =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((1 / divisor : Nat) : Int)],
        targetAfter (targetConstant divisor) 2 (1 / divisor)) :=
  CanonicalDeclaredDivision.target_function (context 2 2) ⟨0⟩ (targetFunction 2 2)
    divisor fuel rfl rfl rfl rfl rfl (declarations 2 2).1 (declarations 2 2).2 range

theorem complete_one_argument_entry_return :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 1] 3 0 = .ret [.int .u64 1] ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩ [.int 64 1] 1 .abort)
      TrustIr.MachineState.empty =
        .ok ([.int 64 1], targetAfter (targetConstant 1) 2 1) :=
  ⟨source_value 1 0 0 (by decide), target_value 1 0 (by decide)⟩

theorem full_u64_maximum_is_an_actual_argument :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 18446744073709551615] 3 0 =
      .ret [.int .u64 0] ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 18446744073709551615] 1 .abort) TrustIr.MachineState.empty =
        .ok ([.int 64 0], targetAfter (targetConstant 18446744073709551615) 2 0) :=
  ⟨source_value _ 0 0 (by decide), target_value _ 0 (by decide)⟩

theorem true_post_still_owes_zero_domain :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 0] 3 0 =
      .ub "unsigned division by zero" ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 0] 1 .abort) TrustIr.MachineState.empty =
        .error (.ub "unsigned division by zero") :=
  ⟨source_value 0 0 0 (by decide), target_value 0 0 (by decide)⟩

theorem wrong_source_return_observes_original_argument :
    SemR.runFunction (sourceModule 2 0) 0 [.int .u64 2] 3 0 = .ret [.int .u64 2] := rfl

theorem wrong_source_destination_refuses :
    SemR.runFunction (sourceModule 3 2) 0 [.int .u64 2] 3 0 =
      .typeError "MissingValue: value is not defined" := rfl

theorem discarded_quotient_still_owes_domain :
    SemR.runFunction (sourceModule 2 0) 0 [.int .u64 0] 3 0 =
      .ub "unsigned division by zero" := rfl

theorem no_extra_constant_parameter_is_invented :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 1, .int .u64 2] 3 0 =
      .typeError "SignatureMismatch: arity mismatch" := rfl

theorem source_instruction_budget_is_owed :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 1] 2 0 = .outOfFuel := rfl

theorem original_pair_geometry_remains_in_the_function_module :
    CanonicalStructLayout.query (sourceModule 2 2) .execution 0 = .ok {
      size := 8, align := some 8,
      fields := [{ ty := .I64, offset := 0, size := 8, align := 8 }] } :=
  CanonicalStructLayout.Checks.original_pair_execution_geometry


private theorem canonical_block_control (destination returned : Nat) :
    let callee := (context destination returned).forFunction (targetFunction destination returned)
    TrustIr.Sem.run (TrustIr.stepNWithContext callee 1 0
      (targetFunction destination returned).cfg ⟨0⟩ [.int 64 2] .abort)
      TrustIr.MachineState.empty =
        TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedReturnValues callee [⟨returned⟩])
          (targetAfter (targetConstant 2) destination 0) := by
  dsimp only
  rw [TrustIr.GenericCoro.Prefix.stepNWithContext_succ_layer,
    TrustIr.AYUnaryReplay.evalLayer_return _ _ 0 _ ⟨0⟩ _ .abort
      (targetBlock destination returned) rfl [⟨returned⟩] rfl,
    TrustIr.Sem.run_bind]
  rw [show TrustIr.Sem.run (TrustIr.AYUnaryReplay.bindParameters
      ((context destination returned).forFunction (targetFunction destination returned))
      (((context destination returned).forFunction (targetFunction destination returned)).resolveBlock
        (targetBlock destination returned)) [.int 64 2]) TrustIr.MachineState.empty =
        .ok ((), targetEntry 2) from target_parameter_binding _ 2, Except.bind]
  change TrustIr.Sem.run (do
    TrustIr.GenericCoro.Prefix.evalBody _ _ 0 .abort
      [(.Const .U64 (.int 1), [⟨1⟩]), (.BinOp .UDiv .U64 ⟨1⟩ ⟨0⟩, [⟨destination⟩])]
    TrustIr.AYUnaryReplay.checkedReturnValues _ [⟨returned⟩]) (targetEntry 2) = _
  rw [TrustIr.GenericCoro.Prefix.evalBody_cons]
  simp only [TrustIr.Sem.run_bind,
    target_constant_step _ _ 0 2 (declarations destination returned).1, Except.bind]
  rw [target_body_singleton,
    target_step_raw _ _ 0 .abort (targetConstant 2) 1 0 destination 1 2
      rfl rfl (declarations destination returned).2 (by decide) (by decide)]
  rfl

private theorem canonical_entry_control (destination returned : Nat) :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context destination returned) ⟨0⟩
      [.int 64 2] 1 .abort) TrustIr.MachineState.empty =
    TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedFinishEntry (context destination returned)
      [.U64] .abort (fun _ => TrustIr.Sem.run
        (TrustIr.AYUnaryReplay.checkedReturnValues
          ((context destination returned).forFunction (targetFunction destination returned)) [⟨returned⟩])
        (targetAfter (targetConstant 2) destination 0))) TrustIr.MachineState.empty := by
  rw [TrustIr.AYUnaryReplay.entry_decomposition, TrustIr.Sem.run_bind,
    show TrustIr.Sem.run (TrustIr.AYUnaryReplay.entryChecks (context destination returned) ⟨0⟩
      [.int 64 2]) TrustIr.MachineState.empty =
        .ok (targetFunction destination returned, TrustIr.MachineState.empty) from
      target_entry_checks _ _ _ _ 2 rfl rfl rfl, Except.bind]
  dsimp only
  exact TrustIr.AYUnaryReplay.checkedFinishEntry_congr _ _ .abort _ _ _
    (canonical_block_control destination returned)

theorem canonical_wrong_return_observes_original_argument :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 0) ⟨0⟩ [.int 64 2] 1 .abort)
      TrustIr.MachineState.empty = .ok ([.int 64 2], targetAfter (targetConstant 2) 2 0) := by
  rw [canonical_entry_control,
    target_return _ (targetAfter (targetConstant 2) 2 0) 0 2 rfl rfl]
  exact target_finish_value _ _ _ 2

theorem canonical_wrong_destination_refuses :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 3 2) ⟨0⟩ [.int 64 2] 1 .abort)
      TrustIr.MachineState.empty = .error (.typeError
        (trustIrStringBuild s!"undefined SSA value: {repr (⟨2⟩ : TrustIr.ValueId)}")) := by
  rw [canonical_entry_control]
  have missing : TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedReturnValues
      ((context 3 2).forFunction (targetFunction 3 2)) [⟨2⟩])
      (targetAfter (targetConstant 2) 3 0) = .error (.typeError
        (trustIrStringBuild s!"undefined SSA value: {repr (⟨2⟩ : TrustIr.ValueId)}")) := by
    simp [TrustIr.AYUnaryReplay.checkedReturnValues, TrustIr.AYUnaryReplay.returnValues,
      List.mapM, List.mapM.loop, targetAfter, targetConstant, targetEntry,
      TrustIr.MachineState.bindValue, TrustIr.MachineState.lookupValue, TrustIr.MachineState.empty,
      TrustIr.ValueMap.get, TrustIr.ValueMap.set, TrustIr.ValueMap.empty,
      TrustIr.Sem.lookupValue, TrustIr.Sem.getState, TrustIr.Sem.throwTypeError,
      TrustIr.Sem.run, StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.map,
      StateT.lift, bind, pure, Except.bind, Except.pure, Except.map, Functor.map,
      throw, throwThe, MonadExceptOf.throw, TrustIr.CompilerCompat.Strings.appendModern_eq]
  rw [missing]
  exact target_finish_error _ _ _

theorem arbitrary_post_is_checked_not_assumed (divisor : Nat) (range : divisor < 2 ^ 64)
    (post : List SemR.Val → List TrustIr.Value → Prop) :
    (∃ left right after,
      SemR.runFunction (sourceModule 2 2) 0 [.int .u64 divisor] 3 0 = .ret left ∧
      TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
        [.int 64 (divisor : Int)] 1 .abort) TrustIr.MachineState.empty = .ok (right, after) ∧
      post left right) ↔
      divisor ≠ 0 ∧ post [.int .u64 (1 / divisor)] [.int 64 ((1 / divisor : Nat) : Int)] :=
  function_wp_iff (sourceModule 2 2) 0 (sourceFunction 2 2) (sourceBlock 2 2)
    (context 2 2) (targetFunction 2 2) divisor 0 0 0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (declarations 2 2).1 (declarations 2 2).2 range post

theorem false_post_has_no_success_witness :
    ¬ ∃ left right after,
      SemR.runFunction (sourceModule 2 2) 0 [.int .u64 2] 3 0 = .ret left ∧
      TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
        [.int 64 2] 1 .abort) TrustIr.MachineState.empty = .ok (right, after) ∧
      left = [.int .u64 1] := by
  intro claimed
  have checked := (arbitrary_post_is_checked_not_assumed 2 (by decide)
    (fun left _ => left = [.int .u64 1])).mp claimed
  simpa using checked.2

end SemR.CanonicalDeclaredDivision.Checks
