-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemRScalarReturn

namespace SemR.CanonicalScalarReturn.Controls
open SemR.CanonicalScalarStep

private def sourceBlock (destination returned : Nat) : SemR.Block :=
  { id := 0, params := [(0, .int .u64), (1, .int .u64)],
    body := [divisionNode 0 1 destination, returnNode returned] }

private def sourceFunction (destination returned : Nat) : SemR.Func :=
  { id := 0, ty := 0, entry := 0, blocks := [sourceBlock destination returned] }

private def sourceModule (destination returned : Nat) : SemR.Module :=
  { funcTys := [sourceSignature], enums := [],
    functions := [sourceFunction destination returned] }

private def targetBlock (destination returned : Nat) : TrustIr.BasicBlock :=
  { entryBlock with
    body := [.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩],
    bodyResultDests := [[⟨destination⟩]], terminator := .Return [⟨returned⟩] }

private def targetFunction (destination returned : Nat) : TrustIr.EvalFunction :=
  { sourceId := some ⟨0⟩, body := { paramTys := [.U64, .U64], returnTys := [.U64] },
    cfg := fun id => if id.index == 0 then some (targetBlock destination returned) else none,
    entryBlock := ⟨0⟩,
    localTypes := some (fun id =>
      if id.index == 0 || id.index == 1 || id.index == destination then some .U64 else none) }

private def context (destination returned : Nat) : TrustIr.EvalContext :=
  { TrustIr.EvalContext.empty with
    functions := fun id =>
      if id.index == 0 then some (targetFunction destination returned) else none }

private theorem source_value (dividend divisor : Nat)
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 dividend, .int .u64 divisor] 2 0 =
      if divisor = 0 then .ub "unsigned division by zero"
      else .ret [.int .u64 (dividend / divisor)] :=
  source_function (sourceModule 2 2) 0 (sourceFunction 2 2) (sourceBlock 2 2)
    dividend divisor 0 0 rfl rfl rfl rfl rfl rfl leftRange rightRange

private theorem target_declarations (destination returned : Nat) :
    ((context destination returned).forFunction (targetFunction destination returned)).instructionResultTypes
      (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩) [⟨destination⟩] 1 = .ok [.U64] := by
  simp [context, targetFunction, TrustIr.EvalContext.forFunction,
    TrustIr.EvalContext.instructionResultTypes, TrustIr.ssaInstructionResultTypes,
    TrustIr.localResultTypes, TrustIr.ssaResultSourceType, TrustIr.closureTyEq,
    List.mapM, List.mapM.loop, bind, pure, Except.bind, Except.pure]

private theorem target_value (dividend divisor : Nat)
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 (dividend : Int), .int 64 (divisor : Int)] 1 .abort) TrustIr.MachineState.empty =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok ([.int 64 ((dividend / divisor : Nat) : Int)],
        targetAfter (targetEntry dividend divisor) 2 (dividend / divisor)) :=
  target_function (context 2 2) ⟨0⟩ (targetFunction 2 2) dividend divisor 0
    rfl rfl rfl rfl rfl (target_declarations 2 2) leftRange rightRange

theorem whole_source_entry_and_return :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 255, .int .u64 2] 2 0 =
      .ret [.int .u64 127] := source_value 255 2 (by decide) (by decide)

theorem whole_canonical_entry_and_return :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
      .ok ([.int 64 127], targetAfter (targetEntry 255 2) 2 127) :=
  target_value 255 2 (by decide) (by decide)

theorem both_entry_paths_reject_zero_division :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 17, .int .u64 0] 2 0 =
      .ub "unsigned division by zero" ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 17, .int 64 0] 1 .abort) TrustIr.MachineState.empty =
        .error (.ub "unsigned division by zero") :=
  ⟨source_value 17 0 (by decide) (by decide), target_value 17 0 (by decide) (by decide)⟩

theorem u64_maximum_quotient :
    SemR.runFunction (sourceModule 2 2) 0
      [.int .u64 18446744073709551615, .int .u64 2] 2 0 =
        .ret [.int .u64 9223372036854775807] ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 18446744073709551615, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
        .ok ([.int 64 9223372036854775807],
          targetAfter (targetEntry 18446744073709551615 2) 2 9223372036854775807) :=
  ⟨source_value 18446744073709551615 2 (by decide) (by decide),
    target_value 18446744073709551615 2 (by decide) (by decide)⟩

theorem source_wrong_return_returns_dividend :
    SemR.runFunction (sourceModule 2 0) 0 [.int .u64 255, .int .u64 2] 2 0 =
      .ret [.int .u64 255] := rfl

theorem source_wrong_destination_refuses :
    SemR.runFunction (sourceModule 3 2) 0 [.int .u64 255, .int .u64 2] 2 0 =
      .typeError "MissingValue: value is not defined" := rfl

theorem wrong_return_still_owes_divisor :
    SemR.runFunction (sourceModule 2 0) 0 [.int .u64 255, .int .u64 0] 2 0 =
      .ub "unsigned division by zero" := rfl

theorem source_missing_signature_refuses :
    SemR.runFunction { sourceModule 2 2 with funcTys := [] } 0
      [.int .u64 255, .int .u64 2] 2 0 =
        .typeError "SignatureMismatch: undefined signature" := rfl

theorem original_source_arity_is_checked :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 255] 2 0 =
      .typeError "SignatureMismatch: arity mismatch" := rfl

private theorem canonical_block_run (destination returned : Nat) :
    let callee := (context destination returned).forFunction (targetFunction destination returned)
    TrustIr.Sem.run (TrustIr.stepNWithContext callee 1 0
      (targetFunction destination returned).cfg ⟨0⟩ [.int 64 255, .int 64 2] .abort)
      TrustIr.MachineState.empty =
        TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedReturnValues callee [⟨returned⟩])
          (targetAfter (targetEntry 255 2) destination 127) := by
  dsimp only
  rw [TrustIr.GenericCoro.Prefix.stepNWithContext_succ_layer,
    TrustIr.AYUnaryReplay.evalLayer_return _ _ 0 _ ⟨0⟩ _ .abort
      (targetBlock destination returned) rfl [⟨returned⟩] rfl,
    TrustIr.Sem.run_bind]
  have bound := target_parameter_binding
    ((context destination returned).forFunction (targetFunction destination returned)) 255 2
  rw [show TrustIr.Sem.run (TrustIr.AYUnaryReplay.bindParameters
      ((context destination returned).forFunction (targetFunction destination returned))
      (((context destination returned).forFunction (targetFunction destination returned)).resolveBlock
        (targetBlock destination returned)) [.int 64 255, .int 64 2])
      TrustIr.MachineState.empty = .ok ((), targetEntry 255 2) from bound, Except.bind]
  change TrustIr.Sem.run (do
    TrustIr.GenericCoro.Prefix.evalBody _ _ 0 .abort
      [(.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩, [⟨destination⟩])]
    TrustIr.AYUnaryReplay.checkedReturnValues _ [⟨returned⟩]) (targetEntry 255 2) = _
  rw [TrustIr.Sem.run_bind, target_body_singleton,
    target_step_raw _ _ 0 .abort (targetEntry 255 2) 0 1 destination 255 2
      rfl rfl (target_declarations destination returned) (by decide) (by decide)]
  rfl

private theorem fixture_entry_checks (destination returned : Nat) :
    TrustIr.Sem.run (TrustIr.AYUnaryReplay.entryChecks (context destination returned) ⟨0⟩
      [.int 64 255, .int 64 2]) TrustIr.MachineState.empty =
        .ok (targetFunction destination returned, TrustIr.MachineState.empty) :=
  target_entry_checks (context destination returned) ⟨0⟩ (targetFunction destination returned)
    TrustIr.MachineState.empty 255 2 rfl rfl rfl

private theorem canonical_entry_control (destination returned : Nat) :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context destination returned) ⟨0⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
    TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedFinishEntry (context destination returned)
      [.U64] .abort (fun _ => TrustIr.Sem.run
        (TrustIr.AYUnaryReplay.checkedReturnValues
          ((context destination returned).forFunction (targetFunction destination returned)) [⟨returned⟩])
        (targetAfter (targetEntry 255 2) destination 127))) TrustIr.MachineState.empty := by
  rw [TrustIr.AYUnaryReplay.entry_decomposition, TrustIr.Sem.run_bind,
    fixture_entry_checks, Except.bind]
  dsimp only
  exact TrustIr.AYUnaryReplay.checkedFinishEntry_congr _ _ .abort _ _ _
    (canonical_block_run destination returned)

private theorem canonical_reader_values :
    TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedReturnValues
      ((context 2 0).forFunction (targetFunction 2 0)) [⟨0⟩])
      (targetAfter (targetEntry 255 2) 2 127) =
        .ok ([.int 64 255], targetAfter (targetEntry 255 2) 2 127) ∧
    TrustIr.Sem.run (TrustIr.AYUnaryReplay.checkedReturnValues
      ((context 3 2).forFunction (targetFunction 3 2)) [⟨2⟩])
      (targetAfter (targetEntry 255 2) 3 127) =
        .error (.typeError (trustIrStringBuild s!"undefined SSA value: {repr (⟨2⟩ : TrustIr.ValueId)}")) := by
  constructor
  · exact target_return _ _ 0 255 rfl rfl
  · simp [TrustIr.AYUnaryReplay.checkedReturnValues, TrustIr.AYUnaryReplay.returnValues,
      List.mapM, List.mapM.loop, targetAfter, targetEntry, TrustIr.MachineState.bindValue,
      TrustIr.MachineState.lookupValue, TrustIr.MachineState.empty,
      TrustIr.ValueMap.get, TrustIr.ValueMap.set, TrustIr.ValueMap.empty,
      TrustIr.Sem.lookupValue, TrustIr.Sem.getState, TrustIr.Sem.throwTypeError,
      TrustIr.Sem.run, StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.map,
      StateT.lift, bind, pure, Except.bind, Except.pure, Except.map, Functor.map,
      throw, throwThe, MonadExceptOf.throw, TrustIr.CompilerCompat.Strings.appendModern_eq]

private theorem canonical_control_values :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 255, .int 64 2] 0 .abort) TrustIr.MachineState.empty =
        .error .outOfFuel ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 0) ⟨0⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
        .ok ([.int 64 255], targetAfter (targetEntry 255 2) 2 127) ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 3 2) ⟨0⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
        .error (.typeError (trustIrStringBuild s!"undefined SSA value: {repr (⟨2⟩ : TrustIr.ValueId)}")) := by
  constructor
  · rw [TrustIr.AYUnaryReplay.entry_decomposition, TrustIr.Sem.run_bind,
      fixture_entry_checks, Except.bind]
    rfl
  · constructor
    · rw [canonical_entry_control, canonical_reader_values.1]
      exact target_finish_value _ _ _ 255
    · rw [canonical_entry_control, canonical_reader_values.2]
      exact target_finish_error _ _ _

theorem canonical_wrong_return_returns_dividend :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 0) ⟨0⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
        .ok ([.int 64 255], targetAfter (targetEntry 255 2) 2 127) :=
  canonical_control_values.2.1

theorem canonical_wrong_destination_refuses :
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 3 2) ⟨0⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
        .error (.typeError (trustIrStringBuild s!"undefined SSA value: {repr (⟨2⟩ : TrustIr.ValueId)}")) :=
  canonical_control_values.2.2

theorem actual_instruction_fuel_is_owed :
    SemR.runFunction (sourceModule 2 2) 0 [.int .u64 255, .int .u64 2] 1 0 =
      .outOfFuel ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
      [.int 64 255, .int 64 2] 0 .abort) TrustIr.MachineState.empty =
        .error .outOfFuel := by
  constructor
  · rfl
  · exact canonical_control_values.1

theorem original_function_identity_is_checked :
    SemR.runFunction (sourceModule 2 2) 1 [.int .u64 255, .int .u64 2] 2 0 =
      .typeError "MissingFunction: function not found" ∧
    TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨1⟩
      [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
        .error (.typeError "evalFunctionInContext: undefined entry function") := by
  exact ⟨rfl, rfl⟩

theorem full_function_false_postcondition_is_refused :
    ¬ (∃ sourceReturned targetReturned after,
      SemR.runFunction (sourceModule 2 2) 0 [.int .u64 255, .int .u64 2] 2 0 =
        .ret sourceReturned ∧
      TrustIr.Sem.run (TrustIr.evalFunctionInContext (context 2 2) ⟨0⟩
        [.int 64 255, .int 64 2] 1 .abort) TrustIr.MachineState.empty =
          .ok (targetReturned, after) ∧
      sourceReturned = [.int .u64 126] ∧ targetReturned = [.int 64 126]) := by
  have agreement := function_wp_iff (sourceModule 2 2) 0 (sourceFunction 2 2)
    (sourceBlock 2 2) (context 2 2) (targetFunction 2 2) 255 2 0 0 0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (target_declarations 2 2)
    (by decide) (by decide)
    (fun sourceReturned targetReturned =>
      sourceReturned = [.int .u64 126] ∧ targetReturned = [.int 64 126])
  intro counterfeit
  have impossible := agreement.mp counterfeit
  simp at impossible

end SemR.CanonicalScalarReturn.Controls
