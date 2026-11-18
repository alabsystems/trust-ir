-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemRScalarStep

namespace SemR.CanonicalScalarStep.Controls

private def source (destination dividend divisor : Nat) : SemR.Core :=
  let block : SemR.Block :=
    { id := 0, params := [], body := [divisionNode 0 1 destination] }
  { fn := { id := 0, ty := 0, entry := 0, blocks := [block] },
    sig := { params := [], returns := [], vararg := false },
    block := block, pc := 0,
    env := [(0, .int .u64 dividend), (1, .int .u64 divisor)],
    depth := 0, stack := [], openFrames := [], nextFrame := 0, mem := .empty }

private def target (dividend divisor : Nat) : TrustIr.MachineState :=
  { TrustIr.MachineState.empty with
    locals := (TrustIr.ValueMap.empty.set ⟨0⟩ (.int 64 (dividend : Int))).set
      ⟨1⟩ (.int 64 (divisor : Int)),
    nextValueId := 3 }

private def module : SemR.Module := { funcTys := [], enums := [], functions := [] }

private def context : TrustIr.EvalContext :=
  { functions := fun _ => none, funcPtrs := fun _ => none,
    funcTys := fun _ => none, maxCallDepth := 0, globalsTable := fun _ => none }

private def recurse : TrustIr.GenericCoro.Prefix.Recurse :=
  fun _ _ _ _ _ _ => throw TrustIr.SemError.outOfFuel

theorem source_actual_step :
    SemR.stepCore module (source 9 255 2) =
      .cont (sourceAfter (source 9 255 2) 9 127) := by
  exact source_step module (source 9 255 2) 0 1 9 255 2 rfl rfl rfl
    (by decide) (by decide)

theorem target_actual_step :
    TrustIr.Sem.run (TrustIr.GenericCoro.Prefix.evalBodyStep recurse context 0 .abort
      (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩, [⟨9⟩])) (target 255 2) =
      .ok (.yield (), targetAfter (target 255 2) 9 127) := by
  exact target_step_raw recurse context 0 .abort (target 255 2) 0 1 9 255 2
    rfl rfl rfl (by decide) (by decide)

theorem explicit_destination_is_bound :
    (targetAfter (target 255 2) 9 127).lookupValue ⟨9⟩ =
      some (.int 64 127) ∧
    (targetAfter (target 255 2) 9 127).lookupValue ⟨3⟩ = none := by
  constructor <;> rfl

theorem fresh_destination_is_not_retired :
    (targetAfter (target 255 2) 3 127).lookupValue ⟨3⟩ = some (.int 64 127) := rfl

theorem input_alias_updates_only_that_register :
    (targetAfter (target 255 2) 0 127).lookupValue ⟨0⟩ = some (.int 64 127) ∧
    (targetAfter (target 255 2) 0 127).lookupValue ⟨1⟩ = some (.int 64 2) ∧
    SemR.lookupEnv (sourceAfter (source 0 255 2) 0 127).env 0 =
      some (.int .u64 127) := by
  exact ⟨rfl, rfl, rfl⟩

theorem zero_refuses_both_steps :
    SemR.stepCore module (source 9 17 0) = .done (.ub "unsigned division by zero") ∧
    TrustIr.Sem.run (TrustIr.GenericCoro.Prefix.evalBodyStep recurse context 0 .abort
      (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩, [⟨9⟩])) (target 17 0) =
        .error (.ub "unsigned division by zero") := by
  constructor
  · exact source_step module (source 9 17 0) 0 1 9 17 0 rfl rfl rfl
      (by decide) (by decide)
  · exact target_step_raw recurse context 0 .abort (target 17 0) 0 1 9 17 0
      rfl rfl rfl (by decide) (by decide)

theorem occupied_temporary_loses_a_live_register :
    let occupied := { target 255 2 with
      locals := (target 255 2).locals.set ⟨3⟩ (.int 64 99) }
    occupied.lookupValue ⟨3⟩ = some (.int 64 99) ∧
      (targetAfter occupied 9 127).lookupValue ⟨3⟩ = none := by
  exact ⟨rfl, rfl⟩

theorem missing_freshness_cannot_preserve_register_agreement :
    let sourceWithLive := { source 9 255 2 with
      env := (3, .int .u64 99) :: (source 9 255 2).env }
    let targetWithLive := { target 255 2 with
      locals := (target 255 2).locals.set ⟨3⟩ (.int 64 99) }
    ¬ RegistersAgree (sourceAfter sourceWithLive 9 127)
      (targetAfter targetWithLive 9 127) := by
  dsimp only
  intro related
  have impossible := related 3
  simp [sourceAfter, source, targetAfter, target, RegistersAgree, scalarImage,
    SemR.lookupEnv, TrustIr.MachineState.bindValue, TrustIr.MachineState.lookupValue,
    TrustIr.ValueMap.set, TrustIr.ValueMap.get, TrustIr.ValueMap.empty] at impossible

theorem wrong_value_is_not_published :
    (targetAfter (target 255 2) 9 127).lookupValue ⟨9⟩ ≠ some (.int 64 126) := by
  change some (TrustIr.Value.int 64 (127 : Int)) ≠ some (.int 64 126)
  simp

theorem wrong_destination_is_not_published :
    (targetAfter (target 255 2) 9 127).lookupValue ⟨8⟩ ≠ some (.int 64 127) := by
  change (none : Option TrustIr.Value) ≠ some (.int 64 127)
  simp

theorem out_of_range_source_is_not_success :
    SemR.evalBinop 64 .udiv (.int .u64) (.int .u64 (2 ^ 64)) (.int .u64 1) =
      .stop (.typeError "TypeError: integer value is out of range for the target width") := rfl

theorem mismatched_width_is_not_success :
    TrustIr.semBinOpValues .UDiv .U64 (.int 32 17) (.int 64 1) =
      .error (.typeError "BinOp: mismatched integer widths") := rfl

theorem initial_register_agreement (dividend divisor : Nat) :
    RegistersAgree (source 9 dividend divisor) (target dividend divisor) := by
  intro id
  by_cases atZero : id = 0
  · subst id; rfl
  · by_cases atOne : id = 1
    · subst id; rfl
    · simp [source, target, SemR.lookupEnv, scalarImage, TrustIr.MachineState.lookupValue,
        TrustIr.ValueMap.empty, TrustIr.ValueMap.get, TrustIr.ValueMap.set,
        atZero, Ne.symm atZero, atOne, Ne.symm atOne]

theorem related_registers_survive_nonsequential_destination :
    RegistersAgree (sourceAfter (source 9 255 2) 9 127)
      (targetAfter (target 255 2) 9 127) :=
  registers_preserved _ _ _ _ (initial_register_agreement 255 2) rfl

theorem false_postcondition_stays_false :
    ¬ (∃ sourceNext targetNext,
      SemR.stepCore module (source 9 255 2) = .cont sourceNext ∧
      TrustIr.Sem.run (TrustIr.GenericCoro.Prefix.evalBodyStep recurse context 0 .abort
        (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩, [⟨9⟩])) (target 255 2) =
          .ok (.yield (), targetNext) ∧
      targetNext.lookupValue ⟨9⟩ = some (.int 64 126)) := by
  rw [division_step_wp_iff module (source 9 255 2) recurse context 0 .abort
    (target 255 2) 0 1 9 255 2 rfl rfl rfl (initial_register_agreement 255 2)
    rfl (by decide) (by decide)]
  simp [wrong_value_is_not_published]

theorem input_alias_actual_steps :
    SemR.stepCore module (source 0 255 2) =
      .cont (sourceAfter (source 0 255 2) 0 127) ∧
    TrustIr.Sem.run (TrustIr.GenericCoro.Prefix.evalBodyStep recurse context 0 .abort
      (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩, [⟨0⟩])) (target 255 2) =
        .ok (.yield (), targetAfter (target 255 2) 0 127) := by
  constructor
  · exact source_step module (source 0 255 2) 0 1 0 255 2 rfl rfl rfl
      (by decide) (by decide)
  · exact target_step_raw recurse context 0 .abort (target 255 2) 0 1 0 255 2
      rfl rfl rfl (by decide) (by decide)

theorem occupied_temporary_initial_registers_agree :
    let sourceWithLive := { source 9 255 2 with
      env := (3, .int .u64 99) :: (source 9 255 2).env }
    let targetWithLive := { target 255 2 with
      locals := (target 255 2).locals.set ⟨3⟩ (.int 64 99) }
    RegistersAgree sourceWithLive targetWithLive := by
  dsimp only
  intro id
  by_cases atLive : id = 3
  · subst id; rfl
  · simpa [source, sourceAfter, target, SemR.lookupEnv, scalarImage,
      TrustIr.MachineState.lookupValue, TrustIr.ValueMap.get, TrustIr.ValueMap.set,
      atLive, Ne.symm atLive] using initial_register_agreement 255 2 id

theorem original_destination_declaration_is_checked :
    let conflict := { context with localTypes := some (fun _ => some .Bool) }
    conflict.instructionResultTypes (.BinOp .UDiv .U64 ⟨0⟩ ⟨1⟩) [⟨9⟩] 1 =
        .error (.typeError "SSA types: result destination conflicts with instruction declaration") := by
  dsimp only
  simp [TrustIr.EvalContext.instructionResultTypes, TrustIr.ssaInstructionResultTypes,
    context, TrustIr.localResultTypes, TrustIr.ssaResultSourceType,
    TrustIr.closureTyEq, List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw]

end SemR.CanonicalScalarStep.Controls
