-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.FrameContextualValidity

namespace TrustIr.FrameLifetime

private def ordinaryDeclaration : BindingFrameDef :=
  { id := ⟨0⟩, name := "ordinary", slots := [{ name := "value", ty := .I32 }] }

private def nominalDeclaration : BindingFrameDef :=
  { id := ⟨3⟩, name := "items", slots := [{ name := "item", ty := .FnItem ⟨7⟩ }] }

private def controlHeader : FunctionItemHeader :=
  { signatureId := ⟨0⟩
    header := { signature := { params := [], returns := [], isVararg := false }, callingConv := .C } }

private def nominalContext : EvalContext :=
  { EvalContext.empty with
    valueSource := FunctionItemPresence.prepare
      { functions :=
          [{ id := ⟨53⟩, header := .ok controlHeader, frames := some [nominalDeclaration] },
           { id := ⟨7⟩, header := .ok controlHeader, frames := none }] } }

private def ordinaryControlState (value : Value) : MachineState :=
  { MachineState.empty with
    locals := (ValueMap.empty.set ⟨0⟩ (.frame 0 [.undef .I32])).set ⟨1⟩ value
    nextValueId := 2, openFrameLineages := [0], nextFrameLineage := 1 }

/-- The original context-free API does not invent a module origin. -/
theorem manual_open_retains_ordinary_snapshot :
    (Sem.run (stepInstWithContext EvalContext.empty (.OpenFrame ordinaryDeclaration))
      MachineState.empty).map (fun (result, state) =>
        (result, state.lookupValue ⟨0⟩, state.openFrameLineages, state.nextFrameLineage)) =
      .ok (.value (some ⟨0⟩), some (.frame 0 [.undef .I32]), [0], 1) := by
  trustIrReduce

/-- A valid original item header does not grant an ordinary slot a nominal type. -/
theorem ordinary_direct_nominal_bind_refused :
    (Sem.run (stepInstWithContext nominalContext (.BindSlot ⟨0⟩ 0 ⟨1⟩))
      (ordinaryControlState (.fnItem ⟨7⟩))).map Prod.fst =
      .error (.typeError "FnItem: runtime kind differs from declared type") := by
  trustIrReduce

theorem ordinary_nested_nominal_bind_refused :
    (Sem.run (stepInstWithContext nominalContext (.BindSlot ⟨0⟩ 0 ⟨1⟩))
      (ordinaryControlState (.aggregate [.fnItem ⟨7⟩]))).map Prod.fst =
      .error (.typeError "FnItem: runtime kind differs from declared type") := by
  trustIrReduce

theorem ordinary_nominal_load_refused :
    (Sem.run (stepInstWithContext nominalContext (.LoadSlot ⟨0⟩ 0 (.FnItem ⟨7⟩)))
      { (ordinaryControlState .uninit) with locals := ValueMap.empty.set ⟨0⟩ (.frame 0 [.fnItem ⟨7⟩]) }).map Prod.fst =
      .error (.typeError "FnItem: runtime kind differs from declared type") := by
  trustIrReduce

theorem ordinary_nested_nominal_load_refused :
    (Sem.run (stepInstWithContext nominalContext (.LoadSlot ⟨0⟩ 0 (.Tuple [.FnItem ⟨7⟩])))
      { (ordinaryControlState .uninit) with
        locals := ValueMap.empty.set ⟨0⟩ (.frame 0 [.aggregate [.fnItem ⟨7⟩]]) }).map Prod.fst =
      .error (.typeError "FnItem: runtime kind differs from declared type") := by
  trustIrReduce

theorem ordinary_bounds_precede_nominal_bind_check :
    (Sem.run (stepInstWithContext nominalContext (.BindSlot ⟨0⟩ 9 ⟨1⟩))
      (ordinaryControlState (.fnItem ⟨7⟩))).map Prod.fst =
      .error (.ub "BindSlot: slot 9 out of range for frame of 1 slots") := by
  trustIrReduce

theorem ordinary_closed_precedes_nominal_bind_check :
    (Sem.run (stepInstWithContext nominalContext (.BindSlot ⟨0⟩ 0 ⟨1⟩))
      { (ordinaryControlState (.fnItem ⟨7⟩)) with openFrameLineages := [] }).map Prod.fst =
      .error (.ub "BindSlot: frame is not open") := by
  trustIrReduce

theorem ordinary_forged_source_frame_bind_refused :
    (Sem.run (stepInstWithContext nominalContext (.BindSlot ⟨0⟩ 0 ⟨1⟩))
      (ordinaryControlState (.aggregate [.sourceFrame 0 ⟨99⟩ nominalDeclaration [.fnItem ⟨7⟩]]))).map Prod.fst =
      .error (.typeError "binding frame: runtime handle requires its Ptr transport type") := by
  trustIrReduce

theorem ordinary_close_unwritten_preserves_original_ub :
    (Sem.run (stepInstWithContext nominalContext (.CloseFrame ⟨0⟩))
      { MachineState.empty with locals := ValueMap.empty.set ⟨0⟩ .uninit }).map Prod.fst =
      .error (.ub "frame handle use: read of an unwritten aggregate lane (uninit)") := by
  trustIrReduce

theorem ordinary_close_non_frame_preserves_original_type_error :
    (Sem.run (stepInstWithContext nominalContext (.CloseFrame ⟨0⟩))
      { MachineState.empty with locals := ValueMap.empty.set ⟨0⟩ (.int 32 7) }).map Prod.fst =
      .error (.typeError "CloseFrame: operand is not a frame") := by
  trustIrReduce

theorem source_zero_fuel_is_refused :
    checkFunctionItemLanes nominalContext 0 .Ptr (.sourceFrame 0 ⟨99⟩ nominalDeclaration [.uninit]) =
      .error (.typeError "binding frame: value nesting does not match its declaration") := by
  trustIrReduce

theorem source_unwritten_origin_mismatch_is_refused :
    (Sem.run (stepInstWithContext nominalContext (.LoadSlot ⟨0⟩ 0 (.FnItem ⟨7⟩)))
      { MachineState.empty with
        locals := ValueMap.empty.set ⟨0⟩
          (.sourceFrame 0 ⟨53⟩ { nominalDeclaration with name := "changed" } [.uninit])
        openFrameLineages := [0], nextFrameLineage := 1, nextValueId := 1 }).map Prod.fst =
      .error (.typeError "binding frame: original declaration differs from held origin") := by
  trustIrReduce

/-- The source-aware route authorizes the actual declared nominal slot and
keeps the original snapshot/alias lineage through bind, load and close. -/
theorem authenticated_nominal_slot_roundtrip :
    let ctx := { nominalContext with currentFunction := some ⟨53⟩ }
    let program := do
      let _ ← stepInstWithContext ctx (.OpenFrame nominalDeclaration)
      let _ ← stepInstWithContext ctx (.BindSlot ⟨6⟩ 0 ⟨5⟩)
      let _ ← stepInstWithContext ctx (.LoadSlot ⟨7⟩ 0 (.FnItem ⟨7⟩))
      let _ ← stepInstWithContext ctx (.CloseFrame ⟨6⟩)
      let state ← Sem.getState
      pure ([6, 7, 8].map (fun id => state.lookupValue ⟨id⟩),
        state.openFrameLineages, state.nextFrameLineage, state.nextValueId)
    (Sem.run program { MachineState.empty with
      locals := ValueMap.empty.set ⟨5⟩ (.fnItem ⟨7⟩), nextValueId := 6 }).map Prod.fst =
      .ok ([some (.sourceFrame 0 ⟨53⟩ nominalDeclaration [.uninit]),
        some (.sourceFrame 0 ⟨53⟩ nominalDeclaration [.fnItem ⟨7⟩]), some (.fnItem ⟨7⟩)], [], 1, 9) := by
  trustIrReduce

end TrustIr.FrameLifetime
