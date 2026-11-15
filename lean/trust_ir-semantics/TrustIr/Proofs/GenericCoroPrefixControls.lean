-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixInference
import TrustIr.Proofs.GenericCoroControls

namespace TrustIr.GenericCoro.PrefixControls
open TrustIr.GenericCoro.Controls

def graph (trailing : List (List ValueId)) : List (BlockId × BasicBlock) := [
  (⟨900⟩, {
    params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    body := [.Copy .I32 ⟨1⟩]
    bodyResultDests := [⟨5⟩] :: trailing
    terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨5⟩ })]

def selectedTarget {blocks : List (BlockId × BasicBlock)} :
    Except SemError (FunctionExpansion blocks) → Option BasicBlock
  | .error _ => none
  | .ok (.capacity _ _) => none
  | .ok (.expanded _ target _) => target.cfg ⟨900⟩

/-- This is the actual factory whose before control left CoroSuspend in place.
    The source Copy remains first and the yielded source id remains5. -/
theorem actual_factory_expands_nonempty_entry :
    (selectedTarget (prepared (graph []))).map BasicBlock.terminator = some (.Return [⟨5⟩]) := by rfl

theorem prefix_destination_is_retained :
    (selectedTarget (prepared (graph []))).map BasicBlock.bodyResultDests =
      some [[⟨5⟩], [⟨3⟩], [⟨4⟩], [⟨6⟩], []] := by rfl

/-- Raw trailing rows reserve names even though no source instruction uses
    them. Appended macro rows must not inherit those old rows as destinations. -/
theorem unused_trailing_rows_are_reserved :
    preparedNames (prepared (graph [[⟨3⟩], [⟨4⟩]])) = some [6,8,9] := by rfl

theorem actual_prefix_rows_are_normalized_before_append :
    (selectedTarget (prepared (graph [[⟨3⟩], [⟨4⟩]]))).map BasicBlock.bodyResultDests =
      some [[⟨5⟩], [⟨6⟩], [⟨8⟩], [⟨9⟩], []] := by rfl

theorem full_prefix_and_macro_are_retained :
    (selectedTarget (prepared (graph [[⟨3⟩], [⟨4⟩]]))).map BasicBlock.body = some [
      .Copy .I32 ⟨1⟩,
      .Const .I64 (.int 0), .GEP .I64 ⟨0⟩ [⟨6⟩] false,
      .Const .I64 (.int 17), .Store .I64 ⟨8⟩ ⟨9⟩ false none] := by rfl

end TrustIr.GenericCoro.PrefixControls
