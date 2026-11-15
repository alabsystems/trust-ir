-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr

/-- Constructor membership transports an opaque composite operand. This is
    not a module-admission or a recursive well-formedness theorem. -/
theorem checkAggregateLane_tuple_transport (model : ByteModel)
    (types : List Ty) (values : List Value) :
    checkAggregateLane model (.Tuple types) (.aggregate values) = .ok () := by
  rfl

theorem checkAggregateLane_record_transport (model : ByteModel) (id : RecordId)
    (fields : List (String × Value)) :
    checkAggregateLane model (.Record id) (.record fields) = .ok () := by
  rfl

theorem checkAggregateLane_nested_poison_is_not_inspected :
    checkAggregateLane .le64 (.Tuple [.U64, .Char])
      (.aggregate [.uninit, .int 32 0xD800]) = .ok () := by
  rfl

theorem checkAggregateLane_immediate_poison_refused :
    checkAggregateLane .le64 (.Tuple [.U64]) (.partial [none]) =
      .error (.ub "MakeAggregate: uninitialized immediate operand") := by
  rfl

theorem checkAggregateLane_wrong_bool_carrier_refused :
    checkAggregateLane .le64 .Bool (.int 1 1) =
      .error (.typeError "MakeAggregate: operand does not match its declared type") := by
  rfl

theorem checkAggregateLane_wrong_integer_width_refused :
    checkAggregateLane .le32 .Usize (.int 64 42) =
      .error (.typeError "MakeAggregate: operand does not match its declared type") := by
  rfl

/-- The contextual rule refuses non-partial Undef before allocating an SSA
    result. The bare stepInst Undef contract remains separate. -/
theorem stepInstWithContext_nonpartial_undef (ctx : EvalContext) (ty : Ty)
    (h : isPartialLoadTy ty = false) :
    stepInstWithContext ctx (.Undef ty) =
      Sem.throwUB (nonpartialUndefMessage ty) := by
  change (if isPartialLoadTy ty then stepInst (.Undef ty) ctx.byteModel
    else Sem.throwUB _) = _
  rw [h]
  rfl

private def unwrittenEnumContext : EvalContext :=
  { EvalContext.empty with
    enums := fun id => if id.index == 0 then
      some { id := ⟨0⟩
             name := "CarriesTuple"
             variants := [{ name := "Only", fields := [.Tuple [.U64, .U64]] }] }
      else none }

theorem makeAggregateValueWithContext_transports_unwritten_tuple :
    makeAggregateValueWithContext unwrittenEnumContext (.Enum ⟨0⟩) (some 0)
      [.aggregate [.uninit, .int 64 42]] =
      .ok (.aggregate [.int 8 0, .aggregate [.uninit, .int 64 42]]) := by
  rfl

end TrustIr
