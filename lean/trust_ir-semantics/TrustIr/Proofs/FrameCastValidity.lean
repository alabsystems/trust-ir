-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameUnaryValidity
import TrustIr.Proofs.FrameDecodeFreedom
import TrustIr.Semantics.Cast

namespace TrustIr.FrameLifetime

private theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state =
      (Sem.run action state >>= fun pair => Sem.run (next pair.1) pair.2) := rfl

private theorem split_bind_success {α β : Type} (action : Sem α) (next : α → Sem β)
    (s final : MachineState) (result : β)
    (run : Sem.run (action >>= next) s = .ok (result, final)) :
    ∃ value middle, Sem.run action s = .ok (value, middle) ∧
      Sem.run (next value) middle = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run action s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa [step] using run⟩

private theorem lookup_success (s final : MachineState) (id : ValueId) (value : Value)
    (run : Sem.run (Sem.lookupValue id) s = .ok (value, final)) :
    s.lookupValue id = some value ∧ final = s := by
  cases lookup : s.lookupValue id with
  | none =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, Sem.throwTypeError, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, lookup, StateT.run,
      StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- Numeric pointers carry no frame identities, regardless of provenance. -/
theorem mintedValue_pointer (bound address : Nat) (provenance : Option AllocId) :
    MintedValue bound (.ptr address provenance) := by
  intro lineage occurs
  cases occurs

private theorem free_fresh_success (s final : MachineState) (value : Value) (id : ValueId)
    (valid : WellMintedState s) (free : MintedValue 0 value)
    (run : Sem.run (Sem.bindFresh value) s = .ok (id, final)) : WellMintedState final :=
  valid.fresh_success s final value id (free.mono (Nat.zero_le _)) run

private theorem throw_success {α : Type} (s final : MachineState) (value : α) (error : SemError)
    (run : Sem.run (throw error : Sem α) s = .ok (value, final)) : False := by
  cases run

private theorem address_success_state (op : String) (width : Nat) (raw : Int)
    (model : ByteModel) (s final : MachineState) (address : Nat)
    (run : Sem.run (Sem.addrOfInt op width raw model) s = .ok (address, final)) : final = s := by
  by_cases carrier : (raw % (2 ^ width)).toNat < 2 ^ Sem.addrBits
  all_goals
    by_cases target : (raw % (2 ^ width)).toNat < model.addressLimit
    all_goals
      cases model <;>
        simp [Sem.addrOfInt, carrier, target, Sem.run, Sem.throwUB,
          StateT.run, StateT.pure, StateT.lift, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
      all_goals exact run.2.symm

private theorem resolve_fresh_success (op : String) (width : Nat) (raw : Int)
    (model : ByteModel) (s final : MachineState) (id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (do
      let address ← Sem.addrOfInt op width raw model
      let state ← Sem.getState
      Sem.bindFresh (state.memory.resolveAddr address)) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨address, middle, computed, tail⟩ := split_bind_success _ _ s final id run
  have same := address_success_state op width raw model s middle address computed
  subst middle
  change Sem.run (Sem.bindFresh (s.memory.resolveAddr address)) s = .ok (id, final) at tail
  apply free_fresh_success s final _ id valid ?_ tail
  unfold Memory.resolveAddr
  split
  · exact mintedValue_null 0
  · exact mintedValue_pointer 0 _ _

private theorem pointer_integer_success (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (s final : MachineState) (id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (Sem.bindPointerInteger op ty address model) s = .ok (id, final)) :
    WellMintedState final := by
  unfold Sem.bindPointerInteger at run
  cases widthEq : getTyWidth ty model with
  | error error =>
    simp [widthEq, Sem.run, StateT.run, StateT.bind, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
  | ok width =>
    simp only [widthEq] at run
    change Sem.run (if address < model.addressLimit then Sem.bindFresh (Value.intAt width (Int.ofNat address))
      else Sem.throwUB _) s = .ok (id, final) at run
    split at run
    · exact free_fresh_success s final _ id valid (mintedValue_int 0 _ _) run
    · exact False.elim (throw_success s final id _ run)

private theorem pointer_provenance_success (op : String) (ty : Ty) (address : Nat)
    (provenance : Option AllocId) (model : ByteModel) (s final : MachineState) (id : ValueId)
    (valid : WellMintedState s)
    (run : Sem.run (Sem.bindPointerIntegerWithProvenance op ty address provenance model) s = .ok (id, final)) :
    WellMintedState final := by
  cases provenance with
  | some alloc => exact pointer_integer_success op ty address model s final id valid run
  | none =>
    unfold Sem.bindPointerIntegerWithProvenance at run
    cases widthEq : getTyWidth ty model with
    | error error =>
      simp [widthEq, Sem.run, StateT.run, StateT.bind, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
    | ok width =>
      simp only [widthEq] at run
      change Sem.run (if address < word64Limit then Sem.bindFresh (Value.intAt width (Int.ofNat address))
        else Sem.throwUB _) s = .ok (id, final) at run
      split at run
      · exact free_fresh_success s final _ id valid (mintedValue_int 0 _ _) run
      · exact False.elim (throw_success s final id _ run)

private theorem reject_success_state (value : Value) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value "Cast") s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

/-- All seventeen actual cast paths preserve recursive frame identities.
The legacy closure reification transports its original nested captures; numeric
and pointer paths produce frame-free values with all original guards retained. -/
theorem WellMintedState.cast_success (s final : MachineState) (op : CastOp)
    (srcTy dstTy : Ty) (operandId id : ValueId) (model : ByteModel) (valid : WellMintedState s)
    (run : Sem.run (semCast op srcTy dstTy operandId model) s = .ok (id, final)) :
    WellMintedState final := by
  obtain ⟨operand, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operandId) _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operandId operand looked
  subst middle
  have operandValid := valid.values operandId operand lookup
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success (Sem.rejectPartial operand "Cast") _ s final id tail
  cases unit
  have same := reject_success_state operand s middle guarded
  subst middle
  cases op <;> dsimp only at tail
  all_goals simp only [Sem.throwTypeError, Sem.throwUB, Sem.throwUnsupported] at tail
  all_goals
    repeat' first
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_int 0 _ _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_float 0 _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_bool 0 _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_pointer 0 _ _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_null 0) tail
      | with_reducible exact valid.fresh_success s final _ id operandValid tail
      | with_reducible exact resolve_fresh_success _ _ _ model s final id valid tail
      | with_reducible exact pointer_integer_success _ _ _ model s final id valid tail
      | with_reducible exact pointer_provenance_success _ _ _ _ model s final id valid tail
      | with_reducible exact False.elim (throw_success s final id _ tail)
      | split at tail

private theorem checked_cast_tail {α β : Type} (checked : Except SemError α)
    (next : α → Sem β) (state final : MachineState) (result : β)
    (run : Sem.run (Sem.fromMemoryExcept checked >>= next) state = .ok (result, final)) :
    ∃ value, checked = .ok value ∧ Sem.run (next value) state = .ok (result, final) := by
  obtain ⟨value, middle, checkedRun, tail⟩ := split_bind_success _ _ state final result run
  have same := memory_check_success_state checked state middle value checkedRun
  have observed := memory_check_success_result checked state middle value checkedRun
  subst middle
  exact ⟨value, observed, tail⟩

private theorem contextual_cast_fresh (state final : MachineState) (value : Value) (result : InstrResult)
    (valid : WellMintedState state) (free : MintedValue 0 value)
    (run : Sem.run (Sem.bindFresh value >>= fun id => pure (.value (some id))) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, fresh, finished⟩ := split_bind_success _ _ state final result run
  have preserved := free_fresh_success state middle value id valid free fresh
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at finished
  cases finished
  exact ⟨id, rfl, preserved⟩

private theorem contextual_cast_bare (state final : MachineState) (op : CastOp)
    (source destination : Ty) (operand : ValueId) (model : ByteModel)
    (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (stepInst (.Cast op source destination operand) model) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, cast, finished⟩ := split_bind_success _ _ state final result run
  have preserved := valid.cast_success state middle op source destination operand id model cast
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at finished
  cases finished
  exact ⟨id, rfl, preserved⟩

private theorem contextual_cast_decoded (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (plan : AggregateMemory.Plan) (bytes : ByteImage)
    (state final : MachineState) (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (do
      let value ← Sem.fromMemoryExcept (AggregateMemory.decode model order memory plan bytes)
      let id ← Sem.bindFresh value
      pure (.value (some id))) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨value, decoded, tail⟩ := checked_cast_tail _ _ state final result run
  have free := aggregate_decode_frame_exit model order memory plan bytes
  rw [decoded] at free
  exact contextual_cast_fresh state final value result valid free tail

private theorem contextual_reject_success_state (op : String) (value : Value)
    (state final : MachineState)
    (run : Sem.run (Sem.rejectPartial value op) state = .ok ((), final)) : final = state := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

private def contextualItemByteCast (ctx : EvalContext) (source destination : Ty)
    (operand : ValueId) : Sem InstrResult :=
  do
      let service ← match ctx.memoryService with
        | some service => pure service
        | none => Sem.throwTypeError "FnItem cast: original source layouts are absent"
      if service.model != ctx.byteModel then
        Sem.throwTypeError "FnItem cast: source layout target differs from evaluator target"
      let sourcePlan ← Sem.fromMemoryExcept (service.query source)
      let destinationPlan ← Sem.fromMemoryExcept (service.query destination)
      if sourcePlan.layout.size != destinationPlan.layout.size then
        Sem.throwTypeError "FnItem cast: byte extents differ"
      let value ← Sem.lookupValue operand
      Sem.rejectPartial value "FnItem cast"
      let image ← Sem.fromMemoryExcept
        (AggregateMemory.encode ctx.byteModel ctx.functionOrder sourcePlan value false)
      let state ← Sem.getState
      let result ← Sem.fromMemoryExcept
        (AggregateMemory.decode ctx.byteModel ctx.functionOrder state.memory destinationPlan image.bytes)
      pure (.value (some (← Sem.bindFresh result)))

private theorem contextual_item_byte_cast_success (ctx : EvalContext) (source destination : Ty)
    (operand : ValueId) (state final : MachineState) (result : InstrResult)
    (valid : WellMintedState state)
    (run : Sem.run (contextualItemByteCast ctx source destination operand) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  unfold contextualItemByteCast at run
  cases present : ctx.memoryService with
  | none =>
    simp only [present] at run
    exact False.elim (throw_success state final result _ run)
  | some service =>
    simp only [present, pure_bind] at run
    split at run
    · exact False.elim (throw_success state final result _ run)
    · try simp only [pure_bind] at run
      obtain ⟨sourcePlan, sourceChecked, tail⟩ := checked_cast_tail _ _ state final result run
      obtain ⟨destinationPlan, destinationChecked, tail⟩ := checked_cast_tail _ _ state final result tail
      split at tail
      · exact False.elim (throw_success state final result _ tail)
      · try simp only [pure_bind] at tail
        obtain ⟨value, middle, looked, tail⟩ :=
          split_bind_success (Sem.lookupValue operand) _ state final result tail
        obtain ⟨_, same⟩ := lookup_success state middle operand value looked
        subst middle
        obtain ⟨unit, middle, guarded, tail⟩ :=
          split_bind_success (Sem.rejectPartial value _) _ state final result tail
        cases unit
        have same := contextual_reject_success_state _ value state middle guarded
        subst middle
        obtain ⟨image, encoded, tail⟩ := checked_cast_tail _ _ state final result tail
        exact contextual_cast_decoded ctx.byteModel ctx.functionOrder state.memory destinationPlan
          image.bytes state final result valid tail

private theorem contextual_reify_item_success (ctx : EvalContext) (source : FuncId)
    (signature : FuncTyId) (operand : ValueId) (state final : MachineState) (result : InstrResult)
    (valid : WellMintedState state)
    (run : Sem.run (do
      let value ← Sem.lookupValue operand
      Sem.rejectPartial value "ReifyFnPointer"
      match value with
      | .fnItem held =>
        if held != source then Sem.throwTypeError "ReifyFnPointer: item identity differs from source type"
        let declaration ← Sem.fromMemoryExcept (functionItemDeclaration ctx source)
        if declaration.signatureId != signature then
          Sem.throwTypeError "ReifyFnPointer: destination signature differs from item declaration"
        pure (.value (some (← Sem.bindFresh (.fnDef signature source))))
      | _ => Sem.throwTypeError "ReifyFnPointer: source is not a nominal function item") state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ :=
    split_bind_success (Sem.lookupValue operand) _ state final result run
  obtain ⟨_, same⟩ := lookup_success state middle operand value looked
  subst middle
  obtain ⟨unit, middle, guarded, tail⟩ :=
    split_bind_success (Sem.rejectPartial value _) _ state final result tail
  cases unit
  have same := contextual_reject_success_state _ value state middle guarded
  subst middle
  split at tail
  · split at tail
    · exact False.elim (throw_success state final result _ tail)
    · simp only [pure_bind] at tail
      obtain ⟨declaration, checked, tail⟩ := checked_cast_tail _ _ state final result tail
      split at tail
      · exact False.elim (throw_success state final result _ tail)
      · try simp only [pure_bind] at tail
        apply contextual_cast_fresh state final _ result valid ?_ tail
        intro lineage occurs
        cases occurs
  · exact False.elim (throw_success state final result _ tail)

private theorem contextual_cast_default_success (ctx : EvalContext) (op : CastOp)
    (source destination : Ty) (operand : ValueId)
    (equation : stepInstWithContext ctx (.Cast op source destination operand) =
      if (op == .Bitcast || op == .Transmute) &&
          ((match source with | .FnItem _ => true | _ => false) ||
           (match destination with | .FnItem _ => true | _ => false)) then
        contextualItemByteCast ctx source destination operand
      else stepInst (.Cast op source destination operand) ctx.byteModel)
    (state final : MachineState) (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (stepInstWithContext ctx (.Cast op source destination operand)) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  rw [equation] at run
  let isItem : Ty → Bool := fun ty => match ty with | .FnItem _ => true | _ => false
  by_cases selected : ((op == .Bitcast || op == .Transmute) &&
      (isItem source || isItem destination)) = true
  · rw [if_pos selected] at run
    exact contextual_item_byte_cast_success ctx source destination operand state final result valid run
  · rw [if_neg selected] at run
    exact contextual_cast_bare state final op source destination operand ctx.byteModel result valid run

/-- Contextual nominal reification and byte casts use the actual decoder;
legacy casts retain their original semantics and identity-preservation law. -/
theorem WellMintedState.contextual_cast_success (ctx : EvalContext) (state final : MachineState)
    (op : CastOp) (source destination : Ty) (operand : ValueId) (result : InstrResult)
    (valid : WellMintedState state)
    (run : Sem.run (stepInstWithContext ctx (.Cast op source destination operand)) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  cases op
  case ReifyFnPointer =>
    cases source
    case FnItem target =>
      cases destination
      case Func signature => exact contextual_reify_item_success ctx target signature operand state final result valid run
      all_goals
        refine contextual_cast_default_success ctx _ _ _ operand ?_ state final result valid run
        rfl
    all_goals
      refine contextual_cast_default_success ctx _ _ _ operand ?_ state final result valid run
      rfl
  all_goals
    refine contextual_cast_default_success ctx _ _ _ operand ?_ state final result valid run
    rfl

end TrustIr.FrameLifetime
