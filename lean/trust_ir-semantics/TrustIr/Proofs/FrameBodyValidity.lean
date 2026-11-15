-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameResultValidity
import TrustIr.Proofs.FrameSlotValidity
import TrustIr.Proofs.FrameAliasValidity
import TrustIr.Proofs.FrameUnaryValidity
import TrustIr.Proofs.FrameBinaryValidity
import TrustIr.Proofs.FrameComparisonValidity
import TrustIr.Proofs.FrameCastValidity
import TrustIr.Proofs.FrameAggregateValidity
import TrustIr.Proofs.FrameConstructionValidity
import TrustIr.Proofs.FrameFieldValidity
import TrustIr.Proofs.FramePointerValidity
import TrustIr.Proofs.FrameCollectionValidity
import TrustIr.Proofs.GenericCoroPrefixLoop

namespace TrustIr.FrameLifetime
open GenericCoro.Prefix

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

/-- Covered body instructions for recursive frame-identity preservation. -/
inductive FrameInstruction : Inst → Prop where
  | open (definition : BindingFrameDef) : FrameInstruction (.OpenFrame definition)
  | bind (frame : ValueId) (slot : Nat) (value : ValueId) : FrameInstruction (.BindSlot frame slot value)
  | load (frame : ValueId) (slot : Nat) (ty : Ty) : FrameInstruction (.LoadSlot frame slot ty)
  | close (frame : ValueId) : FrameInstruction (.CloseFrame frame)
  | copy (ty : Ty) (operand : ValueId) : FrameInstruction (.Copy ty operand)
  | select (ty : Ty) (condition yes no : ValueId) : FrameInstruction (.Select ty condition yes no)
  | unary (op : UnOp) (ty : Ty) (operand : ValueId) : FrameInstruction (.UnOp op ty operand)
  | binary (op : BinOp) (ty : Ty) (left right : ValueId) : FrameInstruction (.BinOp op ty left right)
  | icmp (op : ICmpOp) (ty : Ty) (left right : ValueId) : FrameInstruction (.ICmp op ty left right)
  | fcmp (op : FCmpOp) (ty : Ty) (left right : ValueId) : FrameInstruction (.FCmp op ty left right)
  | cast (op : CastOp) (srcTy dstTy : Ty) (operand : ValueId) : FrameInstruction (.Cast op srcTy dstTy operand)
  | extractElement (ty : Ty) (array index : ValueId) : FrameInstruction (.ExtractElement ty array index)
  | insertElement (ty : Ty) (array index value : ValueId) : FrameInstruction (.InsertElement ty array index value)
  | makeAggregate (ty : Ty) (variant : Option Nat) (fields : List ValueId) : FrameInstruction (.MakeAggregate ty variant fields)
  | makeClosure (cid : ClosureTyId) (fn : FuncId) (captures : List ValueId) : FrameInstruction (.MakeClosure cid fn captures)
  | arraySplat (ty : Ty) (operand : ValueId) : FrameInstruction (.ArraySplat ty operand)
  | extractField (ty : Ty) (operand : ValueId) (field : Nat) : FrameInstruction (.ExtractField ty operand field)
  | insertField (ty : Ty) (operand : ValueId) (field : Nat) (value : ValueId) : FrameInstruction (.InsertField ty operand field value)
  | ptrData (ty : Ty) (operand : ValueId) : FrameInstruction (.PtrData ty operand)
  | ptrMetadata (ty metadataTy : Ty) (operand : ValueId) : FrameInstruction (.PtrMetadata ty metadataTy operand)
  | ptrFromParts (ty metadataTy : Ty) (data metadata : ValueId) : FrameInstruction (.PtrFromParts ty metadataTy data metadata)
  | sequenceAdd (ty : Ty) (operand : ValueId) (k : Nat) : FrameInstruction (.SeqMapAddK ty operand k)
  | sequenceNot (ty : Ty) (operand : ValueId) : FrameInstruction (.SeqMapNot ty operand)
  | overflow (op : OverflowOp) (ty : Ty) (left right : ValueId) : FrameInstruction (.Overflow op ty left right)
  | undef (ty : Ty) : FrameInstruction (.Undef ty)
  | null : FrameInstruction .NullPtr

/-- Body arithmetic may produce one, no, or multiple SSA results, never control. -/
def BodyValueResult : InstrResult → Prop
  | .value _ | .values _ => True
  | .terminator _ => False

private theorem mapped_step_success {α : Type} (action : Sem α) (encode : α → Option ValueId)
    (s final : MachineState) (result : InstrResult)
    (preserve : ∀ value after, Sem.run action s = .ok (value, after) → WellMintedState after)
    (run : Sem.run (action >>= fun value => pure (.value (encode value))) s = .ok (result, final)) :
    BodyValueResult result ∧ WellMintedState final := by
  obtain ⟨value, middle, executed, tail⟩ := split_bind_success _ _ s final result run
  change Except.ok (.value (encode value), middle) = Except.ok (result, final) at tail
  cases tail
  exact ⟨True.intro, preserve value final executed⟩

/-- Successful contextual execution of frame and alias instructions preserves
recursive identity validity and produces only body values. -/
theorem WellMintedState.frame_step_success (ctx : EvalContext) (inst : Inst)
    (site : FrameInstruction inst) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx inst) s = .ok (result, final)) :
    BodyValueResult result ∧ WellMintedState final := by
  cases site with
  | «open» definition =>
    exact mapped_step_success (semOpenFrame definition) some s final result
      (fun id after executed => WellMintedState.open_success s after definition id valid executed) run
  | bind frame slot value =>
    exact mapped_step_success (semBindSlot frame slot value) some s final result
      (fun id after executed => WellMintedState.bind_success s after frame value id slot valid executed) run
  | load frame slot ty =>
    exact mapped_step_success (semLoadSlot frame slot ty) some s final result
      (fun id after executed => WellMintedState.load_success s after frame id slot ty valid executed) run
  | close frame =>
    apply mapped_step_success (semCloseFrame frame) (fun _ => none) s final result ?_ run
    intro unit after executed
    cases unit
    exact WellMintedState.close_success s after frame valid executed
  | copy ty operand =>
    obtain ⟨id, shape, preserved⟩ := WellMintedState.copy_step_success ctx ty operand s final result valid run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | select ty condition yes no =>
    obtain ⟨id, shape, preserved⟩ := WellMintedState.select_step_success ctx ty condition yes no s final result valid run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | unary op ty operand =>
    exact mapped_step_success (semUnOp op ty operand) some s final result
      (fun id after executed => WellMintedState.unary_success s after op ty operand id valid executed) run
  | binary op ty left right =>
    rw [binary_step_eq] at run
    exact mapped_step_success (binaryAction op ty left right) some s final result
      (fun id after executed => WellMintedState.binary_action_success s after op ty left right id valid executed) run
  | icmp op ty left right =>
    exact mapped_step_success (semICmpInst op ty left right ctx.byteModel) some s final result
      (fun id after executed => valid.integer_compare_success s after op ty left right id ctx.byteModel executed) run
  | fcmp op ty left right =>
    exact mapped_step_success (semFCmpInst op ty left right) some s final result
      (fun id after executed => valid.float_compare_success s after op ty left right id executed) run
  | cast op srcTy dstTy operand =>
    exact mapped_step_success (semCast op srcTy dstTy operand ctx.byteModel) some s final result
      (fun id after executed => valid.cast_success s after op srcTy dstTy operand id ctx.byteModel executed) run
  | extractElement ty array index =>
    exact mapped_step_success (semExtractElementUsing (ctx.elementIndex index) ty array index) some s final result
      (fun id after executed => valid.extract_element_success (ctx.elementIndex index)
        (element_index_success_state ctx index) s after ty array index id executed) run
  | insertElement ty array index value =>
    exact mapped_step_success (semInsertElementUsing (ctx.elementIndex index) ty array index value) some s final result
      (fun id after executed => valid.insert_element_success (ctx.elementIndex index)
        (element_index_success_state ctx index) s after ty array index value id executed) run
  | makeAggregate ty variant fields =>
    obtain ⟨id, shape, preserved⟩ := valid.make_aggregate_step_success ctx ty variant fields s final result run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | makeClosure cid fn captures =>
    obtain ⟨id, shape, preserved⟩ := valid.make_closure_step_success ctx cid fn captures s final result run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | arraySplat ty operand =>
    obtain ⟨id, shape, preserved⟩ := valid.array_splat_step_success ctx ty operand s final result run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | extractField ty operand field =>
    obtain ⟨id, shape, preserved⟩ := valid.extract_field_step_success ctx ty operand field s final result run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | insertField ty operand field value =>
    obtain ⟨id, shape, preserved⟩ := valid.insert_field_step_success ctx ty operand value field s final result run
    rw [shape]
    exact ⟨True.intro, preserved⟩
  | ptrData ty operand =>
    exact mapped_step_success (semPtrData ty operand ctx.byteModel) some s final result
      (fun id after executed => valid.pointer_data_success s after ty operand id ctx.byteModel executed) run
  | ptrMetadata ty metadataTy operand =>
    exact mapped_step_success (semPtrMetadata ty metadataTy operand ctx.byteModel) some s final result
      (fun id after executed => valid.pointer_metadata_success s after ty metadataTy operand id ctx.byteModel executed) run
  | ptrFromParts ty metadataTy data metadata =>
    exact mapped_step_success (semPtrFromParts ty metadataTy data metadata ctx.byteModel) some s final result
      (fun id after executed => valid.pointer_from_parts_success s after ty metadataTy data metadata id ctx.byteModel executed) run
  | sequenceAdd ty operand k =>
    exact mapped_step_success (semSeqMapAddK ty operand k) some s final result
      (fun id after executed => valid.sequence_add_success s after ty operand id k executed) run
  | sequenceNot ty operand =>
    exact mapped_step_success (semSeqMapNot ty operand) some s final result
      (fun id after executed => valid.sequence_not_success s after ty operand id executed) run
  | overflow op ty left right =>
    obtain ⟨ids, middle, executed, tail⟩ := split_bind_success (semOverflow op ty left right) _ s final result run
    change Except.ok (.values [ids.1, ids.2], middle) = Except.ok (result, final) at tail
    cases tail
    exact ⟨True.intro, valid.overflow_success s final op ty left right ids executed⟩
  | undef ty =>
    change Sem.run (if isPartialLoadTy ty then (do
      let id ← Sem.bindFresh (.undef ty)
      pure (InstrResult.value (some id))) else Sem.throwUB (nonpartialUndefMessage ty)) s = .ok (result, final) at run
    cases allowed : isPartialLoadTy ty with
    | false =>
      simp [allowed, Sem.throwUB, Sem.run, StateT.run, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
    | true =>
      exact mapped_step_success (Sem.bindFresh (.undef ty)) some s final result
        (fun id after executed => WellMintedState.fresh_success s after (.undef ty) id valid
          (mintedValue_undef _ ty) executed) (by simpa [allowed] using run)
  | null =>
    exact mapped_step_success (Sem.bindFresh .nullPtr) some s final result
      (fun id after executed => WellMintedState.fresh_success s after .nullPtr id valid
        (mintedValue_null _) executed) run

/-- Exact production-body outcome after a frame primitive succeeds. The
original context binder, its errors and the complete final state are retained. -/
theorem frame_body_computed (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : FrameInstruction inst)
    (dests : List ValueId) (s after : MachineState) (result : InstrResult) (shape : BodyValueResult result)
    (computed : Sem.run (stepInstWithContext ctx inst) s = .ok (result, after)) :
    Sem.run (evalBodyStep recurse ctx depth strategy (inst, dests)) s =
      Sem.run (ctx.bindInstructionResults inst result dests >>= fun _ => pure (.yield ())) after := by
  cases result with
  | value id => cases site <;> simp only [evalBodyStep, run_bind, computed] <;> rfl
  | values ids => cases site <;> simp only [evalBodyStep, run_bind, computed] <;> rfl
  | terminator control => exact False.elim shape

theorem frame_body_error (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : FrameInstruction inst)
    (dests : List ValueId) (s : MachineState) (error : SemError)
    (failed : Sem.run (stepInstWithContext ctx inst) s = .error error) :
    Sem.run (evalBodyStep recurse ctx depth strategy (inst, dests)) s = .error error := by
  cases site <;> simp only [evalBodyStep, run_bind, failed] <;> rfl

/-- Successful production frame body nodes preserve the invariant THROUGH
SSA publication. There are no separate success premises for the primitive,
metadata checks or destination binding, and no supplied intermediate state. -/
theorem WellMintedState.frame_body_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : FrameInstruction inst)
    (dests : List ValueId) (s final : MachineState) (outcome : ForInStep Unit)
    (valid : WellMintedState s)
    (run : Sem.run (evalBodyStep recurse ctx depth strategy (inst, dests)) s = .ok (outcome, final)) :
    WellMintedState final := by
  cases stepped : Sem.run (stepInstWithContext ctx inst) s with
  | error error =>
    rw [frame_body_error recurse ctx depth strategy inst site dests s error stepped] at run
    contradiction
  | ok pair =>
    rcases pair with ⟨result, after⟩
    obtain ⟨shape, preserved⟩ := WellMintedState.frame_step_success ctx inst site s after result valid stepped
    rw [frame_body_computed recurse ctx depth strategy inst site dests s after result shape stepped] at run
    obtain ⟨unit, published, binder, tail⟩ := split_bind_success _ _ after final outcome run
    cases unit
    change Except.ok (.yield (), published) = Except.ok (outcome, final) at tail
    cases tail
    exact WellMintedState.bind_instruction_success ctx inst result dests after final preserved binder

/-- Any successful original body list made of covered operations preserves
recursive identity validity, using each actual successor state in order. -/
theorem WellMintedState.frame_body_list_success (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId)) (s final : MachineState)
    (sites : ∀ row ∈ rows, FrameInstruction row.1) (valid : WellMintedState s)
    (run : Sem.run (evalBody recurse ctx depth strategy rows) s = .ok ((), final)) :
    WellMintedState final := by
  induction rows generalizing s with
  | nil =>
    change Except.ok ((), s) = Except.ok ((), final) at run
    cases run
    exact valid
  | cons row rest ih =>
    rw [evalBody_cons] at run
    obtain ⟨outcome, middle, first, tail⟩ := split_bind_success _ _ s final () run
    have preserved := WellMintedState.frame_body_success recurse ctx depth strategy row.1
      (sites row (.head rest)) row.2 s middle outcome valid first
    exact ih middle (fun row member => sites row (.tail _ member)) preserved tail

/-- Closed production witness: OpenFrame publishes over a distinct temporary,
BindSlot publishes at its own fresh id, LoadSlot publishes at a high explicit
destination and retires its temporary, and CloseFrame closes the old alias. -/
theorem published_frame_roundtrip (withDeclarations : Bool) :
    let definition : BindingFrameDef := ⟨⟨0⟩, "body", [⟨"x", .I32⟩]⟩
    let rows : List (Inst × List ValueId) := [
      (.OpenFrame definition, [⟨10⟩]),
      (.BindSlot ⟨10⟩ 0 ⟨5⟩, [⟨11⟩]),
      (.LoadSlot ⟨11⟩ 0 .I32, [⟨42⟩]),
      (.CloseFrame ⟨10⟩, [])]
    let state := { MachineState.empty with
      locals := ValueMap.empty.set ⟨5⟩ (.int 32 7), nextValueId := 6 }
    let context := if withDeclarations then { EvalContext.empty with
      localTypes := some (fun id =>
        if id == ⟨5⟩ || id == ⟨42⟩ then some .I32
        else if id == ⟨10⟩ || id == ⟨11⟩ then some .Ptr else none) }
      else EvalContext.empty
    let program := do
      evalBody (fun _ _ _ _ _ _ => throw SemError.outOfFuel) context 0 .abort rows
      let after ← Sem.getState
      pure ([5, 6, 10, 11, 12, 42].map (fun index => after.lookupValue ⟨index⟩),
        after.openFrameLineages, after.nextFrameLineage, after.nextValueId)
    (Sem.run program state).map Prod.fst =
      .ok ([some (.int 32 7), none, some (.frame 0 [.undef .I32]),
        some (.frame 0 [.int 32 7]), none, some (.int 32 7)], [], 1, 43) := by
  cases withDeclarations <;> trustIrReduce

end TrustIr.FrameLifetime
