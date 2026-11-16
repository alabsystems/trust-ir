-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameScalarActions
import TrustIr.Proofs.FrameMemoryEncoding

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix NoUnwindEffects

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem ok_safe {α : Type} (value : α) : ExceptNoUnwind (.ok value) := by
  intro exception after run
  cases run

private theorem type_result_safe {α : Type} (message : String) :
    ExceptNoUnwind (.error (.typeError message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem unsupported_result_safe {α : Type} (feature : UnsupportedFeature) (message : String) :
    ExceptNoUnwind (.error (.unsupported feature message) : Except SemError α) := by
  intro exception after run
  cases run

local macro "cast_validation_leaves" : tactic => `(tactic|
  repeat' first
    | exact ok_safe _
    | exact type_result_safe _
    | exact unsupported_result_safe _ _
    | (split <;> try dsimp only))

theorem cast_width_no_unwind (ty : Ty) (model : ByteModel) : ExceptNoUnwind (getTyWidth ty model) := by
  unfold getTyWidth
  cast_validation_leaves

theorem cast_float_membership_no_unwind (ty : Ty) (value : Float) : ExceptNoUnwind (checkFloatAt ty value) := by
  unfold checkFloatAt
  cast_validation_leaves

theorem cast_float_round_no_unwind (ty : Ty) (value : Float) : ExceptNoUnwind (roundFloatAt ty value) := by
  unfold roundFloatAt
  cast_validation_leaves

theorem cast_integer_round_no_unwind (ty : Ty) (value : Int) : ExceptNoUnwind (roundIntToFloatAt ty value) := by
  unfold roundIntToFloatAt
  cast_validation_leaves

theorem cast_float_from_bits_no_unwind (ty : Ty) (value : Int) : ExceptNoUnwind (floatFromBitsAt ty value) := by
  unfold floatFromBitsAt
  cast_validation_leaves

theorem cast_float_to_bits_no_unwind (ty : Ty) (value : Float) : ExceptNoUnwind (floatToBitsAt ty value) := by
  unfold floatToBitsAt
  cast_validation_leaves

local macro "checked_cast_leaf" : tactic => `(tactic|
  first
    | exact cast_width_no_unwind _ _
    | exact cast_float_membership_no_unwind _ _
    | exact cast_float_round_no_unwind _ _
    | exact cast_integer_round_no_unwind _ _
    | exact cast_float_from_bits_no_unwind _ _
    | exact cast_float_to_bits_no_unwind _ _)

local macro "cast_action_leaves" : tactic => `(tactic|
  repeat' first
    | exact fresh_safe _
    | exact pure_safe _
    | exact type_safe _
    | exact ub_safe _
    | exact unsupported_safe _ _
    | exact get_safe
    | (refine checked_error_safe _ _ (by assumption) ?_; checked_cast_leaf)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

theorem cast_address_no_unwind (op : String) (width : Nat) (value : Int) (model : ByteModel) :
    CallCheckNoUnwind (Sem.addrOfInt op width value model) := by
  unfold Sem.addrOfInt
  cast_action_leaves

theorem cast_pointer_integer_no_unwind (op : String) (ty : Ty) (address : Nat) (model : ByteModel) :
    CallCheckNoUnwind (Sem.bindPointerInteger op ty address model) := by
  unfold Sem.bindPointerInteger
  cast_action_leaves

theorem cast_pointer_provenance_no_unwind (op : String) (ty : Ty) (address : Nat)
    (provenance : Option AllocId) (model : ByteModel) :
    CallCheckNoUnwind (Sem.bindPointerIntegerWithProvenance op ty address provenance model) := by
  cases provenance with
  | some allocation => exact cast_pointer_integer_no_unwind op ty address model
  | none =>
    simp only [Sem.bindPointerIntegerWithProvenance]
    cast_action_leaves

local macro "cast_full_leaves" : tactic => `(tactic|
  repeat' first
    | exact cast_address_no_unwind _ _ _ _
    | exact cast_pointer_integer_no_unwind _ _ _ _
    | exact cast_pointer_provenance_no_unwind _ _ _ _ _
    | (solve | cast_action_leaves)
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> try dsimp only)
    | (split <;> try dsimp only))

private theorem cast_Trunc_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .Trunc srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_ZExt_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .ZExt srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_SExt_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .SExt srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_FPTrunc_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .FPTrunc srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_FPExt_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .FPExt srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_FPToUI_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .FPToUI srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_FPToSI_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .FPToSI srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_UIToFP_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .UIToFP srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_SIToFP_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .SIToFP srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_PtrToInt_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .PtrToInt srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_IntToPtr_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .IntToPtr srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_Bitcast_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .Bitcast srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_PtrToPtr_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .PtrToPtr srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_Transmute_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .Transmute srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_ReifyFnPointer_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .ReifyFnPointer srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_FPToSISat_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .FPToSISat srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

private theorem cast_FPToUISat_no_unwind (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast .FPToUISat srcTy dstTy input model) := by
  unfold semCast
  refine CallCheckNoUnwind.bind _ _ (lookup_safe input) (fun operand => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> cast_full_leaves

theorem semCast_no_unwind (op : CastOp) (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    CallCheckNoUnwind (semCast op srcTy dstTy input model) := by
  cases op with
  | Trunc => exact cast_Trunc_no_unwind srcTy dstTy input model
  | ZExt => exact cast_ZExt_no_unwind srcTy dstTy input model
  | SExt => exact cast_SExt_no_unwind srcTy dstTy input model
  | FPTrunc => exact cast_FPTrunc_no_unwind srcTy dstTy input model
  | FPExt => exact cast_FPExt_no_unwind srcTy dstTy input model
  | FPToUI => exact cast_FPToUI_no_unwind srcTy dstTy input model
  | FPToSI => exact cast_FPToSI_no_unwind srcTy dstTy input model
  | UIToFP => exact cast_UIToFP_no_unwind srcTy dstTy input model
  | SIToFP => exact cast_SIToFP_no_unwind srcTy dstTy input model
  | PtrToInt => exact cast_PtrToInt_no_unwind srcTy dstTy input model
  | IntToPtr => exact cast_IntToPtr_no_unwind srcTy dstTy input model
  | Bitcast => exact cast_Bitcast_no_unwind srcTy dstTy input model
  | PtrToPtr => exact cast_PtrToPtr_no_unwind srcTy dstTy input model
  | Transmute => exact cast_Transmute_no_unwind srcTy dstTy input model
  | ReifyFnPointer => exact cast_ReifyFnPointer_no_unwind srcTy dstTy input model
  | FPToSISat => exact cast_FPToSISat_no_unwind srcTy dstTy input model
  | FPToUISat => exact cast_FPToUISat_no_unwind srcTy dstTy input model


private theorem ite_cast_safe {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Sem α) (yesSafe : CallCheckNoUnwind yes) (noSafe : CallCheckNoUnwind no) :
    CallCheckNoUnwind (if condition then yes else no) := by
  split <;> assumption

/-- Every service, including arbitrary cached static refusals, has the
intrinsic checked compiler error domain. No context premise is needed. -/
private theorem cast_service_query_no_unwind (service : AggregateMemory.Service) (ty : Ty) :
    ExceptNoUnwind (service.query ty) :=
  DecodeFrameExit.no_unwind (fun _ => True) _ ((block_result_frame_iff _ _).1
    ((AggregateMemory.Service.error_policy BlockDecodeError (fun _ => True.intro)
      (fun _ => True.intro) service ty).1))

private theorem context_reify_item_no_unwind (ctx : EvalContext) (source : FuncId)
    (signature : FuncTyId) (operand : ValueId) :
    CallCheckNoUnwind (α := InstrResult) (do
      let value ← Sem.lookupValue operand
      Sem.rejectPartial value "ReifyFnPointer"
      match value with
      | .fnItem held =>
        if held != source then Sem.throwTypeError "ReifyFnPointer: item identity differs from source type"
        let declaration ← Sem.fromMemoryExcept (functionItemDeclaration ctx source)
        if declaration.signatureId != signature then
          Sem.throwTypeError "ReifyFnPointer: destination signature differs from item declaration"
        pure (.value (some (← Sem.bindFresh (.fnDef signature source))))
      | _ => Sem.throwTypeError "ReifyFnPointer: source is not a nominal function item") := by
  refine CallCheckNoUnwind.bind _ _ (lookup_safe operand) (fun value => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe value _) (fun _ => ?_)
  split
  · split
    · exact type_safe "ReifyFnPointer: item identity differs from source type"
    · try simp only [pure_bind]
      refine CallCheckNoUnwind.bind _ _ (lift_validation_no_unwind _ (function_item_declaration_no_unwind ctx source)) (fun declaration => ?_)
      split
      · exact type_safe "ReifyFnPointer: destination signature differs from item declaration"
      · try simp only [pure_bind]
        exact CallCheckNoUnwind.bind _ _ (fresh_safe _) (fun _ => pure_safe _)
  · exact type_safe "ReifyFnPointer: source is not a nominal function item"

/-- Source layout queries and byte encoding/decoding are pure computations.
    This leaf preserves the complete image and every refusal without reducing
    any source plan or recursive codec inside the freshness proof. -/
private theorem context_item_byte_cast_no_unwind (ctx : EvalContext) (source destination : Ty)
    (operand : ValueId) :
    CallCheckNoUnwind (α := InstrResult) (do
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
      pure (.value (some (← Sem.bindFresh result)))) := by
  cases servicePresent : ctx.memoryService with
  | none => exact type_safe "FnItem cast: original source layouts are absent"
  | some service =>
    simp only [servicePresent, pure_bind]
    split
    · exact type_safe "FnItem cast: source layout target differs from evaluator target"
    · try simp only [pure_bind]
      refine CallCheckNoUnwind.bind _ _ (lift_validation_no_unwind _ (cast_service_query_no_unwind service source)) (fun sourcePlan => ?_)
      refine CallCheckNoUnwind.bind _ _ (lift_validation_no_unwind _ (cast_service_query_no_unwind service destination)) (fun destinationPlan => ?_)
      split
      · exact type_safe "FnItem cast: byte extents differ"
      · try simp only [pure_bind]
        refine CallCheckNoUnwind.bind _ _ (lookup_safe operand) (fun value => ?_)
        refine CallCheckNoUnwind.bind _ _ (reject_safe value _) (fun _ => ?_)
        refine CallCheckNoUnwind.bind _ _ (lift_validation_no_unwind _ (aggregate_encode_no_unwind _ _ _ _ _)) (fun image => ?_)
        refine CallCheckNoUnwind.bind _ _ get_safe (fun state => ?_)
        refine CallCheckNoUnwind.bind _ _ (lift_validation_no_unwind _ (DecodeFrameExit.no_unwind _ _ (aggregate_decode_frame_exit _ _ _ _ _))) (fun result => ?_)
        exact CallCheckNoUnwind.bind _ _ (fresh_safe result) (fun _ => pure_safe _)

theorem contextual_cast_no_unwind (ctx : EvalContext) (op : CastOp) (srcTy dstTy : Ty) (operand : ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.Cast op srcTy dstTy operand)) := by
  cases op
  case ReifyFnPointer =>
    cases srcTy
    case FnItem source =>
      cases dstTy
      case Func signature => exact context_reify_item_no_unwind ctx source signature operand
      all_goals
        simp only [stepInstWithContext]
        exact ite_cast_safe _ _ _ (context_item_byte_cast_no_unwind ctx _ _ operand)
          (CallCheckNoUnwind.bind _ _ (semCast_no_unwind _ _ _ _ _) (fun _ => pure_safe _))
    all_goals
      simp only [stepInstWithContext]
      exact ite_cast_safe _ _ _ (context_item_byte_cast_no_unwind ctx _ _ operand)
        (CallCheckNoUnwind.bind _ _ (semCast_no_unwind _ _ _ _ _) (fun _ => pure_safe _))
  all_goals
    simp only [stepInstWithContext]
    exact ite_cast_safe _ _ _ (context_item_byte_cast_no_unwind ctx _ _ operand)
      (CallCheckNoUnwind.bind _ _ (semCast_no_unwind _ _ _ _ _) (fun _ => pure_safe _))

end TrustIr.FrameLifetime
