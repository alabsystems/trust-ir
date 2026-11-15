-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshStep

namespace TrustIr.SSAFreshInstructions
open SSAFreshFrames SSAFreshStep

theorem ite_fresh {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Sem α) (yesFresh : KeepsFresh yes) (noFresh : KeepsFresh no) :
    KeepsFresh (if condition then yes else no) := by
  split <;> assumption

theorem except_fresh {α β : Type} (result : Except SemError α) (next : α → Sem β)
    (nextFresh : ∀ value, KeepsFresh (next value)) :
    KeepsFresh (match result with | .ok value => next value | .error error => throw error) := by
  cases result with
  | error error => exact throw_fresh _
  | ok value => exact nextFresh value

theorem rejectPartial_fresh (value : Value) (op : String) :
    KeepsFresh (Sem.rejectPartial value op) := by
  cases value <;> first | exact pure_fresh _ | exact throw_fresh _

theorem rejectPoisonValues_fresh (values : List Value) (op : String) :
    KeepsFresh (Sem.rejectPoisonValues values op) := by
  unfold Sem.rejectPoisonValues
  exact ite_fresh _ _ _ (throw_fresh _) (pure_fresh _)

theorem bindFreshPair_fresh (first second : Value) :
    KeepsFresh (Sem.bindFreshPair first second) := by
  unfold Sem.bindFreshPair
  exact bind_fresh _ _ (bindFresh_fresh first)
    (fun _ => bind_fresh _ _ (bindFresh_fresh second) (fun _ => pure_fresh _))

theorem nextFloatZeroChoice_fresh : KeepsFresh Sem.nextFloatZeroChoice := by
  intro state result fresh run
  change Except.ok (state.floatZeroChoices.choose state.floatZeroChoiceCursor,
    { state with floatZeroChoiceCursor := state.floatZeroChoiceCursor + 1 }) = Except.ok result at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact sameSSA_fresh state _ fresh rfl rfl

theorem addrOfInt_fresh (op : String) (width : Nat) (value : Int) (model : ByteModel) :
    KeepsFresh (Sem.addrOfInt op width value model) := by
  unfold Sem.addrOfInt
  apply ite_fresh
  · cases model with
    | le64 => exact pure_fresh _
    | le32 => exact ite_fresh _ _ _ (pure_fresh _) (throw_fresh _)
  · exact throw_fresh _

theorem bindPointerInteger_fresh (op : String) (ty : Ty) (address : Nat) (model : ByteModel) :
    KeepsFresh (Sem.bindPointerInteger op ty address model) := by
  unfold Sem.bindPointerInteger
  cases getTyWidth ty model with
  | ok width =>
    simp only [pure_bind]
    exact ite_fresh _ _ _ (bindFresh_fresh _) (throw_fresh _)
  | error error =>
    exact bind_fresh _ _ (throw_fresh error)
      (fun _ => ite_fresh _ _ _ (bindFresh_fresh _) (throw_fresh _))

theorem bindPointerIntegerWithProvenance_fresh (op : String) (ty : Ty) (address : Nat)
    (provenance : Option AllocId) (model : ByteModel) :
    KeepsFresh (Sem.bindPointerIntegerWithProvenance op ty address provenance model) := by
  cases provenance with
  | some allocation => exact bindPointerInteger_fresh op ty address model
  | none =>
    unfold Sem.bindPointerIntegerWithProvenance
    cases getTyWidth ty model with
    | ok width =>
      simp only [pure_bind]
      exact ite_fresh _ _ _ (bindFresh_fresh _) (throw_fresh _)
    | error error =>
      exact bind_fresh _ _ (throw_fresh error)
        (fun _ => ite_fresh _ _ _ (bindFresh_fresh _) (throw_fresh _))


private theorem except_bindFresh_fresh {α : Type} (result : Except SemError α)
    (value : α → Value) :
    KeepsFresh (match result with
      | .ok result => Sem.bindFresh (value result)
      | .error error => throw error) :=
  except_fresh result _ (fun _ => bindFresh_fresh _)

private theorem except_bindPair_fresh {α : Type} (result : Except SemError α)
    (first second : α → Value) :
    KeepsFresh (match result with
      | .ok result => Sem.bindFreshPair (first result) (second result)
      | .error error => throw error) :=
  except_fresh result _ (fun _ => bindFreshPair_fresh _ _)

theorem setFrameState_fresh (openLineages : List Nat) (nextLineage : Nat) :
    KeepsFresh (Sem.setFrameState openLineages nextLineage) := by
  intro state result fresh run
  change Except.ok ((), { state with openFrameLineages := openLineages, nextFrameLineage := nextLineage }) = .ok result at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact sameSSA_fresh state _ fresh rfl rfl

local macro "fresh_leaves" : tactic =>
  `(tactic| repeat (first
    | exact bindFresh_fresh _
    | exact bindFreshPair_fresh _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact setFrameState_fresh _ _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact rejectPoisonValues_fresh _ _
    | exact nextFloatZeroChoice_fresh
    | exact addrOfInt_fresh _ _ _ _
    | exact bindPointerInteger_fresh _ _ _ _
    | exact bindPointerIntegerWithProvenance_fresh _ _ _ _ _
    | exact except_bindFresh_fresh _ _
    | exact except_bindPair_fresh _ _ _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

private theorem cast_Trunc_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .Trunc srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_ZExt_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .ZExt srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_SExt_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .SExt srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_FPTrunc_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .FPTrunc srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_FPExt_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .FPExt srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_FPToUI_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .FPToUI srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_FPToSI_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .FPToSI srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_UIToFP_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .UIToFP srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_SIToFP_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .SIToFP srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_PtrToInt_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .PtrToInt srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_IntToPtr_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .IntToPtr srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_Bitcast_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .Bitcast srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_PtrToPtr_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .PtrToPtr srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_Transmute_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .Transmute srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_ReifyFnPointer_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .ReifyFnPointer srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_FPToSISat_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .FPToSISat srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

private theorem cast_FPToUISat_fresh (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast .FPToUISat srcTy dstTy input model) := by
  unfold semCast
  refine bind_fresh _ _ (lookup_fresh input) (fun operand => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> fresh_leaves

theorem semCast_fresh (op : CastOp) (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsFresh (semCast op srcTy dstTy input model) := by
  cases op with
  | Trunc => exact cast_Trunc_fresh srcTy dstTy input model
  | ZExt => exact cast_ZExt_fresh srcTy dstTy input model
  | SExt => exact cast_SExt_fresh srcTy dstTy input model
  | FPTrunc => exact cast_FPTrunc_fresh srcTy dstTy input model
  | FPExt => exact cast_FPExt_fresh srcTy dstTy input model
  | FPToUI => exact cast_FPToUI_fresh srcTy dstTy input model
  | FPToSI => exact cast_FPToSI_fresh srcTy dstTy input model
  | UIToFP => exact cast_UIToFP_fresh srcTy dstTy input model
  | SIToFP => exact cast_SIToFP_fresh srcTy dstTy input model
  | PtrToInt => exact cast_PtrToInt_fresh srcTy dstTy input model
  | IntToPtr => exact cast_IntToPtr_fresh srcTy dstTy input model
  | Bitcast => exact cast_Bitcast_fresh srcTy dstTy input model
  | PtrToPtr => exact cast_PtrToPtr_fresh srcTy dstTy input model
  | Transmute => exact cast_Transmute_fresh srcTy dstTy input model
  | ReifyFnPointer => exact cast_ReifyFnPointer_fresh srcTy dstTy input model
  | FPToSISat => exact cast_FPToSISat_fresh srcTy dstTy input model
  | FPToUISat => exact cast_FPToUISat_fresh srcTy dstTy input model

theorem semBinOpDeterministic_fresh (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (semBinOpDeterministic op ty lhs rhs) := by
  unfold semBinOpDeterministic
  fresh_leaves

theorem semBoolBinOpInst_fresh (op : BinOp) (lhs rhs : ValueId) :
    KeepsFresh (semBoolBinOpInst op lhs rhs) := by
  unfold semBoolBinOpInst
  fresh_leaves

theorem semUnOp_fresh (op : UnOp) (ty : Ty) (input : ValueId) :
    KeepsFresh (semUnOp op ty input) := by
  unfold semUnOp
  fresh_leaves

theorem semOverflow_fresh (op : OverflowOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (semOverflow op ty lhs rhs) := by
  unfold semOverflow
  fresh_leaves

theorem semICmpInst_fresh (op : ICmpOp) (ty : Ty) (lhs rhs : ValueId) (model : ByteModel) :
    KeepsFresh (semICmpInst op ty lhs rhs model) := by
  unfold semICmpInst
  fresh_leaves

theorem semFCmpInst_fresh (op : FCmpOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (semFCmpInst op ty lhs rhs) := by
  unfold semFCmpInst
  fresh_leaves

theorem frameHandle_fresh (frame : ValueId) (op : String) :
    KeepsFresh (Sem.frameHandle frame op) := by
  unfold Sem.frameHandle
  fresh_leaves

theorem semOpenFrame_fresh (definition : BindingFrameDef) :
    KeepsFresh (semOpenFrame definition) := by
  unfold semOpenFrame
  fresh_leaves

theorem semBindSlot_fresh (frame : ValueId) (slot : Nat) (value : ValueId) :
    KeepsFresh (semBindSlot frame slot value) := by
  unfold semBindSlot Sem.frameHandle
  fresh_leaves

theorem semLoadSlot_fresh (frame : ValueId) (slot : Nat) (ty : Ty) :
    KeepsFresh (semLoadSlot frame slot ty) := by
  unfold semLoadSlot Sem.frameHandle
  fresh_leaves

theorem semCloseFrame_fresh (frame : ValueId) :
    KeepsFresh (semCloseFrame frame) := by
  unfold semCloseFrame Sem.frameHandle
  fresh_leaves

theorem semBr_fresh (target : BlockId) (args : List ValueId) :
    KeepsFresh (semBr target args) := by
  unfold semBr
  fresh_leaves

theorem semCondBr_fresh (condition : ValueId) (yes : BlockId) (yesArgs : List ValueId) (no : BlockId) (noArgs : List ValueId) :
    KeepsFresh (semCondBr condition yes yesArgs no noArgs) := by
  unfold semCondBr
  fresh_leaves

theorem semReturn_fresh (values : List ValueId) :
    KeepsFresh (semReturn values) := by
  unfold semReturn
  fresh_leaves

theorem semFloatMinMaxAt_fresh (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    KeepsFresh (semFloatMinMaxAt op ty lhs rhs) := by
  unfold semFloatMinMaxAt
  fresh_leaves

local macro "float_leaves" : tactic =>
  `(tactic| repeat (first
    | exact semFloatMinMaxAt_fresh _ _ _ _
    | exact bindFresh_fresh _
    | exact bindFreshPair_fresh _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact setFrameState_fresh _ _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact rejectPoisonValues_fresh _ _
    | exact nextFloatZeroChoice_fresh
    | exact addrOfInt_fresh _ _ _ _
    | exact bindPointerInteger_fresh _ _ _ _
    | exact bindPointerIntegerWithProvenance_fresh _ _ _ _ _
    | exact except_bindFresh_fresh _ _
    | exact except_bindPair_fresh _ _ _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semFloatMinMaxScalarValue_fresh (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    KeepsFresh (semFloatMinMaxScalarValue op ty lhs rhs) := by
  unfold semFloatMinMaxScalarValue
  float_leaves

theorem semFloatMinMaxLanes_fresh (op : BinOp) (ty : Ty) (lhs rhs : List Value) :
    KeepsFresh (semFloatMinMaxLanes op ty lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact pure_fresh _ | exact throw_fresh _
  | cons left lefts ih =>
    cases rhs with
    | nil => exact throw_fresh _
    | cons right rights =>
      simp only [semFloatMinMaxLanes]
      exact bind_fresh _ _ (semFloatMinMaxScalarValue_fresh op ty left right)
        (fun _ => bind_fresh _ _ (ih rights) (fun _ => pure_fresh _))

local macro "float_vector_leaves" : tactic =>
  `(tactic| repeat (first
    | exact semFloatMinMaxScalarValue_fresh _ _ _ _
    | exact semFloatMinMaxLanes_fresh _ _ _ _
    | exact semFloatMinMaxAt_fresh _ _ _ _
    | exact bindFresh_fresh _
    | exact bindFreshPair_fresh _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact setFrameState_fresh _ _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact rejectPoisonValues_fresh _ _
    | exact nextFloatZeroChoice_fresh
    | exact addrOfInt_fresh _ _ _ _
    | exact bindPointerInteger_fresh _ _ _ _
    | exact bindPointerIntegerWithProvenance_fresh _ _ _ _ _
    | exact except_bindFresh_fresh _ _
    | exact except_bindPair_fresh _ _ _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semFloatMinMaxValues_fresh (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    KeepsFresh (semFloatMinMaxValues op ty lhs rhs) := by
  unfold semFloatMinMaxValues
  float_vector_leaves

theorem semFloatMinMax_fresh (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (semFloatMinMax op ty lhs rhs) := by
  unfold semFloatMinMax
  exact bind_fresh _ _ (lookup_fresh lhs) (fun left =>
    bind_fresh _ _ (lookup_fresh rhs) (fun right =>
      bind_fresh _ _ (semFloatMinMaxValues_fresh op ty left right) bindFresh_fresh))

theorem semBinOp_fresh (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (semBinOp op ty lhs rhs) := by
  unfold semBinOp
  exact ite_fresh _ _ _ (semFloatMinMax_fresh op ty lhs rhs)
    (semBinOpDeterministic_fresh op ty lhs rhs)

theorem lookupLanes_fresh (ids : List ValueId) : KeepsFresh (lookupLanes ids) := by
  induction ids with
  | nil => exact pure_fresh _
  | cons id rest ih =>
    exact bind_fresh _ _ (lookup_fresh id) (fun value =>
      bind_fresh _ _ (rejectPartial_fresh value "MakeAggregate") (fun _ =>
        bind_fresh _ _ ih (fun _ => pure_fresh _)))

local macro "aggregate_leaves" : tactic =>
  `(tactic| repeat (first
    | exact lookupLanes_fresh _
    | exact bindFresh_fresh _
    | exact bindFreshPair_fresh _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact setFrameState_fresh _ _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact rejectPoisonValues_fresh _ _
    | exact nextFloatZeroChoice_fresh
    | exact addrOfInt_fresh _ _ _ _
    | exact bindPointerInteger_fresh _ _ _ _
    | exact bindPointerIntegerWithProvenance_fresh _ _ _ _ _
    | exact except_bindFresh_fresh _ _
    | exact except_bindPair_fresh _ _ _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semExtractField_fresh (ty : Ty) (value : ValueId) (field : Nat) :
    KeepsFresh (semExtractField ty value field) := by
  unfold semExtractField
  aggregate_leaves

theorem semInsertField_fresh (ty : Ty) (value : ValueId) (field : Nat) (replacement : ValueId) :
    KeepsFresh (semInsertField ty value field replacement) := by
  unfold semInsertField
  aggregate_leaves

theorem semMakeAggregate_fresh (ty : Ty) (variant : Option Nat) (fields : List ValueId) :
    KeepsFresh (semMakeAggregate ty variant fields) := by
  unfold semMakeAggregate
  aggregate_leaves

theorem semArraySplat_fresh (ty : Ty) (value : ValueId) :
    KeepsFresh (semArraySplat ty value) := by
  unfold semArraySplat
  aggregate_leaves

theorem semSeqMapAddK_fresh (ty : Ty) (value : ValueId) (amount : Nat) :
    KeepsFresh (semSeqMapAddK ty value amount) := by
  unfold semSeqMapAddK
  aggregate_leaves

theorem semSeqMapNot_fresh (ty : Ty) (value : ValueId) :
    KeepsFresh (semSeqMapNot ty value) := by
  unfold semSeqMapNot
  aggregate_leaves

theorem context_elementIndex_fresh (ctx : EvalContext) (id : ValueId) (value : Value) :
    KeepsFresh (EvalContext.elementIndex ctx id value) := by
  unfold EvalContext.elementIndex
  dsimp only
  aggregate_leaves

theorem semExtractElementUsing_fresh (indexOf : Value → Sem Nat)
    (ty : Ty) (array index : ValueId) (indexFresh : ∀ value, KeepsFresh (indexOf value)) :
    KeepsFresh (semExtractElementUsing indexOf ty array index) := by
  unfold semExtractElementUsing
  refine bind_fresh _ _ (lookup_fresh array) (fun heldArray => ?_)
  refine bind_fresh _ _ (lookup_fresh index) (fun heldIndex => ?_)
  refine bind_fresh _ _ (indexFresh heldIndex) (fun position => ?_)
  aggregate_leaves

theorem semInsertElementUsing_fresh (indexOf : Value → Sem Nat)
    (ty : Ty) (array index value : ValueId) (indexFresh : ∀ value, KeepsFresh (indexOf value)) :
    KeepsFresh (semInsertElementUsing indexOf ty array index value) := by
  unfold semInsertElementUsing
  refine bind_fresh _ _ (lookup_fresh array) (fun heldArray => ?_)
  refine bind_fresh _ _ (lookup_fresh index) (fun heldIndex => ?_)
  refine bind_fresh _ _ (lookup_fresh value) (fun heldValue => ?_)
  refine bind_fresh _ _ (indexFresh heldIndex) (fun position => ?_)
  aggregate_leaves

theorem semExtractElement_fresh (ty : Ty) (array index : ValueId) :
    KeepsFresh (semExtractElement ty array index) := by
  unfold semExtractElement
  apply semExtractElementUsing_fresh
  intro value
  aggregate_leaves

theorem semInsertElement_fresh (ty : Ty) (array index value : ValueId) :
    KeepsFresh (semInsertElement ty array index value) := by
  unfold semInsertElement
  apply semInsertElementUsing_fresh
  intro value
  aggregate_leaves

end TrustIr.SSAFreshInstructions
