-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameBodyValidity

namespace TrustIr.FrameLifetime.HistoryEffects

/-- The live-lineage table and next never-reused identity counter. -/
def fields (state : MachineState) : List Nat × Nat :=
  (state.openFrameLineages,state.nextFrameLineage)

/-- Exact successful retention of history, independent of input validity.
OpenFrame and CloseFrame instead satisfy the weaker HistoryExtends relation. -/
def KeepsHistory {α : Type} (action : Sem α) : Prop :=
  ∀ state result, Sem.run action state = .ok result → fields result.2 = fields state

theorem pure_history {α : Type} (value : α) : KeepsHistory (pure value : Sem α) := by
  intro state result run
  cases run
  rfl

theorem throw_history {α : Type} (error : SemError) : KeepsHistory (throw error : Sem α) := by
  intro state result run
  cases run

theorem throwTypeError_history {α : Type} (message : String) : KeepsHistory (Sem.throwTypeError message : Sem α) :=
  throw_history _
theorem throwUB_history {α : Type} (message : String) : KeepsHistory (Sem.throwUB message : Sem α) :=
  throw_history _
theorem throwUnsupported_history {α : Type} (feature : UnsupportedFeature) (message : String) :
    KeepsHistory (Sem.throwUnsupported feature message : Sem α) := throw_history _

theorem bind_history {α β : Type} (action : Sem α) (next : α → Sem β)
    (first : KeepsHistory action) (rest : ∀ value, KeepsHistory (next value)) :
    KeepsHistory (action >>= next) := by
  intro state result run
  rw [Sem.run_bind] at run
  cases executed : Sem.run action state with
  | error error => rw [executed] at run; cases run
  | ok pair =>
    have tail : Sem.run (next pair.1) pair.2 = .ok result := by simpa [executed] using run
    exact (rest pair.1 pair.2 result tail).trans (first state pair executed)

theorem get_history : KeepsHistory Sem.getState := by
  intro state result run
  cases run
  rfl

theorem lookup_history (id : ValueId) : KeepsHistory (Sem.lookupValue id) := by
  intro state result run
  cases lookup : state.lookupValue id with
  | none =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, Sem.throwTypeError, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some value =>
    have exactRun : Sem.run (Sem.lookupValue id) state = .ok (value,state) := by
      simp [Sem.lookupValue, Sem.run, Sem.getState, lookup, StateT.run,
        StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure]
    rw [exactRun] at run
    cases run
    rfl

theorem bindFresh_history (value : Value) : KeepsHistory (Sem.bindFresh value) := by
  intro state result run
  change Except.ok (state.bindValue value) = .ok result at run
  cases run
  rfl

theorem mapM_history {α β : Type} (action : α → Sem β) (values : List α)
    (preserve : ∀ value, KeepsHistory (action value)) : KeepsHistory (values.mapM action) := by
  induction values with
  | nil => exact pure_history _
  | cons first rest ih =>
    rw [List.mapM_cons]
    exact bind_history _ _ (preserve first) (fun _ => bind_history _ _ ih (fun _ => pure_history _))

theorem KeepsHistory.extends {α : Type} {action : Sem α} (keep : KeepsHistory action)
    (state final : MachineState) (value : α) (run : Sem.run action state = .ok (value,final)) :
    HistoryExtends state final := by
  have same := keep state (value,final) run
  have table := congrArg Prod.fst same
  have counter := congrArg Prod.snd same
  change final.openFrameLineages = state.openFrameLineages at table
  change final.nextFrameLineage = state.nextFrameLineage at counter
  exact ⟨by change state.nextFrameLineage ≤ final.nextFrameLineage; rw [counter]; exact Nat.le_refl _,
    fun _ _ closed => by change final.openFrameLineages.contains _ = false; rw [table]; exact closed⟩

theorem ite_history {α : Type} (condition : Prop) [Decidable condition]
    (yes no : Sem α) (yesHistory : KeepsHistory yes) (noHistory : KeepsHistory no) :
    KeepsHistory (if condition then yes else no) := by
  split <;> assumption

theorem except_history {α β : Type} (result : Except SemError α) (next : α → Sem β)
    (nextHistory : ∀ value, KeepsHistory (next value)) :
    KeepsHistory (match result with | .ok value => next value | .error error => throw error) := by
  cases result with
  | error error => exact throw_history _
  | ok value => exact nextHistory value

theorem rejectPartial_history (value : Value) (op : String) :
    KeepsHistory (Sem.rejectPartial value op) := by
  cases value <;> first | exact pure_history _ | exact throw_history _

theorem rejectPoisonValues_history (values : List Value) (op : String) :
    KeepsHistory (Sem.rejectPoisonValues values op) := by
  unfold Sem.rejectPoisonValues
  exact ite_history _ _ _ (throw_history _) (pure_history _)

theorem bindFreshPair_history (first second : Value) :
    KeepsHistory (Sem.bindFreshPair first second) := by
  unfold Sem.bindFreshPair
  exact bind_history _ _ (bindFresh_history first)
    (fun _ => bind_history _ _ (bindFresh_history second) (fun _ => pure_history _))

theorem nextFloatZeroChoice_history : KeepsHistory Sem.nextFloatZeroChoice := by
  intro state result run
  change Except.ok (state.floatZeroChoices.choose state.floatZeroChoiceCursor,
    { state with floatZeroChoiceCursor := state.floatZeroChoiceCursor + 1 }) = Except.ok result at run
  cases run
  rfl

theorem addrOfInt_history (op : String) (width : Nat) (value : Int) (model : ByteModel) :
    KeepsHistory (Sem.addrOfInt op width value model) := by
  unfold Sem.addrOfInt
  apply ite_history
  · cases model with
    | le64 => exact pure_history _
    | le32 => exact ite_history _ _ _ (pure_history _) (throw_history _)
  · exact throw_history _

theorem bindPointerInteger_history (op : String) (ty : Ty) (address : Nat) (model : ByteModel) :
    KeepsHistory (Sem.bindPointerInteger op ty address model) := by
  unfold Sem.bindPointerInteger
  cases getTyWidth ty model with
  | ok width =>
    simp only [pure_bind]
    exact ite_history _ _ _ (bindFresh_history _) (throw_history _)
  | error error =>
    exact bind_history _ _ (throw_history error)
      (fun _ => ite_history _ _ _ (bindFresh_history _) (throw_history _))

theorem bindPointerIntegerWithProvenance_history (op : String) (ty : Ty) (address : Nat)
    (provenance : Option AllocId) (model : ByteModel) :
    KeepsHistory (Sem.bindPointerIntegerWithProvenance op ty address provenance model) := by
  cases provenance with
  | some allocation => exact bindPointerInteger_history op ty address model
  | none =>
    unfold Sem.bindPointerIntegerWithProvenance
    cases getTyWidth ty model with
    | ok width =>
      simp only [pure_bind]
      exact ite_history _ _ _ (bindFresh_history _) (throw_history _)
    | error error =>
      exact bind_history _ _ (throw_history error)
        (fun _ => ite_history _ _ _ (bindFresh_history _) (throw_history _))


private theorem except_bindFresh_history {α : Type} (result : Except SemError α)
    (value : α → Value) :
    KeepsHistory (match result with
      | .ok result => Sem.bindFresh (value result)
      | .error error => throw error) :=
  except_history result _ (fun _ => bindFresh_history _)

private theorem except_bindPair_history {α : Type} (result : Except SemError α)
    (first second : α → Value) :
    KeepsHistory (match result with
      | .ok result => Sem.bindFreshPair (first result) (second result)
      | .error error => throw error) :=
  except_history result _ (fun _ => bindFreshPair_history _ _)

theorem targetAddress_history (model : ByteModel) (op : String) (address : Nat) :
    KeepsHistory (Sem.targetAddress model op address) := by
  cases model with
  | le64 => exact pure_history _
  | le32 => exact ite_history _ _ _ (pure_history _) (throw_history _)

local macro "history_leaves" : tactic =>
  `(tactic| repeat (first
    | exact bindFresh_history _
    | exact bindFreshPair_history _ _
    | exact pure_history _
    | exact throw_history _
    | exact get_history
    | exact targetAddress_history _ _ _
    | exact lookup_history _
    | exact rejectPartial_history _ _
    | exact rejectPoisonValues_history _ _
    | exact nextFloatZeroChoice_history
    | exact addrOfInt_history _ _ _ _
    | exact bindPointerInteger_history _ _ _ _
    | exact bindPointerIntegerWithProvenance_history _ _ _ _ _
    | exact except_bindFresh_history _ _
    | exact except_bindPair_history _ _ _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

private theorem cast_Trunc_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .Trunc srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_ZExt_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .ZExt srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_SExt_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .SExt srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_FPTrunc_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .FPTrunc srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_FPExt_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .FPExt srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_FPToUI_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .FPToUI srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_FPToSI_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .FPToSI srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_UIToFP_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .UIToFP srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_SIToFP_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .SIToFP srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_PtrToInt_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .PtrToInt srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_IntToPtr_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .IntToPtr srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_Bitcast_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .Bitcast srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_PtrToPtr_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .PtrToPtr srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_Transmute_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .Transmute srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_ReifyFnPointer_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .ReifyFnPointer srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_FPToSISat_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .FPToSISat srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

private theorem cast_FPToUISat_history (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast .FPToUISat srcTy dstTy input model) := by
  unfold semCast
  refine bind_history _ _ (lookup_history input) (fun operand => ?_)
  refine bind_history _ _ (rejectPartial_history operand "Cast") (fun _ => ?_)
  cases operand <;> simp only [] <;> history_leaves

theorem semCast_history (op : CastOp) (srcTy dstTy : Ty) (input : ValueId) (model : ByteModel) :
    KeepsHistory (semCast op srcTy dstTy input model) := by
  cases op with
  | Trunc => exact cast_Trunc_history srcTy dstTy input model
  | ZExt => exact cast_ZExt_history srcTy dstTy input model
  | SExt => exact cast_SExt_history srcTy dstTy input model
  | FPTrunc => exact cast_FPTrunc_history srcTy dstTy input model
  | FPExt => exact cast_FPExt_history srcTy dstTy input model
  | FPToUI => exact cast_FPToUI_history srcTy dstTy input model
  | FPToSI => exact cast_FPToSI_history srcTy dstTy input model
  | UIToFP => exact cast_UIToFP_history srcTy dstTy input model
  | SIToFP => exact cast_SIToFP_history srcTy dstTy input model
  | PtrToInt => exact cast_PtrToInt_history srcTy dstTy input model
  | IntToPtr => exact cast_IntToPtr_history srcTy dstTy input model
  | Bitcast => exact cast_Bitcast_history srcTy dstTy input model
  | PtrToPtr => exact cast_PtrToPtr_history srcTy dstTy input model
  | Transmute => exact cast_Transmute_history srcTy dstTy input model
  | ReifyFnPointer => exact cast_ReifyFnPointer_history srcTy dstTy input model
  | FPToSISat => exact cast_FPToSISat_history srcTy dstTy input model
  | FPToUISat => exact cast_FPToUISat_history srcTy dstTy input model

theorem semBinOpDeterministic_history (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsHistory (semBinOpDeterministic op ty lhs rhs) := by
  unfold semBinOpDeterministic
  history_leaves

theorem semBoolBinOpInst_history (op : BinOp) (lhs rhs : ValueId) :
    KeepsHistory (semBoolBinOpInst op lhs rhs) := by
  unfold semBoolBinOpInst
  history_leaves

theorem semUnOp_history (op : UnOp) (ty : Ty) (input : ValueId) :
    KeepsHistory (semUnOp op ty input) := by
  unfold semUnOp
  history_leaves

theorem semOverflow_history (op : OverflowOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsHistory (semOverflow op ty lhs rhs) := by
  unfold semOverflow
  history_leaves

theorem semICmpInst_history (op : ICmpOp) (ty : Ty) (lhs rhs : ValueId) (model : ByteModel) :
    KeepsHistory (semICmpInst op ty lhs rhs model) := by
  unfold semICmpInst
  history_leaves

theorem semFCmpInst_history (op : FCmpOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsHistory (semFCmpInst op ty lhs rhs) := by
  unfold semFCmpInst
  history_leaves

theorem frameHandle_history (frame : ValueId) (op : String) :
    KeepsHistory (Sem.frameHandle frame op) := by
  unfold Sem.frameHandle
  history_leaves

theorem semBindSlot_history (frame : ValueId) (slot : Nat) (value : ValueId) :
    KeepsHistory (semBindSlot frame slot value) := by
  unfold semBindSlot Sem.frameHandle
  history_leaves

theorem semLoadSlot_history (frame : ValueId) (slot : Nat) (ty : Ty) :
    KeepsHistory (semLoadSlot frame slot ty) := by
  unfold semLoadSlot Sem.frameHandle
  history_leaves

theorem semBr_history (target : BlockId) (args : List ValueId) :
    KeepsHistory (semBr target args) := by
  unfold semBr
  history_leaves

theorem semCondBr_history (condition : ValueId) (yes : BlockId) (yesArgs : List ValueId) (no : BlockId) (noArgs : List ValueId) :
    KeepsHistory (semCondBr condition yes yesArgs no noArgs) := by
  unfold semCondBr
  history_leaves

theorem semReturn_history (values : List ValueId) :
    KeepsHistory (semReturn values) := by
  unfold semReturn
  history_leaves

theorem semFloatMinMaxAt_history (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    KeepsHistory (semFloatMinMaxAt op ty lhs rhs) := by
  unfold semFloatMinMaxAt
  history_leaves

local macro "float_leaves" : tactic =>
  `(tactic| repeat (first
    | exact semFloatMinMaxAt_history _ _ _ _
    | exact bindFresh_history _
    | exact bindFreshPair_history _ _
    | exact pure_history _
    | exact throw_history _
    | exact get_history
    | exact targetAddress_history _ _ _
    | exact lookup_history _
    | exact rejectPartial_history _ _
    | exact rejectPoisonValues_history _ _
    | exact nextFloatZeroChoice_history
    | exact addrOfInt_history _ _ _ _
    | exact bindPointerInteger_history _ _ _ _
    | exact bindPointerIntegerWithProvenance_history _ _ _ _ _
    | exact except_bindFresh_history _ _
    | exact except_bindPair_history _ _ _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semFloatMinMaxScalarValue_history (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    KeepsHistory (semFloatMinMaxScalarValue op ty lhs rhs) := by
  unfold semFloatMinMaxScalarValue
  float_leaves

theorem semFloatMinMaxLanes_history (op : BinOp) (ty : Ty) (lhs rhs : List Value) :
    KeepsHistory (semFloatMinMaxLanes op ty lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact pure_history _ | exact throw_history _
  | cons left lefts ih =>
    cases rhs with
    | nil => exact throw_history _
    | cons right rights =>
      simp only [semFloatMinMaxLanes]
      exact bind_history _ _ (semFloatMinMaxScalarValue_history op ty left right)
        (fun _ => bind_history _ _ (ih rights) (fun _ => pure_history _))

local macro "float_vector_leaves" : tactic =>
  `(tactic| repeat (first
    | exact semFloatMinMaxScalarValue_history _ _ _ _
    | exact semFloatMinMaxLanes_history _ _ _ _
    | exact semFloatMinMaxAt_history _ _ _ _
    | exact bindFresh_history _
    | exact bindFreshPair_history _ _
    | exact pure_history _
    | exact throw_history _
    | exact get_history
    | exact targetAddress_history _ _ _
    | exact lookup_history _
    | exact rejectPartial_history _ _
    | exact rejectPoisonValues_history _ _
    | exact nextFloatZeroChoice_history
    | exact addrOfInt_history _ _ _ _
    | exact bindPointerInteger_history _ _ _ _
    | exact bindPointerIntegerWithProvenance_history _ _ _ _ _
    | exact except_bindFresh_history _ _
    | exact except_bindPair_history _ _ _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semFloatMinMaxValues_history (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    KeepsHistory (semFloatMinMaxValues op ty lhs rhs) := by
  unfold semFloatMinMaxValues
  float_vector_leaves

theorem semFloatMinMax_history (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsHistory (semFloatMinMax op ty lhs rhs) := by
  unfold semFloatMinMax
  exact bind_history _ _ (lookup_history lhs) (fun left =>
    bind_history _ _ (lookup_history rhs) (fun right =>
      bind_history _ _ (semFloatMinMaxValues_history op ty left right) bindFresh_history))

theorem semBinOp_history (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsHistory (semBinOp op ty lhs rhs) := by
  unfold semBinOp
  exact ite_history _ _ _ (semFloatMinMax_history op ty lhs rhs)
    (semBinOpDeterministic_history op ty lhs rhs)

theorem lookupLanes_history (ids : List ValueId) : KeepsHistory (lookupLanes ids) := by
  induction ids with
  | nil => exact pure_history _
  | cons id rest ih =>
    exact bind_history _ _ (lookup_history id) (fun value =>
      bind_history _ _ (rejectPartial_history value "MakeAggregate") (fun _ =>
        bind_history _ _ ih (fun _ => pure_history _)))

local macro "aggregate_leaves" : tactic =>
  `(tactic| repeat (first
    | exact lookupLanes_history _
    | exact bindFresh_history _
    | exact bindFreshPair_history _ _
    | exact pure_history _
    | exact throw_history _
    | exact get_history
    | exact targetAddress_history _ _ _
    | exact lookup_history _
    | exact rejectPartial_history _ _
    | exact rejectPoisonValues_history _ _
    | exact nextFloatZeroChoice_history
    | exact addrOfInt_history _ _ _ _
    | exact bindPointerInteger_history _ _ _ _
    | exact bindPointerIntegerWithProvenance_history _ _ _ _ _
    | exact except_bindFresh_history _ _
    | exact except_bindPair_history _ _ _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semExtractField_history (ty : Ty) (value : ValueId) (field : Nat) :
    KeepsHistory (semExtractField ty value field) := by
  unfold semExtractField
  aggregate_leaves

theorem semInsertField_history (ty : Ty) (value : ValueId) (field : Nat) (replacement : ValueId) :
    KeepsHistory (semInsertField ty value field replacement) := by
  unfold semInsertField
  aggregate_leaves

theorem semMakeAggregate_history (ty : Ty) (variant : Option Nat) (fields : List ValueId) :
    KeepsHistory (semMakeAggregate ty variant fields) := by
  unfold semMakeAggregate
  aggregate_leaves

theorem semArraySplat_history (ty : Ty) (value : ValueId) :
    KeepsHistory (semArraySplat ty value) := by
  unfold semArraySplat
  aggregate_leaves

theorem semSeqMapAddK_history (ty : Ty) (value : ValueId) (amount : Nat) :
    KeepsHistory (semSeqMapAddK ty value amount) := by
  unfold semSeqMapAddK
  aggregate_leaves

theorem semSeqMapNot_history (ty : Ty) (value : ValueId) :
    KeepsHistory (semSeqMapNot ty value) := by
  unfold semSeqMapNot
  aggregate_leaves

theorem context_elementIndex_history (ctx : EvalContext) (id : ValueId) (value : Value) :
    KeepsHistory (EvalContext.elementIndex ctx id value) := by
  unfold EvalContext.elementIndex
  dsimp only
  aggregate_leaves

theorem semExtractElementUsing_history (indexOf : Value → Sem Nat)
    (ty : Ty) (array index : ValueId) (indexHistory : ∀ value, KeepsHistory (indexOf value)) :
    KeepsHistory (semExtractElementUsing indexOf ty array index) := by
  unfold semExtractElementUsing
  refine bind_history _ _ (lookup_history array) (fun heldArray => ?_)
  refine bind_history _ _ (lookup_history index) (fun heldIndex => ?_)
  refine bind_history _ _ (indexHistory heldIndex) (fun position => ?_)
  aggregate_leaves

theorem semInsertElementUsing_history (indexOf : Value → Sem Nat)
    (ty : Ty) (array index value : ValueId) (indexHistory : ∀ value, KeepsHistory (indexOf value)) :
    KeepsHistory (semInsertElementUsing indexOf ty array index value) := by
  unfold semInsertElementUsing
  refine bind_history _ _ (lookup_history array) (fun heldArray => ?_)
  refine bind_history _ _ (lookup_history index) (fun heldIndex => ?_)
  refine bind_history _ _ (lookup_history value) (fun heldValue => ?_)
  refine bind_history _ _ (indexHistory heldIndex) (fun position => ?_)
  aggregate_leaves

theorem semExtractElement_history (ty : Ty) (array index : ValueId) :
    KeepsHistory (semExtractElement ty array index) := by
  unfold semExtractElement
  apply semExtractElementUsing_history
  intro value
  aggregate_leaves

theorem semInsertElement_history (ty : Ty) (array index value : ValueId) :
    KeepsHistory (semInsertElement ty array index value) := by
  unfold semInsertElement
  apply semInsertElementUsing_history
  intro value
  aggregate_leaves


theorem semPtrData_history (ty : Ty) (operand : ValueId) (model : ByteModel) :
    KeepsHistory (semPtrData ty operand model) := by
  unfold semPtrData
  history_leaves

theorem semPtrMetadata_history (ty metadataTy : Ty) (operand : ValueId) (model : ByteModel) :
    KeepsHistory (semPtrMetadata ty metadataTy operand model) := by
  unfold semPtrMetadata
  history_leaves

theorem semPtrFromParts_history (ty metadataTy : Ty) (data metadata : ValueId) (model : ByteModel) :
    KeepsHistory (semPtrFromParts ty metadataTy data metadata model) := by
  unfold semPtrFromParts
  history_leaves

private theorem bare_extract_history (ty : Ty) (operand : ValueId) (field : Nat) (model : ByteModel) :
    KeepsHistory (stepInst (.ExtractField ty operand field) model) :=
  bind_history _ _ (semExtractField_history ty operand field) (fun _ => pure_history _)

private theorem bare_insert_history (ty : Ty) (operand rhs : ValueId) (field : Nat) (model : ByteModel) :
    KeepsHistory (stepInst (.InsertField ty operand field rhs) model) :=
  bind_history _ _ (semInsertField_history ty operand field rhs) (fun _ => pure_history _)

private theorem bare_splat_history (ty : Ty) (operand : ValueId) (model : ByteModel) :
    KeepsHistory (stepInst (.ArraySplat ty operand) model) :=
  bind_history _ _ (semArraySplat_history ty operand) (fun _ => pure_history _)

local macro "context_history_leaves" : tactic =>
  `(tactic| with_reducible (repeat' (first
    | exact bare_extract_history _ _ _ _
    | exact bare_insert_history _ _ _ _ _
    | exact bare_splat_history _ _ _
    | exact lookupLanes_history _
    | exact bindFresh_history _
    | exact pure_history _
    | exact throw_history _
    | exact throwTypeError_history _
    | exact throwUB_history _
    | exact throwUnsupported_history _ _
    | exact lookup_history _
    | exact rejectPartial_history _ _
    | exact mapM_history Sem.lookupValue _ lookup_history
    | (refine bind_history _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)))

theorem contextual_extract_history (ctx : EvalContext) (ty : Ty) (operand : ValueId) (field : Nat) :
    KeepsHistory (stepInstWithContext ctx (.ExtractField ty operand field)) := by
  unfold stepInstWithContext
  context_history_leaves

theorem contextual_insert_history (ctx : EvalContext) (ty : Ty) (operand rhs : ValueId) (field : Nat) :
    KeepsHistory (stepInstWithContext ctx (.InsertField ty operand field rhs)) := by
  unfold stepInstWithContext
  context_history_leaves

theorem contextual_splat_history (ctx : EvalContext) (ty : Ty) (operand : ValueId) :
    KeepsHistory (stepInstWithContext ctx (.ArraySplat ty operand)) := by
  unfold stepInstWithContext
  context_history_leaves

theorem contextual_closure_history (ctx : EvalContext) (cid : ClosureTyId) (fn : FuncId) (captures : List ValueId) :
    KeepsHistory (stepInstWithContext ctx (.MakeClosure cid fn captures)) := by
  unfold stepInstWithContext
  context_history_leaves

theorem contextual_aggregate_history (ctx : EvalContext) (ty : Ty) (variant : Option Nat) (fields : List ValueId) :
    KeepsHistory (stepInstWithContext ctx (.MakeAggregate ty variant fields)) := by
  cases ty <;> unfold stepInstWithContext
  all_goals first
    | exact bind_history _ _ (semMakeAggregate_history _ variant fields) (fun _ => pure_history _)
    | context_history_leaves

theorem contextual_select_history (ctx : EvalContext) (ty : Ty) (condition yes no : ValueId) :
    KeepsHistory (stepInstWithContext ctx (.Select ty condition yes no)) := by
  rw [select_step_eq]
  unfold selectTransport
  history_leaves

end TrustIr.FrameLifetime.HistoryEffects
