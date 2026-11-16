-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixContext

namespace TrustIr.GenericCoro.Prefix
open LocalTypeInference

/-- Metadata queries retain whether an original table exists, as well as
    every lookup on this instruction's actual operands and destinations. -/
inductive TypesAgreeOn (ids : List ValueId) : Option LocalTypeTable → Option LocalTypeTable → Prop where
  | absent : TypesAgreeOn ids none none
  | present (source target : LocalTypeTable)
      (agree : ∀ id ∈ ids, source id = target id) : TypesAgreeOn ids (some source) (some target)

theorem TypesAgreeOn.mono {ids smaller : List ValueId} {source target : Option LocalTypeTable}
    (related : TypesAgreeOn ids source target) (included : ∀ id ∈ smaller, id ∈ ids) :
    TypesAgreeOn smaller source target := by
  cases related with
  | absent => exact .absent
  | present source target agree => exact .present source target (fun id member => agree id (included id member))

theorem TypesAgreeOn.at {ids : List ValueId} {source target : Option LocalTypeTable}
    (related : TypesAgreeOn ids source target) (id : ValueId) (member : id ∈ ids) :
    source.map (fun table => table id) = target.map (fun table => table id) := by
  cases related with
  | absent => rfl
  | present source target agree => exact congrArg some (agree id member)

theorem localResultTypes_borrow_operand (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (inst : Inst) (sources : List LocalTypeSource)
    (classified : localResultTypes direct indirect inst = .ok sources)
    (operand : ValueId) (member : LocalTypeSource.borrow operand ∈ sources) :
    operand ∈ operandIds inst := by
  cases (inferInstance : Decidable (operand ∈ operandIds inst)) with
  | isTrue present => exact present
  | isFalse absent =>
    have avoids : SourceAvoids operand.index (.borrow operand) :=
      classified_sources_avoid direct indirect operand.index inst
        (fun id inOperands same => by
          have equal : id = operand := by cases id; cases operand; exact congrArg ValueId.mk same
          exact absent (equal ▸ inOperands)) sources classified (.borrow operand) member
    exact False.elim (avoids rfl)

/-- Congruence of the core left-to-right monadic traversal keeps early errors. -/
theorem mapM_congr_mem {α β : Type} (items : List α)
    (source target : α → Except SemError β)
    (agree : ∀ item ∈ items, source item = target item) : items.mapM source = items.mapM target := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.mapM_cons, List.mapM_cons, agree item ((trustIrListMemConsSelf _ _))]
    rw [ih (fun value member => agree value (List.mem_cons_of_mem item member))]

/-- Pure left-to-right validation has the same early refusal whenever all
    actual metadata reads agree. No traversal effects or order are discarded. -/
theorem forM_congr_mem {α : Type} (items : List α)
    (source target : α → Except SemError PUnit)
    (agree : ∀ item ∈ items, source item = target item) : items.forM source = items.forM target := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    change (source item >>= fun _ => rest.forM source) =
      (target item >>= fun _ => rest.forM target)
    rw [agree item ((trustIrListMemConsSelf _ _))]
    rw [ih (fun value member => agree value (List.mem_cons_of_mem item member))]

theorem makeArrayValueWithContext_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceTypes targetTypes : Option LocalTypeTable)
    (element : TyId) (count : Nat) (variant : Option Nat) (ids : List ValueId) (lanes : List Value)
    (types : TypesAgreeOn ids sourceTypes targetTypes) :
    makeArrayValueWithContext (scopedContext base source sourceTypes) element count variant ids lanes =
      makeArrayValueWithContext (scopedContext base target targetTypes) element count variant ids lanes := by
  cases types with
  | absent => rfl
  | present sourceTable targetTable agree =>
    have reads : ∀ elementTy,
        ids.forM (checkArrayRegisterType (some sourceTable) elementTy) =
        ids.forM (checkArrayRegisterType (some targetTable) elementTy) := by
      intro elementTy
      apply forM_congr_mem
      intro id member
      simp only [checkArrayRegisterType, pure_bind, agree id member]
    unfold makeArrayValueWithContext
    simp only [scopedContext, EvalContext.types, reads]

theorem integerOperand_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceTypes targetTypes : Option LocalTypeTable)
    (id : ValueId) (related : TypesAgreeOn [id] sourceTypes targetTypes) (value : Value) :
    (scopedContext base source sourceTypes).integerOperand id value =
      (scopedContext base target targetTypes).integerOperand id value := by
  cases related with
  | absent => rfl
  | present sourceTable targetTable agree =>
    have read := agree id ((trustIrListMemConsSelf _ _))
    simp [EvalContext.integerOperand, scopedContext, read,
      Except.bind, Except.pure, Bind.bind, Pure.pure]

theorem carrierIntegerOperand_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceTypes targetTypes : Option LocalTypeTable)
    (id : ValueId) (related : TypesAgreeOn [id] sourceTypes targetTypes) (value : Value) :
    (scopedContext base source sourceTypes).carrierIntegerOperand id value =
      (scopedContext base target targetTypes).carrierIntegerOperand id value := by
  cases related with
  | absent => rfl
  | present sourceTable targetTable agree =>
    have read := agree id ((trustIrListMemConsSelf _ _))
    simp [EvalContext.carrierIntegerOperand, scopedContext, read,
      Except.bind, Except.pure, Bind.bind, Pure.pure]

theorem elementIndex_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceTypes targetTypes : Option LocalTypeTable)
    (id : ValueId) (related : TypesAgreeOn [id] sourceTypes targetTypes) (value : Value) :
    (scopedContext base source sourceTypes).elementIndex id value =
      (scopedContext base target targetTypes).elementIndex id value := by
  simp only [EvalContext.elementIndex,
    integerOperand_congr base source target sourceTypes targetTypes id related value]

theorem declaredFieldTy_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (aggregateTy : Ty) (held : Value) (field : Nat) :
    declaredFieldTy (scopedContext base functions types) aggregateTy held field =
      declaredFieldTy base aggregateTy held field := by rfl

theorem checkDeclaredField_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceTypes targetTypes : Option LocalTypeTable)
    (id : ValueId) (related : TypesAgreeOn [id] sourceTypes targetTypes)
    (held : Value) (field : Nat) (accessTy : Ty) :
    checkDeclaredField (scopedContext base source sourceTypes) id held field accessTy =
      checkDeclaredField (scopedContext base target targetTypes) id held field accessTy := by
  cases related with
  | absent => rfl
  | present sourceTable targetTable agree =>
    have read := agree id ((trustIrListMemConsSelf _ _))
    simp only [checkDeclaredField]
    simp only [show (scopedContext base source (some sourceTable)).localTypes = some sourceTable from rfl,
      show (scopedContext base target (some targetTable)).localTypes = some targetTable from rfl]
    simp only [Except.bind, Except.pure, Bind.bind, Pure.pure, read, declaredFieldTy_scoped]


theorem resultSourceType_congr {ids : List ValueId} {source target : Option LocalTypeTable}
    (related : TypesAgreeOn ids source target) (entry : LocalTypeSource)
    (borrow : ∀ operand, entry = .borrow operand → operand ∈ ids) :
    ssaResultSourceType source entry = ssaResultSourceType target entry := by
  cases entry with
  | declared ty => rfl
  | borrow operand =>
    have member := borrow operand rfl
    cases related with
    | absent => rfl
    | present source target agree => simp only [ssaResultSourceType, agree operand member]

/-- Result classification and every recorded association remain a complete
    Except computation; missing declarations and census errors are retained. -/
theorem ssaInstructionResultTypes_congr (source target : Option LocalTypeTable)
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (inst : Inst) (dests : List ValueId) (produced : Nat)
    (related : TypesAgreeOn (dests ++ operandIds inst) source target) :
    ssaInstructionResultTypes source direct indirect inst dests produced =
      ssaInstructionResultTypes target direct indirect inst dests produced := by
  cases related with
  | absent => rfl
  | present sourceTable targetTable agree =>
    have recorded : dests.mapM (fun dest => match sourceTable dest with
          | some ty => Except.ok ty
          | none => .error (SemError.typeError "SSA types: result destination has no declaration")) =
        dests.mapM (fun dest => match targetTable dest with
          | some ty => Except.ok ty
          | none => .error (SemError.typeError "SSA types: result destination has no declaration")) := by
      apply mapM_congr_mem
      intro id member
      rw [agree id (trustIrListMemAppendLeft _ member)]
    unfold ssaInstructionResultTypes
    dsimp only
    rw (config := { transparency := .default }) [recorded]
    cases classified : localResultTypes direct indirect inst with
    | error error => rfl
    | ok sources =>
      have expected : sources.mapM (ssaResultSourceType (some sourceTable)) =
          sources.mapM (ssaResultSourceType (some targetTable)) := by
        apply mapM_congr_mem
        intro entry member
        apply resultSourceType_congr (.present sourceTable targetTable agree) entry
        intro operand isBorrow
        subst entry
        exact trustIrListMemAppendRight _
          (localResultTypes_borrow_operand direct indirect inst sources classified operand member)
      simp only [Except.bind, Except.pure, Bind.bind, Pure.pure]
      rw (config := { transparency := .default }) [expected]
      rfl

theorem instructionResultTypes_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (inst : Inst)
    (dests : List ValueId) (produced : Nat)
    (related : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    (scopedContext base source sourceTypes).instructionResultTypes inst dests produced =
      (scopedContext base target targetTypes).instructionResultTypes inst dests produced := by
  unfold EvalContext.instructionResultTypes
  rw [resultTypeHeaders_congr base source target headers sourceTypes targetTypes]
  exact ssaInstructionResultTypes_congr sourceTypes targetTypes _ _ inst dests produced related

theorem checkInstructionResults_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (inst : Inst)
    (dests : List ValueId) (values : List Value)
    (related : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    (scopedContext base source sourceTypes).checkInstructionResults inst dests values =
      (scopedContext base target targetTypes).checkInstructionResults inst dests values := by
  simp only [EvalContext.checkInstructionResults,
    instructionResultTypes_congr base source target headers sourceTypes targetTypes inst dests values.length related]

theorem bindCallResults_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (inst : Inst)
    (dests : List ValueId) (values : List Value)
    (related : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    (scopedContext base source sourceTypes).bindCallResults inst dests values =
      (scopedContext base target targetTypes).bindCallResults inst dests values := by
  simp only [EvalContext.bindCallResults,
    checkInstructionResults_congr base source target headers sourceTypes targetTypes inst dests values related]

theorem bindInstructionResults_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (inst : Inst)
    (dests : List ValueId) (result : InstrResult)
    (related : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    (scopedContext base source sourceTypes).bindInstructionResults inst result dests =
      (scopedContext base target targetTypes).bindInstructionResults inst result dests := by
  cases result with
  | value value =>
    cases dests with
    | nil => cases value <;> simp only [EvalContext.bindInstructionResults,
        checkInstructionResults_congr base source target headers sourceTypes targetTypes inst [] _ related]
    | cons dest rest =>
      cases rest with
      | nil => cases value <;> simp only [EvalContext.bindInstructionResults,
          checkInstructionResults_congr base source target headers sourceTypes targetTypes inst [dest] _ related]
      | cons second rest => cases value <;> rfl
  | values values =>
    simp only [EvalContext.bindInstructionResults,
      checkInstructionResults_congr base source target headers sourceTypes targetTypes inst dests _ related]
  | terminator term => rfl

end TrustIr.GenericCoro.Prefix
