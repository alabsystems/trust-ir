-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixInference
import TrustIr.Proofs.TransformRefinementCtx
import TrustIr.Proofs.GenericCoroCaptureStep

namespace TrustIr.GenericCoro.Prefix

/-- Callable headers include the nominal-closure calling convention. CFGs,
    entry blocks and function-local declarations are executed separately. -/
inductive HeaderRelated : Option EvalFunction → Option EvalFunction → Prop where
  | absent : HeaderRelated none none
  | present (source target : EvalFunction)
      (body : source.body = target.body)
      (convention : source.callingConv = target.callingConv) :
      HeaderRelated (some source) (some target)

def HeaderAgreement (source target : FuncId → Option EvalFunction) : Prop :=
  ∀ id, HeaderRelated (source id) (target id)

def scopedContext (base : EvalContext) (functions : FuncId → Option EvalFunction)
    (types : Option LocalTypeTable) : EvalContext :=
  { base with functions := functions, localTypes := types }

theorem headerAgreement_refl (functions : FuncId → Option EvalFunction) :
    HeaderAgreement functions functions := by
  intro id
  cases functions id with
  | none => exact .absent
  | some function => exact .present function function rfl rfl

theorem headerAgreement_withFunction (ctx : EvalContext) (id : FuncId)
    (source target : EvalFunction) (body : source.body = target.body)
    (convention : source.callingConv = target.callingConv) :
    HeaderAgreement (withFunction ctx id source).functions (withFunction ctx id target).functions := by
  intro query
  dsimp only [withFunction]
  split
  · exact .present source target body convention
  · cases ctx.functions query with
    | none => exact .absent
    | some function => exact .present function function rfl rfl

theorem HeaderRelated.resultHeaders {source target : Option EvalFunction}
    (related : HeaderRelated source target) :
    source.map (fun function =>
      ({ params := function.body.paramTys, returns := function.body.returnTys,
         isVararg := function.body.isVararg, abi := function.body.abi } : FuncTyDef)) =
    target.map (fun function =>
      ({ params := function.body.paramTys, returns := function.body.returnTys,
         isVararg := function.body.isVararg, abi := function.body.abi } : FuncTyDef)) := by
  cases related with
  | absent => rfl
  | present source target body convention => simp only [Option.map, body]

theorem resultTypeHeaders_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (related : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) :
    (scopedContext base source sourceTypes).resultTypeHeaders =
      (scopedContext base target targetTypes).resultTypeHeaders := by
  funext id
  exact (related id).resultHeaders

/-- Constant construction reads declaration tables, not the active SSA table. -/
theorem constValueAtWithDefs_withLocalTypes (ctx : EvalContext)
    (types : Option LocalTypeTable) (ty : Ty) (constant : Constant) :
    constValueAtWithDefs { ctx with localTypes := types } ty constant =
      constValueAtWithDefs ctx ty constant := by rfl

set_option smartUnfolding false in
theorem checkClosureValueAt_withLocalTypes (ctx : EvalContext)
    (types : Option LocalTypeTable) (fuel : Nat) (ty : Ty) (value : Value) :
    checkClosureValueAt { ctx with localTypes := types } fuel ty value =
      checkClosureValueAt ctx fuel ty value := by
  induction fuel generalizing ty value with
  | zero => rfl
  | succ fuel ih =>
    have recursion : checkClosureValueAt { ctx with localTypes := types } fuel =
        checkClosureValueAt ctx fuel := funext (fun ty => funext (fun value => ih ty value))
    rw [checkClosureValueAt_succ_step, checkClosureValueAt_succ_step, recursion]
    exact captureCheckStep_withLocalTypes ctx types _ ty value

theorem checkClosureValue_withLocalTypes (ctx : EvalContext)
    (types : Option LocalTypeTable) (ty : Ty) (value : Value) :
    checkClosureValue { ctx with localTypes := types } ty value =
      checkClosureValue ctx ty value :=
  checkClosureValueAt_withLocalTypes ctx types _ ty value


theorem constValueAtWithDefs_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (ty : Ty) (constant : Constant) :
    constValueAtWithDefs (scopedContext base functions types) ty constant =
      constValueAtWithDefs base ty constant := by rfl

theorem checkClosureValue_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (ty : Ty) (value : Value) :
    checkClosureValue (scopedContext base functions types) ty value =
      checkClosureValue base ty value :=
  (checkClosureValue_withLocalTypes {base with functions := functions} types ty value).trans
    (checkClosureValue_withFunctions base functions ty value)

theorem makeAggregateValueWithContext_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (ty : Ty) (variant : Option Nat) (lanes : List Value) :
    makeAggregateValueWithContext (scopedContext base functions types) ty variant lanes =
      makeAggregateValueWithContext base ty variant lanes := by
  have checker : checkClosureValue (scopedContext base functions types) = checkClosureValue base :=
    funext (fun ty => funext (fun value => checkClosureValue_scoped base functions types ty value))
  unfold makeAggregateValueWithContext
  simp only [checker]
  rfl

theorem functionCall_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (agreement : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (held : FuncTyId) (fn : FuncId) (sig : FuncTyId) :
    functionCall (scopedContext base source sourceTypes) held fn sig =
      functionCall (scopedContext base target targetTypes) held fn sig := by
  have related := agreement fn
  cases sourceFound : source fn with
  | none =>
    cases targetFound : target fn with
    | none =>
      simp [functionCall, scopedContext, sourceFound, targetFound,
        Except.bind, Except.pure, Bind.bind, Pure.pure]
    | some function =>
      rw [sourceFound, targetFound] at related
      cases related
  | some sourceFunction =>
    cases targetFound : target fn with
    | none =>
      rw [sourceFound, targetFound] at related
      cases related
    | some targetFunction =>
      rw [sourceFound, targetFound] at related
      cases related with
      | present _ _ body convention =>
        simp [functionCall, scopedContext, sourceFound, targetFound, body,
          Except.bind, Except.pure, Bind.bind, Pure.pure]


theorem checkedClosureCaptures_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (cid : ClosureTyId) (captures : List Value) :
    checkedClosureCaptures (scopedContext base functions types) cid captures =
      checkedClosureCaptures base cid captures := by
  have checker : checkClosureValue (scopedContext base functions types) = checkClosureValue base :=
    funext (fun ty => funext (fun value => checkClosureValue_scoped base functions types ty value))
  simp only [checkedClosureCaptures, checker]
  rfl

theorem closureExtract_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (ty : Ty) (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (field : Nat) :
    closureExtract (scopedContext base functions types) ty cid fn captures field =
      closureExtract base ty cid fn captures field := by
  simp only [closureExtract, checkedClosureCaptures_scoped]

theorem closureInsert_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (ty : Ty) (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (field : Nat) (value : Value) :
    closureInsert (scopedContext base functions types) ty cid fn captures field value =
      closureInsert base ty cid fn captures field value := by
  simp only [closureInsert, checkedClosureCaptures_scoped, checkClosureValue_scoped]

theorem makeClosureValue_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (agreement : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (cid : ClosureTyId) (fn : FuncId)
    (captures : List Value) :
    makeClosureValue (scopedContext base source sourceTypes) cid fn captures =
      makeClosureValue (scopedContext base target targetTypes) cid fn captures := by
  have sourceCheck : checkClosureValue (scopedContext base source sourceTypes) = checkClosureValue base :=
    funext (fun ty => funext (fun value => checkClosureValue_scoped base source sourceTypes ty value))
  have targetCheck : checkClosureValue (scopedContext base target targetTypes) = checkClosureValue base :=
    funext (fun ty => funext (fun value => checkClosureValue_scoped base target targetTypes ty value))
  unfold makeClosureValue
  simp only [sourceCheck, targetCheck]
  cases definition : base.closures cid with
  | none =>
    simp [closureContract, scopedContext, definition, Except.bind, Except.pure, Bind.bind, Pure.pure]
  | some declaration =>
    cases signature : base.funcTys declaration.func with
    | none =>
      simp [closureContract, scopedContext, definition, signature,
        Except.bind, Except.pure, Bind.bind, Pure.pure]
    | some signatureDefinition =>
      have related := agreement fn
      cases sourceFound : source fn with
      | none =>
        cases targetFound : target fn with
        | none =>
          simp [closureContract, scopedContext, definition, signature, sourceFound, targetFound,
            Except.bind, Except.pure, Bind.bind, Pure.pure]
        | some function =>
          rw [sourceFound, targetFound] at related
          cases related
      | some sourceFunction =>
        cases targetFound : target fn with
        | none =>
          rw [sourceFound, targetFound] at related
          cases related
        | some targetFunction =>
          rw [sourceFound, targetFound] at related
          cases related with
          | present _ _ body convention =>
            cases abi : (signatureDefinition.abi.isSome || targetFunction.body.abi.isSome) <;>
              cases shape : (signatureDefinition.isVararg || targetFunction.body.isVararg ||
                !(closureTyListEq targetFunction.body.paramTys (declaration.captures ++ signatureDefinition.params)) ||
                !(closureTyListEq targetFunction.body.returnTys signatureDefinition.returns) ||
                targetFunction.body.abi != signatureDefinition.abi) <;>
              simp [closureContract, scopedContext, definition, signature, sourceFound, targetFound, body,
                abi, shape, Except.bind, Except.pure, Bind.bind, Pure.pure]

theorem closureCall_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (agreement : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (cid : ClosureTyId) (fn : FuncId)
    (captures : List Value) (sig : FuncTyId) (args : List Value) (conv : CallingConv) :
    closureCall (scopedContext base source sourceTypes) cid fn captures sig args conv =
      closureCall (scopedContext base target targetTypes) cid fn captures sig args conv := by
  have sourceCheck : checkClosureValue (scopedContext base source sourceTypes) = checkClosureValue base :=
    funext (fun ty => funext (fun value => checkClosureValue_scoped base source sourceTypes ty value))
  have targetCheck : checkClosureValue (scopedContext base target targetTypes) = checkClosureValue base :=
    funext (fun ty => funext (fun value => checkClosureValue_scoped base target targetTypes ty value))
  unfold closureCall
  simp only [sourceCheck, targetCheck,
    makeClosureValue_congr base source target agreement sourceTypes targetTypes]
  cases definition : base.closures cid with
  | none =>
    simp [closureContract, scopedContext, definition, Except.bind, Except.pure, Bind.bind, Pure.pure]
  | some declaration =>
    cases signature : base.funcTys declaration.func with
    | none =>
      simp [closureContract, scopedContext, definition, signature,
        Except.bind, Except.pure, Bind.bind, Pure.pure]
    | some signatureDefinition =>
      have related := agreement fn
      cases sourceFound : source fn with
      | none =>
        cases targetFound : target fn with
        | none =>
          simp [closureContract, scopedContext, definition, signature, sourceFound, targetFound,
            Except.bind, Except.pure, Bind.bind, Pure.pure]
        | some function =>
          rw [sourceFound, targetFound] at related
          cases related
      | some sourceFunction =>
        cases targetFound : target fn with
        | none =>
          rw [sourceFound, targetFound] at related
          cases related
        | some targetFunction =>
          rw [sourceFound, targetFound] at related
          cases related with
          | present _ _ body convention =>
            cases abi : (signatureDefinition.abi.isSome || targetFunction.body.abi.isSome) <;>
              cases shape : (signatureDefinition.isVararg || targetFunction.body.isVararg ||
                !(closureTyListEq targetFunction.body.paramTys (declaration.captures ++ signatureDefinition.params)) ||
                !(closureTyListEq targetFunction.body.returnTys signatureDefinition.returns) ||
                targetFunction.body.abi != signatureDefinition.abi) <;>
              simp [closureContract, scopedContext, definition, signature, sourceFound, targetFound, body,
                convention, abi, shape, Except.bind, Except.pure, Bind.bind, Pure.pure]

end TrustIr.GenericCoro.Prefix
