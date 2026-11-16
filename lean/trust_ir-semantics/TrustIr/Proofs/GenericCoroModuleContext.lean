-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedContext
import TrustIr.Proofs.DecodedContextLookup
import TrustIr.Proofs.GenericCoroAllBlocksContext
import TrustIr.Proofs.GenericCoroModuleFactory
import TrustIr.Proofs.GenericCoroHeaderMaps

namespace TrustIr.GenericCoro.ModuleContext
open TrustIrEval GenericCoroAllBlocksPlanner GenericCoroFreshIds
open AllBlocksContext ModuleFactory

/-- Actual decoded bodies and executable metadata for one successful source
    occurrence. Declarations are retained without inventing executable bodies. -/
def EvaluatedOccurrence (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source target : Function) : Prop :=
  ∃ sourceRows targetRows, source.blocks = .ok sourceRows ∧ target.blocks = .ok targetRows ∧
    sameHeader source target ∧
    (source.isDeclaration = true ∨
      ∃ sourceFunction targetFunction, source.isDeclaration = false ∧
        evalFunctionOfWithTypes signatures direct source sourceRows = .ok sourceFunction ∧
        evalFunctionOfWithTypes signatures direct target targetRows = .ok targetFunction ∧
        FactoryReplacement sourceFunction targetFunction)

private theorem evalFunctionOfWithTypes_inferred (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (function : Function) (rows : Rows)
    (signature : FuncTyDef) (found : (trustIrArrayGet? signatures function.ty.index) = some signature)
    (inferred : LocalTypeInference)
    (actual : inferLocalTypesWithEvidence direct (fun id => (trustIrArrayGet? signatures id.index))
      (graphParams rows) (graphNodes rows) = .ok inferred) :
    evalFunctionOfWithTypes signatures direct function rows = .ok
      { sourceId := some function.id
        body := {paramTys := signature.params, returnTys := signature.returns, abi := signature.abi, isVararg := signature.isVararg}
        cfg := TrustIrEval.cfgOf rows, entryBlock := function.entry,
        callingConv := function.callingConvention, localTypes := some inferred.table } := by
  trustIrCompilerProof {
    simp only [evalFunctionOfWithTypes, DecodedCFG.indexedCFG_eq_cfgOf, found,
      inferLocalTypes, inferLocalTypesWithWork,
      show rows.bind (fun row => row.snd.params) = graphParams rows from rfl,
      show rows.bind (fun (_, block) => bodyInstsWithResultDests block.body block.bodyResultDests ++
        [(block.terminator, block.terminatorResultDests)]) = graphNodes rows from rfl,
      actual, Bind.bind, Except.bind, Pure.pure, Except.pure]
  } {
    simp only [evalFunctionOfWithTypes, DecodedCFG.indexedCFG_eq_cfgOf, found,
      inferLocalTypes, inferLocalTypesWithWork,
      show (trustIrListBind rows (fun row => row.snd.params)) = graphParams rows from rfl,
      show (trustIrListBind rows (fun (_, block) => bodyInstsWithResultDests block.body block.bodyResultDests ++
        [(block.terminator, block.terminatorResultDests)])) = graphNodes rows from rfl,
      actual, Bind.bind, Except.bind, Pure.pure, Except.pure]
  }

theorem lowerFunction_evaluated (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (source target : Function)
    (actual : lowerFunction signatures direct source = .ok target) :
    EvaluatedOccurrence signatures direct source target := by
  trustIrCompilerProof {
    have law := lowerFunction_law signatures direct source target actual
    cases body : source.blocks with
    | error error => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind] at actual
    | ok rows =>
      cases declaration : source.isDeclaration with
      | true =>
        have targetEq := law.2.1 declaration
        subst target
        exact ⟨rows, rows, body, body, rfl, Or.inl declaration⟩
      | false =>
        cases signatureFound : signatures.get? source.ty.index with
        | none => simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind,
            declaration, Bool.false_eq_true, if_false, signatureFound] at actual
        | some signature =>
          have prepared := lowerFunction_prepared signatures direct source target actual
          rcases prepared with impossible | ⟨sourceRows, expansion, _declared, sourceBody, prepared, targetEq⟩
          · rw [declaration] at impossible; cases impossible.1
          have rowsEq : sourceRows = rows := Except.ok.inj (sourceBody.symm.trans body)
          subst sourceRows
          have ready := prepareRows_ready u32Domain direct (fun id => signatures.get? id.index)
            rows expansion prepared
          cases expansion with
          | unchanged inferred =>
            subst target
            have evaluated := evalFunctionOfWithTypes_inferred signatures direct source rows signature
              signatureFound inferred ready.1
            exact ⟨rows, rows, body, body, rfl, Or.inr ⟨_, _, declaration, evaluated, evaluated, Or.inl rfl⟩⟩
          | capacity inferred certificate => exact False.elim targetEq
          | expanded targetRows sourceInferred targetInferred =>
            subst target
            let header : EvalFunction :=
              { sourceId := some source.id
                body := {paramTys := signature.params, returnTys := signature.returns, abi := signature.abi, isVararg := signature.isVararg}
                cfg := TrustIrEval.cfgOf rows, entryBlock := source.entry,
                callingConv := source.callingConvention }
            have sourceEvaluated := evalFunctionOfWithTypes_inferred signatures direct source rows signature
              signatureFound sourceInferred ready.1
            have targetEvaluated := evalFunctionOfWithTypes_inferred signatures direct
              {source with blocks := .ok targetRows} targetRows signature signatureFound
              targetInferred ready.2.2.2.1
            have factory := prepareRows_toFunctions u32Domain direct (fun id => signatures.get? id.index)
              header rows
            rw [prepared] at factory
            have factoryActual : AllBlocks.functions direct (fun id => signatures.get? id.index) header rows =
                .ok (.expanded (AllBlocks.withInferredGraph header rows sourceInferred)
                  (AllBlocks.withInferredGraph header targetRows targetInferred)) := factory.symm
            refine ⟨rows, targetRows, body, rfl, rfl, Or.inr ⟨_, _, declaration,
              sourceEvaluated, targetEvaluated, Or.inr ⟨direct, (fun id => signatures.get? id.index), header, rows, ?_⟩⟩⟩
            simpa only [AllBlocks.withInferredGraph_eq, header] using factoryActual
  } {
    have error_ne_ok : ∀ {ε α : Type} (error : ε) (value : α),
        (Except.error error : Except ε α) ≠ Except.ok value := by
      intro ε α error value impossible
      cases impossible
    have law := lowerFunction_law signatures direct source target actual
    cases body : source.blocks with
    | error error =>
      simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind] at actual
      exact False.elim (error_ne_ok _ _ actual)
    | ok rows =>
      cases declaration : source.isDeclaration with
      | true =>
        have targetEq := law.2.1 declaration
        subst target
        exact ⟨rows, rows, body, body, rfl, Or.inl declaration⟩
      | false =>
        cases signatureFound : (trustIrArrayGet? signatures source.ty.index) with
        | none =>
          simp only [lowerFunction, body, Except.mapError, Bind.bind, Except.bind,
            declaration, Bool.false_eq_true, if_false, signatureFound] at actual
          exact False.elim (error_ne_ok _ _ actual)
        | some signature =>
          have prepared := lowerFunction_prepared signatures direct source target actual
          rcases prepared with impossible | ⟨sourceRows, expansion, _declared, sourceBody, prepared, targetEq⟩
          · rw [declaration] at impossible; cases impossible.1
          have rowsEq : sourceRows = rows := Except.ok.inj (sourceBody.symm.trans body)
          subst sourceRows
          have ready := prepareRows_ready u32Domain direct (fun id => (trustIrArrayGet? signatures id.index))
            rows expansion prepared
          cases expansion with
          | unchanged inferred =>
            subst target
            have evaluated := evalFunctionOfWithTypes_inferred signatures direct source rows signature
              signatureFound inferred ready.1
            exact ⟨rows, rows, body, body, rfl, Or.inr ⟨_, _, declaration, evaluated, evaluated, Or.inl rfl⟩⟩
          | capacity inferred certificate => exact False.elim targetEq
          | expanded targetRows sourceInferred targetInferred =>
            subst target
            let header : EvalFunction :=
              { sourceId := some source.id
                body := {paramTys := signature.params, returnTys := signature.returns, abi := signature.abi, isVararg := signature.isVararg}
                cfg := TrustIrEval.cfgOf rows, entryBlock := source.entry,
                callingConv := source.callingConvention }
            have sourceEvaluated := evalFunctionOfWithTypes_inferred signatures direct source rows signature
              signatureFound sourceInferred ready.1
            have targetEvaluated := evalFunctionOfWithTypes_inferred signatures direct
              {source with blocks := .ok targetRows} targetRows signature signatureFound
              targetInferred ready.2.2.2.1
            have factory := prepareRows_toFunctions u32Domain direct (fun id => (trustIrArrayGet? signatures id.index))
              header rows
            rw [prepared] at factory
            have factoryActual : AllBlocks.functions direct (fun id => (trustIrArrayGet? signatures id.index)) header rows =
                .ok (.expanded (AllBlocks.withInferredGraph header rows sourceInferred)
                  (AllBlocks.withInferredGraph header targetRows targetInferred)) := factory.symm
            refine ⟨rows, targetRows, body, rfl, rfl, Or.inr ⟨_, _, declaration,
              sourceEvaluated, targetEvaluated, Or.inr ⟨direct, (fun id => (trustIrArrayGet? signatures id.index)), header, rows, ?_⟩⟩⟩
            simpa only [AllBlocks.withInferredGraph_eq, header] using factoryActual
  }

/-- The literal filter projection inside `contextOf`, used only as a proof
    expression. Runtime context construction remains the shared original code. -/
private abbrev executableEntries (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (functions : List Function) : List (FuncId × D EvalFunction) :=
  functions.filterMap (fun function => match function.blocks with
    | .ok blocks => if function.isDeclaration then none
      else some (function.id, evalFunctionOfWithTypes signatures direct function blocks)
    | .error _ => none)

private theorem sameHeader_declaration {source target : Function} (same : sameHeader source target) :
    target.isDeclaration = source.isDeclaration := by
  have equality : {target with blocks := source.blocks} = source := same
  have projected := congrArg Function.isDeclaration equality
  exact projected

private theorem sameHeader_callingConvention {source target : Function} (same : sameHeader source target) :
    target.callingConvention = source.callingConvention := by
  have equality : {target with blocks := source.blocks} = source := same
  have projected := congrArg Function.callingConvention equality
  exact projected

private theorem produced_law (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    {source target : List Function} (produced : Produced signatures direct source target) :
    FunctionsLaw source target := by
  induction produced with
  | nil => exact .nil
  | cons actual _rest ih => exact .cons (lowerFunction_law signatures direct _ _ actual) ih

/-- All executable rows are actual successful metadata conversions. The list
    keeps every occurrence in source order; later same-key rows stay masked. -/
theorem produced_evaluated (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    {source target : List Function} (produced : Produced signatures direct source target) :
    ∃ updates : List FunctionUpdate,
      executableEntries signatures direct source = updates.map (fun update => (update.id, .ok update.source)) ∧
      executableEntries signatures direct target = updates.map (fun update => (update.id, .ok update.target)) ∧
      (∀ update ∈ updates, FactoryReplacement update.source update.target) ∧
      (∀ function ∈ source, ∃ rows, function.blocks = .ok rows) ∧
      (∀ function ∈ target, ∃ rows, function.blocks = .ok rows) := by
  induction produced with
  | nil =>
    refine ⟨[], rfl, rfl, ?_, ?_, ?_⟩
    · intro update member; cases member
    · intro function member; cases member
    · intro function member; cases member
  | @cons source target sources targets actual _rest ih =>
    obtain ⟨updates, sourceEntries, targetEntries, replacements, sourceDecoded, targetDecoded⟩ := ih
    obtain ⟨sourceRows, targetRows, sourceBody, targetBody, same, declaration | executable⟩ :=
      lowerFunction_evaluated signatures direct source target actual
    · refine ⟨updates, ?_, ?_, replacements, ?_, ?_⟩
      · simpa only [executableEntries, List.filterMap, sourceBody, declaration, if_true] using sourceEntries
      · simpa only [executableEntries, List.filterMap, targetBody,
          sameHeader_declaration same, declaration, if_true] using targetEntries
      · intro function member
        rcases List.mem_cons.mp member with rfl | rest
        · exact ⟨sourceRows, sourceBody⟩
        · exact sourceDecoded function rest
      · intro function member
        rcases List.mem_cons.mp member with rfl | rest
        · exact ⟨targetRows, targetBody⟩
        · exact targetDecoded function rest
    · obtain ⟨sourceFunction, targetFunction, declaration, sourceEval, targetEval, replacement⟩ := executable
      let update : FunctionUpdate := ⟨source.id, sourceFunction, targetFunction⟩
      refine ⟨update :: updates, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [executableEntries, List.filterMap, sourceBody, declaration,
          Bool.false_eq_true, if_false, sourceEval, List.map_cons, update]
        exact congrArg (List.cons _) sourceEntries
      · simp only [executableEntries, List.filterMap, targetBody, sameHeader_declaration same,
          declaration, Bool.false_eq_true, if_false, targetEval, sameHeader_id same, List.map_cons, update]
        exact congrArg (List.cons _) targetEntries
      · intro entry member
        rcases List.mem_cons.mp member with rfl | rest
        · exact replacement
        · exact replacements entry rest
      · intro function member
        rcases List.mem_cons.mp member with rfl | rest
        · exact ⟨sourceRows, sourceBody⟩
        · exact sourceDecoded function rest
      · intro function member
        rcases List.mem_cons.mp member with rfl | rest
        · exact ⟨targetRows, targetBody⟩
        · exact targetDecoded function rest

private theorem filter_append {α : Type} (predicate : α → Bool) (left right : List α) :
    (left ++ right).filter predicate = left.filter predicate ++ right.filter predicate := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
    cases found : predicate head <;> simp only [List.cons_append, List.filter, found,
      Bool.false_eq_true, if_false, if_true, List.cons_append]
    · exact ih
    · exact congrArg (List.cons head) ih

private theorem filter_bind {α β : Type} (predicate : β → Bool) (rows : List α) (f : α → List β) :
    ((trustIrListBind rows f)).filter predicate = (trustIrListBind rows (fun row => (f row).filter predicate)) := by
  trustIrCompilerProof {
    induction rows with
    | nil => rfl
    | cons head rest ih => simp only [List.cons_bind, filter_append, ih]
  } {
    induction rows with
    | nil => rfl
    | cons head rest ih => simp only [List.flatMap_cons, filter_append, ih]
  }

/-- Proof projection of the exact original memory-root selector. -/
private def imageRoots (types : List (Option Ty)) : Inst → List Ty
  | .Alloca ty .. | .HeapAlloc ty .. | .GEP ty .. | .Load ty .. | .Store ty ..
  | .AtomicLoad ty .. | .AtomicStore ty .. | .AtomicRMW _ ty .. | .CmpXchg ty .. => [ty]
  | .SeqMap (.Sequence element) _ _ => (((trustIrListGet? types element.index)).join).toList
  | _ => []

private def blockImageRoots (types : List (Option Ty)) (block : BasicBlock) : List Ty :=
  ((trustIrListBind (block.body ++ [block.terminator]) (imageRoots types))).filter (fun ty => !ty.hasCanonicalMemoryLayout)

private def graphImageRoots (types : List (Option Ty)) (rows : Rows) : List Ty :=
  (trustIrListBind rows (fun row => blockImageRoots types row.2))

private theorem expandedEntry_imageRoots (types : List (Option Ty)) (names : Names) (block : BasicBlock) :
    blockImageRoots types (expandedEntry names block) = blockImageRoots types block := by
  trustIrCompilerProof {
    cases term : block.terminator <;> simp only [expandedEntry, term]
    simp only [blockImageRoots, term, List.append_bind, List.cons_bind,
      List.nil_bind, imageRoots, List.append_nil, filter_append, List.filter,
      Ty.hasCanonicalMemoryLayout, Bool.not_true, Bool.false_eq_true, if_false,
      List.nil_append]
  } {
    cases term : block.terminator <;> simp only [expandedEntry, term]
    simp only [blockImageRoots, term, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, imageRoots, List.append_nil, filter_append, List.filter,
      Ty.hasCanonicalMemoryLayout, Bool.not_true, Bool.false_eq_true, if_false,
      List.nil_append]
  }

private theorem plans_imageRoots {domain : Nat} {used : List Nat}
    {before after : GenericCoroFreshCursor.Cursor domain used} {source target : Rows} {trace : Trace}
    (plan : Plans before after source target trace) (types : List (Option Ty)) :
    graphImageRoots types target = graphImageRoots types source := by
  trustIrCompilerProof {
    induction plan with
    | nil => rfl
    | keep _ _ id block _ source target trace _rest ih =>
      simp only [graphImageRoots, List.cons_bind] at ih ⊢
      rw [ih]
    | expand _ _ _ id block _ names _ source target trace _rest ih =>
      simp only [graphImageRoots, List.cons_bind] at ih ⊢
      rw [expandedEntry_imageRoots, ih]
  } {
    induction plan with
    | nil => rfl
    | keep _ _ id block _ source target trace _rest ih =>
      simp only [graphImageRoots, List.flatMap_cons] at ih ⊢
      rw [ih]
    | expand _ _ _ id block _ names _ source target trace _rest ih =>
      simp only [graphImageRoots, List.flatMap_cons] at ih ⊢
      rw [expandedEntry_imageRoots, ih]
  }

private def functionImageRoots (types : List (Option Ty)) (function : Function) : List Ty :=
  match function.blocks with
  | .error _ => []
  | .ok rows => graphImageRoots types rows

/-- Preparing the transformed rows adds only canonical I64 roots. Every
    original aggregate image root, including shadowed/unused rows, remains. -/
theorem lowerFunction_imageRoots (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source target : Function) (actual : lowerFunction signatures direct source = .ok target)
    (types : List (Option Ty)) : functionImageRoots types target = functionImageRoots types source := by
  trustIrCompilerProof {
    rcases lowerFunction_prepared signatures direct source target actual with declaration | prepared
    · rw [declaration.2]
    · obtain ⟨rows, expansion, _declared, sourceBody, prepared, targetEq⟩ := prepared
      have ready := prepareRows_ready u32Domain direct (fun id => signatures.get? id.index) rows expansion prepared
      cases expansion with
      | unchanged inferred => rw [targetEq]
      | capacity inferred certificate => exact False.elim targetEq
      | expanded targetRows sourceInferred targetInferred =>
        rw [targetEq, functionImageRoots, functionImageRoots, sourceBody]
        rw [ready.2.1]
        exact plans_imageRoots (lowerRows_ready u32Domain rows ready.2.2.1) types
  } {
    rcases lowerFunction_prepared signatures direct source target actual with declaration | prepared
    · rw [declaration.2]
    · obtain ⟨rows, expansion, _declared, sourceBody, prepared, targetEq⟩ := prepared
      have ready := prepareRows_ready u32Domain direct (fun id => (trustIrArrayGet? signatures id.index)) rows expansion prepared
      cases expansion with
      | unchanged inferred => rw [targetEq]
      | capacity inferred certificate => exact False.elim targetEq
      | expanded targetRows sourceInferred targetInferred =>
        rw [targetEq, functionImageRoots, functionImageRoots, sourceBody]
        rw [ready.2.1]
        exact plans_imageRoots (lowerRows_ready u32Domain rows ready.2.2.1) types
  }

private theorem produced_imageRoots (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    {source target : List Function} (produced : Produced signatures direct source target)
    (types : List (Option Ty)) :
    (trustIrListBind target (functionImageRoots types)) = (trustIrListBind source (functionImageRoots types)) := by
  trustIrCompilerProof {
    induction produced with
    | nil => rfl
    | cons actual _rest ih =>
      simp only [List.cons_bind, lowerFunction_imageRoots signatures direct _ _ actual types, ih]
  } {
    induction produced with
    | nil => rfl
    | cons actual _rest ih =>
      simp only [List.flatMap_cons, lowerFunction_imageRoots signatures direct _ _ actual types, ih]
  }

/-- The exact original OpenFrame census is source metadata, not a
    reconstructed type from runtime frame children. -/
private def frameDeclaration : Inst → Option BindingFrameDef
  | .OpenFrame declaration => some declaration
  | _ => none

private def blockFrameDeclarations (block : BasicBlock) : List BindingFrameDef :=
  (block.body ++ [block.terminator]).filterMap frameDeclaration

private def graphFrameDeclarations (rows : Rows) : List BindingFrameDef :=
  trustIrListBind rows (fun row => blockFrameDeclarations row.2)

private theorem frameDeclaration_append (left right : List Inst) :
    (left ++ right).filterMap frameDeclaration =
      left.filterMap frameDeclaration ++ right.filterMap frameDeclaration := by
  induction left with
  | nil => rfl
  | cons inst rest ih =>
    cases found : frameDeclaration inst <;>
      simp only [List.cons_append, List.filterMap, found, List.cons_append]
    all_goals first | exact ih | exact congrArg (List.cons _) ih

private theorem expandedEntry_frameDeclarations (names : Names) (block : BasicBlock) :
    blockFrameDeclarations (expandedEntry names block) = blockFrameDeclarations block := by
  cases term : block.terminator <;> simp only [expandedEntry, term]
  simp only [blockFrameDeclarations, term, frameDeclaration_append,
    List.filterMap, frameDeclaration, List.append_nil]

private theorem plans_frameDeclarations {domain : Nat} {used : List Nat}
    {before after : GenericCoroFreshCursor.Cursor domain used} {source target : Rows} {trace : Trace}
    (plan : Plans before after source target trace) :
    graphFrameDeclarations target = graphFrameDeclarations source := by
  induction plan with
  | nil => rfl
  | keep _ _ id block _ source target trace _rest ih =>
    trustIrCompilerProof {
      simp only [graphFrameDeclarations, List.cons_bind] at ih ⊢
    } {
      simp only [graphFrameDeclarations, List.flatMap_cons] at ih ⊢
    }
    rw [ih]
  | expand _ _ _ id block _ names _ source target trace _rest ih =>
    trustIrCompilerProof {
      simp only [graphFrameDeclarations, List.cons_bind] at ih ⊢
    } {
      simp only [graphFrameDeclarations, List.flatMap_cons] at ih ⊢
    }
    rw [expandedEntry_frameDeclarations, ih]

private def functionFrameDeclarations (function : Function) : Option (List BindingFrameDef) :=
  function.blocks.toOption.map graphFrameDeclarations

private theorem lowerFunction_frameDeclarations (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) (source target : Function)
    (actual : lowerFunction signatures direct source = .ok target) :
    functionFrameDeclarations target = functionFrameDeclarations source := by
  rcases lowerFunction_prepared signatures direct source target actual with declaration | prepared
  · rw [declaration.2]
  · obtain ⟨rows, expansion, _declared, sourceBody, prepared, targetEq⟩ := prepared
    have ready := prepareRows_ready u32Domain direct (fun id => trustIrArrayGet? signatures id.index) rows expansion prepared
    cases expansion with
    | unchanged inferred => rw [targetEq]
    | capacity inferred certificate => exact False.elim targetEq
    | expanded targetRows sourceInferred targetInferred =>
      rw [targetEq, functionFrameDeclarations, functionFrameDeclarations, sourceBody]
      simp only [Except.toOption, Option.map]
      rw [ready.2.1]
      exact congrArg some (plans_frameDeclarations (lowerRows_ready u32Domain rows ready.2.2.1))

private theorem produced_functionDeclarations (signatures : Array FuncTyDef)
    (direct : FuncId → Option FuncTyDef) {source target : List Function}
    (produced : Produced signatures direct source target) :
    target.map (functionDeclarationOf signatures) =
      source.map (functionDeclarationOf signatures) := by
  induction produced with
  | nil => rfl
  | cons actual _rest ih =>
    simp only [List.map_cons, ih]
    apply congrArg (List.cons · _)
    have same := (lowerFunction_law signatures direct _ _ actual).1
    have frames := lowerFunction_frameDeclarations signatures direct _ _ actual
    unfold functionDeclarationOf
    rw [sameHeader_id same, sameHeader_ty same, sameHeader_callingConvention same]
    congr 1
    all_goals exact frames

private theorem produced_valueSource (source : Module) (targets : List Function)
    (produced : Produced source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions targets) :
    valueSourceOf {source with functions := targets} = valueSourceOf source := by
  have functions := produced_functionDeclarations _ _ produced
  unfold valueSourceOf
  apply congrArg FunctionItemPresence.prepare
  apply congrArg (fun rows => ({ types := source.types, structs := source.structs, enums := source.enums, records := source.records, closures := source.closureTys, functions := rows } : FunctionItemPresence.Source))
  exact functions

private theorem header_foldl {α : Type} (step : α → Function → α)
    (respects : ∀ state source target, sameHeader source target → step state target = step state source)
    {source target : List Function} (law : FunctionsLaw source target) (initial : α) :
    target.foldl step initial = source.foldl step initial := by
  induction law generalizing initial with
  | nil => rfl
  | cons law _rest ih =>
    simp only [List.foldl_cons]
    rw [respects initial _ _ law.1]
    exact ih _

private theorem headers_original (signatures : Array FuncTyDef)
    {source target : List Function} (law : FunctionsLaw source target) :
    (target.foldl (fun table function =>
      if table.contains function.id.index then table
      else table.insert function.id.index (match (trustIrArrayGet? signatures function.ty.index) with
        | some signature => .ok { signature, callingConv := function.callingConvention }
        | none => .error (.typeError s!"function {function.id.index}: original signature is absent")))
      (Lean.mkRBMap Nat (Except SemError TrustIr.FunctionHeader) compare)) =
    (source.foldl (fun table function =>
      if table.contains function.id.index then table
      else table.insert function.id.index (match (trustIrArrayGet? signatures function.ty.index) with
        | some signature => .ok { signature, callingConv := function.callingConvention }
        | none => .error (.typeError s!"function {function.id.index}: original signature is absent")))
      (Lean.mkRBMap Nat (Except SemError TrustIr.FunctionHeader) compare)) := by
  apply header_foldl _ _ law
  intro table source target same
  rw [sameHeader_id same, sameHeader_ty same, sameHeader_callingConvention same]

private theorem header_functions {source target : List Function} (law : FunctionsLaw source target) :
    target.map (fun function => (function.id, function.ty)) =
      source.map (fun function => (function.id, function.ty)) := by
  induction law with
  | nil => rfl
  | cons law _rest ih => simp only [List.map_cons, sameHeader_id law.1, sameHeader_ty law.1, ih]

private theorem header_ids {source target : List Function} (law : FunctionsLaw source target) :
    target.map Function.id = source.map Function.id := by
  induction law with
  | nil => rfl
  | cons law _rest ih => simp only [List.map_cons, sameHeader_id law.1, ih]

private theorem header_declared {source target : List Function} (law : FunctionsLaw source target) (id : FuncId) :
    target.any (fun function => function.id == id && function.isDeclaration) =
      source.any (fun function => function.id == id && function.isDeclaration) := by
  induction law with
  | nil => rfl
  | cons law _rest ih =>
    simp only [List.any_cons, sameHeader_id law.1, sameHeader_declaration law.1, ih]

private theorem find_some_member {α : Type} (predicate : α → Bool) (rows : List α)
    (value : α) (actual : rows.find? predicate = some value) : value ∈ rows := by
  induction rows with
  | nil => cases actual
  | cons head rest ih =>
    cases found : predicate head <;> simp only [List.find?, found] at actual
    · exact List.mem_cons_of_mem head (ih actual)
    · cases actual; exact (trustIrListMemConsSelf _ _)

private theorem entries_find (choose : FunctionUpdate → EvalFunction) (updates : List FunctionUpdate) (id : FuncId) :
    ((updates.map (fun update => (update.id, (.ok (choose update) : D EvalFunction)))).find?
      (fun row => row.1 == id)) =
      (updates.find? (fun update => id == update.id)).map (fun update => (update.id, .ok (choose update))) := by
  induction updates with
  | nil => rfl
  | cons head rest ih =>
    have flip : (head.id == id) = (id == head.id) := by
      exact Bool.beq_comm
    simp only [List.map_cons, List.find?, flip]
    cases found : id == head.id <;> simp only [found, Option.map, ih]

private theorem entries_errors_none (choose : FunctionUpdate → EvalFunction) (updates : List FunctionUpdate) (id : FuncId) :
    (match (updates.map (fun update => (update.id, (.ok (choose update) : D EvalFunction)))).find?
      (fun row => row.1 == id) with
      | some (_, .error (.malformed message)) => some (SemError.typeError message)
      | some (_, .error (.unsupported feature)) => some (SemError.unsupported .ssaTypeTable feature)
      | _ => none) = none := by
  rw [entries_find]
  cases updates.find? (fun update => id == update.id) <;> rfl

private def functionErrorsView (functions : List Function) (entries : List (FuncId × D EvalFunction))
    (id : FuncId) : Option SemError :=
  match functions.find? (fun function => function.id == id) with
      | some function => match function.blocks with
        | Except.error (DecodeError.unsupported feature) => some (SemError.unsupported .interproceduralCall
            s!"function {id.index} body is unsupported: {feature}")
        | Except.error (DecodeError.malformed message) => some (SemError.typeError s!"function {id.index} body is malformed: {message}")
        | Except.ok _ => match entries.find?
            (fun row => row.1 == id) with
          | some (_, Except.error (DecodeError.malformed message)) => some (SemError.typeError message)
          | some (_, Except.error (DecodeError.unsupported feature)) => some (SemError.unsupported .ssaTypeTable feature)
          | _ => none
      | none => none

private theorem function_errors_none (functions : List Function) (decoded : ∀ function ∈ functions,
    ∃ rows, function.blocks = .ok rows) (choose : FunctionUpdate → EvalFunction)
    (updates : List FunctionUpdate) (id : FuncId) :
    functionErrorsView functions (updates.map (fun update => (update.id, (.ok (choose update) : D EvalFunction)))) id = none := by
  unfold functionErrorsView
  cases found : functions.find? (fun function => function.id == id) with
  | none => rfl
  | some function =>
    obtain ⟨rows, body⟩ := decoded function (find_some_member _ _ _ found)
    simp only [body]
    exact entries_errors_none choose updates id

private theorem roots_filter (types : List (Option Ty)) (globals : List GlobalDef) (functions : List Function) :
    (List.filter (fun ty => !ty.hasCanonicalMemoryLayout) ([Ty.I64] ++ globals.map (·.ty) ++ (trustIrListBind functions (fun function => match function.blocks with
      | .error _ => []
      | .ok rows => (trustIrListBind rows (fun row => (trustIrListBind (row.2.body ++ [row.2.terminator]) (imageRoots types)))))))
      ) =
    (globals.map (·.ty)).filter (fun ty => !ty.hasCanonicalMemoryLayout) ++
      (trustIrListBind functions (functionImageRoots types)) := by
  trustIrCompilerProof {
    simp only [filter_append, show [Ty.I64].filter (fun ty => !ty.hasCanonicalMemoryLayout) = [] from rfl,
      List.nil_append, filter_bind]
    apply congrArg (fun rest => (globals.map (·.ty)).filter (fun ty => !ty.hasCanonicalMemoryLayout) ++ rest)
    apply congrArg (List.bind functions)
    funext function
    cases body : function.blocks with
    | error error => simp only [functionImageRoots, body, List.filter]
    | ok rows => simp only [functionImageRoots, body, graphImageRoots, blockImageRoots, filter_bind]
  } {
    simp only [filter_append, show [Ty.I64].filter (fun ty => !ty.hasCanonicalMemoryLayout) = [] from rfl,
      List.nil_append, filter_bind]
    apply congrArg (fun rest => (globals.map (·.ty)).filter (fun ty => !ty.hasCanonicalMemoryLayout) ++ rest)
    apply congrArg (fun callback => (trustIrListBind functions callback))
    funext function
    cases body : function.blocks with
    | error error => simp only [functionImageRoots, body, List.filter]
    | ok rows => simp only [functionImageRoots, body, graphImageRoots, blockImageRoots, filter_bind]
  }

private def eraseFunctions (context : EvalContext) : EvalContext :=
  {context with functions := fun _ => none}

/-- Actual context assembly retains every field other than executable bodies.
    Its lazy errors are all absent after successful factory preparation. -/
private theorem contextOf_erased_produced (source : Module) (targets : List Function)
    (produced : Produced source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions targets)
    (maxDepth : Nat) :
    (contextOf source maxDepth).map eraseFunctions =
      (contextOf {source with functions := targets} maxDepth).map eraseFunctions := by
  trustIrCompilerProof {
    have law := produced_law _ _ produced
    obtain ⟨updates, sourceEntries, targetEntries, _replacements, sourceDecoded, targetDecoded⟩ :=
      produced_evaluated _ _ produced
    dsimp only [executableEntries] at sourceEntries targetEntries
    have originalHeaders := headers_original source.funcTys.toArray law
    have valueSource (selected : D ByteModel) :
        valueSourceOf {source with byteModel := selected, functions := targets} = valueSourceOf source :=
      produced_valueSource {source with byteModel := selected} targets produced
    have storageHeaders := header_functions law
    have indexes := law.headerIndex source.funcTys.toArray
    have order := header_ids law
    have declarations := header_declared law
    have roots := produced_imageRoots _ _ produced source.types
    cases model : source.byteModel with
    | error error => simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, Except.map]
    | ok byteModel =>
      cases typed : source.funcTys.any (fun signature => signature.abi.isSome) with
      | true => simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, if_true,
          unsupported, Except.map, throw]
      | false =>
        simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, Bool.false_eq_true,
          if_false, HeaderMaps.localTypeHeadersOf_eq, indexes, Pure.pure, Except.pure, Except.map]
        simp only [eraseFunctions, originalHeaders, valueSource,
          sourceEntries, targetEntries, order, declarations, dropGlueOf]
        congr 1
        simp only [memoryServiceOf_eq, memoryRootsOfInst_eq, storageHeaders]
        have rootsEqual := congrArg (fun rest =>
          (source.globals.map (·.ty)).filter (fun ty => !ty.hasCanonicalMemoryLayout) ++ rest) roots
        congr 1
        · congr 2
          change (List.filter (fun ty => !ty.hasCanonicalMemoryLayout)
            ([Ty.I64] ++ source.globals.map (·.ty) ++ source.functions.bind (fun function =>
              match function.blocks with
              | .error _ => []
              | .ok rows => rows.bind (fun row => (row.2.body ++ [row.2.terminator]).bind (imageRoots source.types))))) =
            List.filter (fun ty => !ty.hasCanonicalMemoryLayout)
              ([Ty.I64] ++ source.globals.map (·.ty) ++ targets.bind (fun function =>
                match function.blocks with
                | .error _ => []
                | .ok rows => rows.bind (fun row => (row.2.body ++ [row.2.terminator]).bind (imageRoots source.types))))
          rw [roots_filter, roots_filter]
          exact rootsEqual.symm
        · funext id
          have projected := congrArg (fun table => table.find? id.index) originalHeaders
          exact projected.symm
        · funext id
          have sourceProjection := congrArg (fun entries => functionErrorsView source.functions entries id) sourceEntries
          have targetProjection := congrArg (fun entries => functionErrorsView targets entries id) targetEntries
          exact sourceProjection.trans
            ((function_errors_none source.functions sourceDecoded FunctionUpdate.source updates id).trans
              ((function_errors_none targets targetDecoded FunctionUpdate.target updates id).symm.trans targetProjection.symm))
  } {
    have originalExecutableErrorRuntimeDispatch {α : Type}
        (selected : Option (FuncId × D EvalFunction))
        (onMalformed : FuncId → String → α)
        (onUnsupported : FuncId → String → α)
        (onOther : Option (FuncId × D EvalFunction) → α) :
        FunctionLookup.findError_prepare.match_1 (fun _ => α) selected
          onMalformed onUnsupported onOther =
        (match selected with
         | some (key, Except.error (.malformed message)) => onMalformed key message
         | some (key, Except.error (.unsupported feature)) => onUnsupported key feature
         | other => onOther other) := by
      cases selected with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result with
        | ok function => rfl
        | error error => cases error <;> rfl
    have originalCanonicalSourceDispatch {α : Type} (selected : Option Function)
        (onSome : Function → α) (onNone : Unit → α) :
        FunctionLookup.findError_prepare.match_6 (fun _ => α) selected onSome onNone =
        (match selected with
         | some function => onSome function
         | none => onNone ()) := by
      cases selected <;> rfl
    have originalCanonicalBlocksDispatch {α : Type}
        (selected : Except DecodeError (List (BlockId × BasicBlock)))
        (onUnsupported : String → α) (onMalformed : String → α)
        (onBlocks : List (BlockId × BasicBlock) → α) :
        FunctionLookup.findError_prepare.match_4 (fun _ => α) selected
          onUnsupported onMalformed onBlocks =
        (match selected with
         | .error (.unsupported feature) => onUnsupported feature
         | .error (.malformed message) => onMalformed message
         | .ok blocks => onBlocks blocks) := by
      cases selected with
      | error error => cases error <;> rfl
      | ok blocks => rfl
    have law := produced_law _ _ produced
    obtain ⟨updates, sourceEntries, targetEntries, _replacements, sourceDecoded, targetDecoded⟩ :=
      produced_evaluated _ _ produced
    dsimp only [executableEntries] at sourceEntries targetEntries
    have originalHeaders := headers_original source.funcTys.toArray law
    have valueSource (selected : D ByteModel) :
        valueSourceOf {source with byteModel := selected, functions := targets} = valueSourceOf source :=
      produced_valueSource {source with byteModel := selected} targets produced
    have storageHeaders := header_functions law
    have indexes := law.headerIndex source.funcTys.toArray
    have order := header_ids law
    have declarations := header_declared law
    have roots := produced_imageRoots _ _ produced source.types
    cases model : source.byteModel with
    | error error => simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, Except.map]
    | ok byteModel =>
      cases typed : source.funcTys.any (fun signature => signature.abi.isSome) with
      | true => simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, if_true,
          unsupported, Except.map, throw]
      | false =>
        simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, Bool.false_eq_true,
          if_false, HeaderMaps.localTypeHeadersOf_eq, indexes, Pure.pure, Except.pure, Except.map]
        simp only [eraseFunctions, originalHeaders, valueSource,
          sourceEntries, targetEntries, order, declarations, dropGlueOf]
        congr 1
        simp only [memoryServiceOf_eq, memoryRootsOfInst_eq, storageHeaders]
        have rootsEqual := congrArg (fun rest =>
          (source.globals.map (·.ty)).filter (fun ty => !ty.hasCanonicalMemoryLayout) ++ rest) roots
        congr 1
        · congr 2
          change (List.filter (fun ty => !ty.hasCanonicalMemoryLayout)
            ([Ty.I64] ++ source.globals.map (·.ty) ++ (trustIrListBind source.functions (fun function =>
              match function.blocks with
              | .error _ => []
              | .ok rows => (trustIrListBind rows (fun row => (trustIrListBind (row.2.body ++ [row.2.terminator]) (imageRoots source.types)))))))) =
            List.filter (fun ty => !ty.hasCanonicalMemoryLayout)
              ([Ty.I64] ++ source.globals.map (·.ty) ++ (trustIrListBind targets (fun function =>
                match function.blocks with
                | .error _ => []
                | .ok rows => (trustIrListBind rows (fun row => (trustIrListBind (row.2.body ++ [row.2.terminator]) (imageRoots source.types)))))))
          rw [roots_filter, roots_filter]
          exact rootsEqual.symm
        · funext id
          have projected := congrArg (fun table => table.find? id.index) originalHeaders
          exact projected.symm
        · funext id
          have sourceProjection := congrArg (fun entries => functionErrorsView source.functions entries id) sourceEntries
          have targetProjection := congrArg (fun entries => functionErrorsView targets entries id) targetEntries
          simpa only [functionErrorsView, originalExecutableErrorRuntimeDispatch,
            originalCanonicalSourceDispatch, originalCanonicalBlocksDispatch] using sourceProjection.trans
            ((function_errors_none source.functions sourceDecoded FunctionUpdate.source updates id).trans
              ((function_errors_none targets targetDecoded FunctionUpdate.target updates id).symm.trans targetProjection.symm))
  }

private theorem erase_installFirst (choose : FunctionUpdate → EvalFunction)
    (base : EvalContext) (updates : List FunctionUpdate) :
    eraseFunctions (installFirst choose base updates) = eraseFunctions base := by
  induction updates with
  | nil => rfl
  | cons _head _rest ih => exact ih

private theorem context_eq_of_erased (source target : EvalContext)
    (erased : eraseFunctions source = eraseFunctions target) (functions : source.functions = target.functions) :
    source = target := by
  calc
    source = {eraseFunctions source with functions := source.functions} := rfl
    _ = {eraseFunctions target with functions := target.functions} := by rw [erased, functions]
    _ = target := rfl

private theorem framedCalls_of_entries (source target : EvalContext) (updates : List FunctionUpdate)
    (replacements : ∀ update ∈ updates, FactoryReplacement update.source update.target)
    (erased : eraseFunctions source = eraseFunctions target)
    (sourceLookup : ∀ id, source.functions id = match updates.find? (fun update => id == update.id) with
      | some update => some update.source | none => none)
    (targetLookup : ∀ id, target.functions id = match updates.find? (fun update => id == update.id) with
      | some update => some update.target | none => none) :
    FramedCallsEquivalent source target := by
  have sourceRepresentation : installFirst FunctionUpdate.source (eraseFunctions source) updates = source := by
    apply context_eq_of_erased
    · exact erase_installFirst _ _ _
    · funext id
      rw [installFirst_functions, sourceLookup id]
      cases updates.find? (fun update => id == update.id) <;> rfl
  have targetRepresentation : installFirst FunctionUpdate.target (eraseFunctions source) updates = target := by
    apply context_eq_of_erased
    · exact (erase_installFirst _ _ _).trans erased
    · funext id
      rw [installFirst_functions, targetLookup id]
      cases updates.find? (fun update => id == update.id) <;> rfl
  have related := installFirst_framedCallsEquivalent updates replacements (eraseFunctions source)
  rw [sourceRepresentation, targetRepresentation] at related
  exact related

private theorem contextOf_functions (module : Module) (maxDepth : Nat) (context : EvalContext)
    (actual : contextOf module maxDepth = .ok context) :
    context.functions = fun id => match (executableEntries (localTypeHeadersOf module).1
      (localTypeHeadersOf module).2 module.functions).find? (fun row => row.1 == id) with
      | some (_, Except.ok function) => some function
      | _ => none := by
  trustIrCompilerProof {
    cases model : module.byteModel with
    | error error => simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind] at actual
    | ok byteModel =>
      cases typed : module.funcTys.any (fun signature => signature.abi.isSome) with
      | true => simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, if_true,
          unsupported] at actual
      | false =>
        simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, Bool.false_eq_true,
          if_false, Pure.pure, Except.pure, Except.ok.injEq] at actual
        cases actual
        rfl
  } {
    have originalExecutableRuntimeDispatch {α : Type}
        (selected : Option (FuncId × D EvalFunction))
        (onFunction : FuncId → EvalFunction → α)
        (onOther : Option (FuncId × D EvalFunction) → α) :
        FunctionLookup.findFunction_prepare.match_1 (fun _ => α) selected onFunction onOther =
        (match selected with
         | some (key, Except.ok function) => onFunction key function
         | other => onOther other) := by
      cases selected with
      | none => rfl
      | some row =>
        rcases row with ⟨key, result⟩
        cases result <;> rfl
    have error_ne_ok : ∀ {ε α : Type} (error : ε) (value : α),
        (Except.error error : Except ε α) ≠ Except.ok value := by
      intro ε α error value impossible
      cases impossible
    cases model : module.byteModel with
    | error error =>
      simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
        FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind] at actual
      exact False.elim (error_ne_ok _ _ actual)
    | ok byteModel =>
      cases typed : module.funcTys.any (fun signature => signature.abi.isSome) with
      | true =>
        simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, if_true,
          unsupported] at actual
        exact False.elim (error_ne_ok _ _ actual)
      | false =>
        simp only [contextOf, FunctionLookup.findFunction_prepare, FunctionLookup.findError_prepare,
          FunctionLookup.isDeclared_prepare, model, Bind.bind, Except.bind, typed, Bool.false_eq_true,
          if_false, Pure.pure, Except.pure, Except.ok.injEq] at actual
        cases actual
        simp only [originalExecutableRuntimeDispatch] <;> rfl
  }

trustIrDenseMatch
/-- Equality of context-construction failures or equality of actual framed
    calls at all entries after successful construction. -/
def ContextCallsEquivalent : D EvalContext → D EvalContext → Prop
  | Except.error source, Except.error target => source = target
  | Except.ok source, Except.ok target => FramedCallsEquivalent source target
  | _, _ => False

/-- The actual positional producer, interpreted by the original executable
    context assembly. Duplicate ids retain the first executable occurrence;
    declarations continue to supply headers without becoming executable. -/
theorem produced_context_calls (source : Module) (targets : List Function)
    (produced : Produced source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions targets)
    (maxDepth : Nat) :
    ContextCallsEquivalent (contextOf source maxDepth)
      (contextOf {source with functions := targets} maxDepth) := by
  trustIrCompilerProof {
    have erased := contextOf_erased_produced source targets produced maxDepth
    obtain ⟨updates, sourceEntries, targetEntries, replacements, _sourceDecoded, _targetDecoded⟩ :=
      produced_evaluated _ _ produced
    have indexes := (produced_law _ _ produced).headerIndex source.funcTys.toArray
    cases sourceActual : contextOf source maxDepth with
    | error error =>
      cases targetActual : contextOf {source with functions := targets} maxDepth with
      | error targetError =>
        simp only [sourceActual, targetActual, Except.map, Except.error.injEq] at erased
        exact erased
      | ok targetContext => simp only [sourceActual, targetActual, Except.map] at erased
    | ok sourceContext =>
      cases targetActual : contextOf {source with functions := targets} maxDepth with
      | error error => simp only [sourceActual, targetActual, Except.map] at erased
      | ok targetContext =>
        simp only [sourceActual, targetActual, Except.map, Except.ok.injEq] at erased
        have sourceFunctions := contextOf_functions source maxDepth sourceContext sourceActual
        have targetFunctions := contextOf_functions {source with functions := targets} maxDepth targetContext targetActual
        simp only [HeaderMaps.localTypeHeadersOf_eq, indexes] at sourceFunctions targetFunctions
        apply framedCalls_of_entries sourceContext targetContext updates replacements erased
        · intro id
          have projection := congrArg (fun entries : List (FuncId × D EvalFunction) => match entries.find? (fun row => row.1 == id) with
            | some (_, Except.ok function) => some function | _ => none) sourceEntries
          have sourceAt := (congrFun sourceFunctions id).trans projection
          have selected := congrArg (fun found : Option (FuncId × D EvalFunction) => match found with
            | some (_, Except.ok function) => some function | _ => none)
            (entries_find FunctionUpdate.source updates id)
          have full := sourceAt.trans selected
          cases found : updates.find? (fun update => id == update.id) <;>
            simpa only [found, Option.map] using full
        · intro id
          have projection := congrArg (fun entries : List (FuncId × D EvalFunction) => match entries.find? (fun row => row.1 == id) with
            | some (_, Except.ok function) => some function | _ => none) targetEntries
          have targetAt := (congrFun targetFunctions id).trans projection
          have selected := congrArg (fun found : Option (FuncId × D EvalFunction) => match found with
            | some (_, Except.ok function) => some function | _ => none)
            (entries_find FunctionUpdate.target updates id)
          have full := targetAt.trans selected
          cases found : updates.find? (fun update => id == update.id) <;>
            simpa only [found, Option.map] using full
  } {
    have error_ne_ok : ∀ {ε α : Type} (error : ε) (value : α),
        (Except.error error : Except ε α) ≠ Except.ok value := by
      intro ε α error value impossible
      cases impossible
    have erased := contextOf_erased_produced source targets produced maxDepth
    obtain ⟨updates, sourceEntries, targetEntries, replacements, _sourceDecoded, _targetDecoded⟩ :=
      produced_evaluated _ _ produced
    have indexes := (produced_law _ _ produced).headerIndex source.funcTys.toArray
    cases sourceActual : contextOf source maxDepth with
    | error error =>
      cases targetActual : contextOf {source with functions := targets} maxDepth with
      | error targetError =>
        simp only [sourceActual, targetActual, Except.map, Except.error.injEq] at erased
        exact erased
      | ok targetContext =>
        simp only [sourceActual, targetActual, Except.map] at erased
        exact False.elim (error_ne_ok _ _ erased)
    | ok sourceContext =>
      cases targetActual : contextOf {source with functions := targets} maxDepth with
      | error error =>
        simp only [sourceActual, targetActual, Except.map] at erased
        exact False.elim (error_ne_ok _ _ erased.symm)
      | ok targetContext =>
        simp only [sourceActual, targetActual, Except.map, Except.ok.injEq] at erased
        have sourceFunctions := contextOf_functions source maxDepth sourceContext sourceActual
        have targetFunctions := contextOf_functions {source with functions := targets} maxDepth targetContext targetActual
        simp only [HeaderMaps.localTypeHeadersOf_eq, indexes] at sourceFunctions targetFunctions
        apply framedCalls_of_entries sourceContext targetContext updates replacements erased
        · intro id
          have projection := congrArg (fun entries : List (FuncId × D EvalFunction) => match entries.find? (fun row => row.1 == id) with
            | some (_, Except.ok function) => some function | _ => none) sourceEntries
          have sourceAt := (congrFun sourceFunctions id).trans projection
          have selected := congrArg (fun found : Option (FuncId × D EvalFunction) => match found with
            | some (_, Except.ok function) => some function | _ => none)
            (entries_find FunctionUpdate.source updates id)
          have full := sourceAt.trans selected
          cases found : updates.find? (fun update => id == update.id) <;>
            simpa only [found, Option.map] using full
        · intro id
          have projection := congrArg (fun entries : List (FuncId × D EvalFunction) => match entries.find? (fun row => row.1 == id) with
            | some (_, Except.ok function) => some function | _ => none) targetEntries
          have targetAt := (congrFun targetFunctions id).trans projection
          have selected := congrArg (fun found : Option (FuncId × D EvalFunction) => match found with
            | some (_, Except.ok function) => some function | _ => none)
            (entries_find FunctionUpdate.target updates id)
          have full := targetAt.trans selected
          cases found : updates.find? (fun update => id == update.id) <;>
            simpa only [found, Option.map] using full
  }

/-- A successful actual ModuleFactory publication preserves construction
    errors and every real framed call. No per-entry semantic relation is
    assumed, and no runtime planner is rerun by this proof. -/
theorem transform_ready_context_calls (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat) :
    ContextCallsEquivalent (contextOf source maxDepth) (contextOf target maxDepth) := by
  have fields := (ModuleFactory.transform_ready source target actual).1
  have targetEq : target = {source with functions := target.functions} := by
    have updated := congrArg (fun module : Module => {module with functions := target.functions}) fields
    exact updated
  have produced := ModuleFactory.transform_produced source target actual
  have related := produced_context_calls source target.functions produced maxDepth
  rw [← targetEq] at related
  exact related

/-- Complete Sem equality at any requested function, both zero budgets,
    arbitrary arguments/panic strategy and arbitrary caller state. -/
theorem transform_ready_runCallReq (source target : Module)
    (actual : ModuleFactory.transform source = .ready target) (maxDepth : Nat)
    (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf target maxDepth = .ok targetContext)
    (requested : FuncId) (fuel depth : Nat) (args : List Value) (strategy : PanicStrategy)
    (caller : MachineState) :
    Sem.run (runCallReq sourceContext fuel depth requested args strategy) caller =
      Sem.run (runCallReq targetContext fuel depth requested args strategy) caller := by
  have related := transform_ready_context_calls source target actual maxDepth
  rw [sourceBuilt, targetBuilt] at related
  exact FramedCallsEquivalent.run related requested fuel depth args strategy caller

end TrustIr.GenericCoro.ModuleContext

namespace TrustIr.GenericCoro.ModuleContext
open TrustIrEval GenericCoroAllBlocksPlanner GenericCoroFreshIds
open AllBlocksContext ModuleFactory

/-- Actual produced contexts are literal first-executable-wins installations
    over ONE common non-function context. Each occurrence carries genuine
    factory provenance; this package asserts no semantic relation. -/
theorem produced_context_updates (source : Module) (targets : List Function)
    (produced : Produced source.funcTys.toArray
      (directHeaders (headerIndex source.funcTys.toArray source.functions)) source.functions targets)
    (maxDepth : Nat) (sourceContext targetContext : EvalContext)
    (sourceBuilt : contextOf source maxDepth = .ok sourceContext)
    (targetBuilt : contextOf {source with functions := targets} maxDepth = .ok targetContext) :
    ∃ (base : EvalContext) (updates : List FunctionUpdate),
      sourceContext = installFirst FunctionUpdate.source base updates ∧
      targetContext = installFirst FunctionUpdate.target base updates ∧
      (∀ update ∈ updates, FactoryReplacement update.source update.target) := by
  have erased := contextOf_erased_produced source targets produced maxDepth
  simp only [sourceBuilt, targetBuilt, Except.map, Except.ok.injEq] at erased
  obtain ⟨updates, sourceEntries, targetEntries, replacements, _sourceDecoded, _targetDecoded⟩ :=
    produced_evaluated _ _ produced
  have indexes := (produced_law _ _ produced).headerIndex source.funcTys.toArray
  have sourceFunctions := contextOf_functions source maxDepth sourceContext sourceBuilt
  have targetFunctions := contextOf_functions {source with functions := targets} maxDepth targetContext targetBuilt
  simp only [HeaderMaps.localTypeHeadersOf_eq, indexes] at sourceFunctions targetFunctions
  have sourceLookup : ∀ id, sourceContext.functions id =
      match updates.find? (fun update => id == update.id) with
      | some update => some update.source | none => none := by
    intro id
    have projection := congrArg (fun entries : List (FuncId × D EvalFunction) => match entries.find? (fun row => row.1 == id) with
      | some (_, Except.ok function) => some function | _ => none) sourceEntries
    have sourceAt := (congrFun sourceFunctions id).trans projection
    have selected := congrArg (fun found : Option (FuncId × D EvalFunction) => match found with
      | some (_, Except.ok function) => some function | _ => none)
      (entries_find FunctionUpdate.source updates id)
    have full := sourceAt.trans selected
    cases found : updates.find? (fun update => id == update.id) <;>
      simpa only [found, Option.map] using full
  have targetLookup : ∀ id, targetContext.functions id =
      match updates.find? (fun update => id == update.id) with
      | some update => some update.target | none => none := by
    intro id
    have projection := congrArg (fun entries : List (FuncId × D EvalFunction) => match entries.find? (fun row => row.1 == id) with
      | some (_, Except.ok function) => some function | _ => none) targetEntries
    have targetAt := (congrFun targetFunctions id).trans projection
    have selected := congrArg (fun found : Option (FuncId × D EvalFunction) => match found with
      | some (_, Except.ok function) => some function | _ => none)
      (entries_find FunctionUpdate.target updates id)
    have full := targetAt.trans selected
    cases found : updates.find? (fun update => id == update.id) <;>
      simpa only [found, Option.map] using full
  have sourceRepresentation : installFirst FunctionUpdate.source (eraseFunctions sourceContext) updates = sourceContext := by
    apply context_eq_of_erased
    · exact erase_installFirst _ _ _
    · funext id
      rw [installFirst_functions, sourceLookup id]
      cases updates.find? (fun update => id == update.id) <;> rfl
  have targetRepresentation : installFirst FunctionUpdate.target (eraseFunctions sourceContext) updates = targetContext := by
    apply context_eq_of_erased
    · exact (erase_installFirst _ _ _).trans erased
    · funext id
      rw [installFirst_functions, targetLookup id]
      cases updates.find? (fun update => id == update.id) <;> rfl
  exact ⟨eraseFunctions sourceContext, updates, sourceRepresentation.symm,
    targetRepresentation.symm, replacements⟩

end TrustIr.GenericCoro.ModuleContext

/-- info: 'TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.ModuleContext.ContextCallsEquivalent.match_1
