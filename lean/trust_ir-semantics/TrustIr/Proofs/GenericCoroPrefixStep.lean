-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixReaders

namespace TrustIr.GenericCoro.Prefix

theorem stepInstWithContext_const_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (ty : Ty) (constant : Constant) :
    stepInstWithContext (scopedContext base functions types) (.Const ty constant) =
      stepInstWithContext base (.Const ty constant) := by
  cases constant <;> simp only [stepInstWithContext, constValueAtWithDefs_scoped] <;> rfl

/-- A contextual leaf observes callable headers and the declarations of its
    actual operands. The extra fresh rows of an expansion remain irrelevant. -/
theorem stepInstWithContext_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (inst : Inst)
    (types : TypesAgreeOn (operandIds inst) sourceTypes targetTypes) :
    stepInstWithContext (scopedContext base source sourceTypes) inst =
      stepInstWithContext (scopedContext base target targetTypes) inst := by
  cases inst
  case Const ty constant =>
    rw [stepInstWithContext_const_scoped, stepInstWithContext_const_scoped]
  case BinOp op ty lhs rhs => cases ty <;> rfl
  case Undef ty => cases ty <;> rfl
  case ArraySplat ty valueId =>
    cases types with
    | absent =>
      simp only [stepInstWithContext, scopedContext]
    | present sourceTable targetTable agree =>
      have read := agree valueId ((trustIrListMemConsSelf _ _))
      simp only [stepInstWithContext, scopedContext, pure_bind, read]
  case Alloca ty count align =>
    simp only [stepInstWithContext]
    have equal := semAllocateUsing_reader_congr base.memoryLayout
      (scopedContext base source sourceTypes).carrierIntegerOperand
      (scopedContext base target targetTypes).carrierIntegerOperand
      ty count align .rustStack false 0 base.byteModel (fun id member value => by
        exact carrierIntegerOperand_congr base source target sourceTypes targetTypes id
          (types.mono (fun queried present => by
            have same : queried = id := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
            subst queried
            cases count with
            | none => cases member
            | some countId => cases member; exact (trustIrListMemConsSelf _ _))) value)
    exact congrArg (fun (action : Sem ValueId) => do
      let id ← action
      pure (InstrResult.value (some id))) equal
  case HeapAlloc ty count align origin =>
    simp only [stepInstWithContext]
    have equal := semAllocateUsing_reader_congr base.memoryLayout
      (scopedContext base source sourceTypes).carrierIntegerOperand
      (scopedContext base target targetTypes).carrierIntegerOperand
      ty count align origin.toAllocationOrigin origin.isRefCounted heapUsableSlack base.byteModel
      (fun id member value => by
        exact carrierIntegerOperand_congr base source target sourceTypes targetTypes id
          (types.mono (fun queried present => by
            have same : queried = id := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
            subst queried
            cases count with
            | none => cases member
            | some countId => cases member; exact (trustIrListMemConsSelf _ _))) value)
    exact congrArg (fun (action : Sem ValueId) => do
      let id ← action
      pure (InstrResult.value (some id))) equal
  case GEP ty pointer indices inbounds =>
    simp only [stepInstWithContext]
    have equal := semGEPUsing_reader_congr base.memoryLayout
      (scopedContext base source sourceTypes).carrierIntegerOperand
      (scopedContext base target targetTypes).carrierIntegerOperand ty pointer indices base.byteModel
      (fun id member value => carrierIntegerOperand_congr base source target sourceTypes targetTypes id
        (types.mono (fun queried present => by
          have same : queried = id := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
          subst queried
          exact List.mem_cons_of_mem pointer member)) value)
    exact congrArg (fun (action : Sem ValueId) => do
      let id ← action
      pure (InstrResult.value (some id))) equal
  case ExtractElement ty array index =>
    have equal : (scopedContext base source sourceTypes).elementIndex index =
        (scopedContext base target targetTypes).elementIndex index := by
      funext value
      exact elementIndex_congr base source target sourceTypes targetTypes index
        (types.mono (fun queried present => by
          have same : queried = index := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
          subst queried
          exact List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _)))) value
    simp only [stepInstWithContext, equal]
  case InsertElement ty array index value =>
    have equal : (scopedContext base source sourceTypes).elementIndex index =
        (scopedContext base target targetTypes).elementIndex index := by
      funext value
      exact elementIndex_congr base source target sourceTypes targetTypes index
        (types.mono (fun queried present => by
          have same : queried = index := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
          subst queried
          exact List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _)))) value
    simp only [stepInstWithContext, equal]
  case MakeClosure cid fn captures =>
    simp only [stepInstWithContext, makeClosureValue_congr base source target headers sourceTypes targetTypes]
  case MakeAggregate ty variant fields =>
    cases ty <;> simp only [stepInstWithContext, makeAggregateValueWithContext_scoped] <;> try rfl
    case Array element count =>
      have arrays : ∀ lanes,
          makeArrayValueWithContext (scopedContext base source sourceTypes) element count variant fields lanes =
          makeArrayValueWithContext (scopedContext base target targetTypes) element count variant fields lanes := by
        intro lanes
        exact makeArrayValueWithContext_congr base source target sourceTypes targetTypes element count variant fields lanes types
      simp only [arrays]
  case ExtractField ty aggregateId field =>
    have check : ∀ held,
        checkDeclaredField (scopedContext base source sourceTypes) aggregateId held field ty =
        checkDeclaredField (scopedContext base target targetTypes) aggregateId held field ty := by
      intro held
      exact checkDeclaredField_congr base source target sourceTypes targetTypes aggregateId types held field ty
    simp only [stepInstWithContext, closureExtract_scoped, check]
    rfl
  case InsertField ty aggregateId field valueId =>
    have check : ∀ held accessTy,
        checkDeclaredField (scopedContext base source sourceTypes) aggregateId held field accessTy =
        checkDeclaredField (scopedContext base target targetTypes) aggregateId held field accessTy := by
      intro held accessTy
      exact checkDeclaredField_congr base source target sourceTypes targetTypes aggregateId
        (types.mono (fun queried present => by
          have same : queried = aggregateId := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
          subst queried
          exact (trustIrListMemConsSelf _ _))) held field accessTy
    simp only [stepInstWithContext, closureInsert_scoped, check]
    cases types with
    | absent => rfl
    | present sourceTable targetTable agree =>
      have aggregate := agree aggregateId ((trustIrListMemConsSelf _ _))
      have inserted := agree valueId (List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _)))
      simp only [scopedContext, aggregate, inserted]
  all_goals rfl

end TrustIr.GenericCoro.Prefix
