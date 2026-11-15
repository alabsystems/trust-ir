-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixMetadata

namespace TrustIr.GenericCoro.Prefix

theorem resolveDrop_operands (ctx : EvalContext) (inst : Inst) :
    operandIds (ctx.resolveDrop inst) = operandIds inst := by
  cases inst
  case Drop ty pointer =>
    cases found : ctx.dropGlue ty <;> simp only [EvalContext.resolveDrop, found, operandIds, List.cons_append, List.nil_append]
  case DropInvoke ty pointer normalDest normalArgs unwindDest =>
    cases found : ctx.dropGlue ty <;> simp only [EvalContext.resolveDrop, found, operandIds, List.cons_append, List.nil_append]
  all_goals rfl

theorem resolveDrop_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (inst : Inst) : (scopedContext base functions types).resolveDrop inst = base.resolveDrop inst := rfl

theorem resolveBlock_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (block : BasicBlock) : (scopedContext base functions types).resolveBlock block = base.resolveBlock block := rfl

theorem bodyInsts_resolve (ctx : EvalContext) (body : List Inst)
    (dests : List (List ValueId)) :
    bodyInstsWithResultDests (body.map ctx.resolveDrop) dests =
      (bodyInstsWithResultDests body dests).map (fun row => (ctx.resolveDrop row.1, row.2)) := by
  induction body generalizing dests with
  | nil => rfl
  | cons inst body ih =>
    cases dests with
    | nil => simp only [List.map_cons, bodyInstsWithResultDests, ih]
    | cons dest dests => simp only [List.map_cons, bodyInstsWithResultDests, ih]

theorem graphNode_ids (blocks : List (BlockId × BasicBlock))
    (row : Inst × List ValueId) (member : row ∈ graphNodes blocks)
    (id : ValueId) (inRow : id ∈ row.2 ++ operandIds row.1) :
    id ∈ graphValueIds blocks :=
  trustIrListMemAppendRight _ (trustIrListMemAppendLeft _
    (mem_bind_of_mem (fun row => row.2 ++ operandIds row.1) (graphNodes blocks) row id member inRow))

theorem resolvedRow_typesAgree (base : EvalContext)
    (blocks : List (BlockId × BasicBlock)) (source target : LocalTypeTable)
    (same : ∀ id ∈ graphValueIds blocks, source id = target id)
    (row : Inst × List ValueId) (member : row ∈ graphNodes blocks) :
    TypesAgreeOn (row.2 ++ operandIds (base.resolveDrop row.1)) (some source) (some target) := by
  refine .present source target ?_
  intro id inRow
  rw [resolveDrop_operands] at inRow
  exact same id (graphNode_ids blocks row member id inRow)

theorem entry_body_mem_graphNodes (blocks : List (BlockId × BasicBlock))
    (entry : BlockId) (block : BasicBlock) (found : cfgOf blocks entry = some block)
    (row : Inst × List ValueId)
    (member : row ∈ bodyInstsWithResultDests block.body block.bodyResultDests) :
    row ∈ graphNodes blocks := by
  obtain ⟨before, id, after, decomposition, selected, noMatch⟩ :=
    cfgOf_decompose blocks entry block found
  rw [decomposition, graphNodes_append, graphNodes_cons]
  exact trustIrListMemAppendRight _
    (trustIrListMemAppendLeft _ (trustIrListMemAppendLeft _ member))

end TrustIr.GenericCoro.Prefix
