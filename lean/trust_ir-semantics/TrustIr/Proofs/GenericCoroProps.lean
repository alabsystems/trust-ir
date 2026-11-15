-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSACharProps
import TrustIr.Proofs.CallProps
import TrustIr.Proofs.HeldMemoryFrames
import TrustIr.Proofs.SSAFreshFrames
import TrustIr.Proofs.MetaTheorems
import TrustIr.Proofs.LocalTypeInferenceProps
import TrustIr.Proofs.GenericCoroFreshIds

/-- Select the actual standard list flattening operation on each compiler. -/
macro "trustIrCoroFlatten" : term => do
  if Lean.versionString == "4.8.0" then `(List.join)
  else if Lean.versionString == "4.30.0-rc2" then `(List.flatten)
  else Lean.Macro.throwError "unsupported compiler for coroutine list flattening"

macro "trustIrCoroListLemma " oldName:ident newName:ident : term => do
  if Lean.versionString == "4.8.0" then pure oldName
  else if Lean.versionString == "4.30.0-rc2" then pure newName
  else Lean.Macro.throwError "unsupported compiler for coroutine list lemmas"

namespace TrustIr.GenericCoro

/-! Source graph construction for coroutine entry expansion. The identifier
inventory includes uses as well as definitions: a new declaration must never
turn a formerly undefined source operand into a typed value. The intra-callee
relation hides only SSA storage; the real Call boundary restores caller SSA
storage and must preserve every other field, including float choice state. -/

def assertValueIds : AssertKind → List ValueId
  | .BoundsCheck index length => [index, length]
  | .MisalignedPtr required found => [required, found]
  | .Unspecified | .Overflow _ | .DivByZero | .RemByZero | .NullPtr => []

def siteValueIds (site : PanicSite) : List ValueId :=
  match site.location with
  | .value id => [id]
  | .global _ => []

/-- Every SSA operand carried by a source instruction, including edge and
    panic-message operands. FuncId, BlockId and plain numeric fields are not
    SSA operands. This match is exhaustive over the actual instruction type. -/
def operandIds : Inst → List ValueId
  | .BinOp _ _ lhs rhs | .Overflow _ _ lhs rhs | .ICmp _ _ lhs rhs
  | .FCmp _ _ lhs rhs => [lhs, rhs]
  | .UnOp _ _ value | .Cast _ _ _ value | .Load _ value _ _
  | .AtomicLoad _ value _ | .ExtractField _ value _ | .Copy _ value
  | .ArraySplat _ value | .SeqMapAddK _ value _ | .SeqMapNot _ value
  | .SeqMap _ value _ | .PtrData _ value | .PtrMetadata _ _ value
  | .Assume value | .Borrow value | .BorrowMut value | .EndBorrow value
  | .Retain value | .Release value | .IsUnique value | .Dealloc value
  | .Drop _ value | .LoadSlot value _ _ | .CloseFrame value | .Resume value => [value]
  | .Store _ pointer value _ _ | .AtomicStore _ pointer value _
  | .AtomicRMW _ _ pointer value _ | .PtrFromParts _ _ pointer value
  | .InsertField _ pointer _ value | .BindSlot pointer _ value => [pointer, value]
  | .Alloca _ count _ | .HeapAlloc _ count _ _ => count.toList
  | .GEP _ base indices _ => base :: indices
  | .CmpXchg _ pointer expected desired _ _ _ => [pointer, expected, desired]
  | .Br _ args | .Call _ args | .CallCannotUnwind _ args | .Return args
  | .MakeAggregate _ _ args | .MakeClosure _ _ args => args
  | .CondBr condition _ thenArgs _ elseArgs => condition :: (thenArgs ++ elseArgs)
  | .Switch value _ defaultArgs cases _ => value :: (defaultArgs ++ trustIrListBind cases (·.args))
  | .CallIndirect callee _ args _ | .CallIndirectCannotUnwind callee _ args _ => callee :: args
  | .ExtractElement _ array index => [array, index]
  | .InsertElement _ array index value | .Select _ array index value => [array, index, value]
  | .Assert condition kind site =>
    condition :: (assertValueIds kind ++ trustIrListBind site.toList siteValueIds)
  | .MemCopy destination source bytes _ | .MemSet destination source bytes =>
    [destination, source, bytes]
  | .CoroSuspend frame _ _ value => [frame, value]
  | .Invoke _ args _ normalArgs _ => args ++ normalArgs
  | .InvokeIndirect callee _ args _ _ normalArgs _ => callee :: (args ++ normalArgs)
  | .AssertInvoke condition kind site _ normalArgs _ =>
    condition :: (assertValueIds kind ++ siteValueIds site ++ normalArgs)
  | .DropInvoke _ pointer _ normalArgs _ => pointer :: normalArgs
  | .DialectOp instruction => instruction.operands
  | .GlobalAddr _ | .Fence _ | .Const _ _ | .NullPtr | .Undef _ | .Unreachable
  | .OpenFrame _ | .LandingPad _ _ => []

def graphParams (blocks : List (BlockId × BasicBlock)) : List (ValueId × Ty) :=
  trustIrListBind blocks (fun row => row.snd.params)

def graphNodes (blocks : List (BlockId × BasicBlock)) : List (Inst × List ValueId) :=
  trustIrListBind blocks (fun row =>
    bodyInstsWithResultDests row.snd.body row.snd.bodyResultDests ++
      [(row.snd.terminator, row.snd.terminatorResultDests)])

def graphValueIds (blocks : List (BlockId × BasicBlock)) : List ValueId :=
  (graphParams blocks).map Prod.fst ++
  ((trustIrListBind (graphNodes blocks) (fun row => row.snd ++ operandIds row.fst)) ++
  -- Keep even unused raw destination rows in the reservation domain. A
  -- malformed source must never acquire a new meaning through an alias.
  trustIrListBind blocks (fun row => trustIrCoroFlatten row.snd.bodyResultDests))

/-- One greater than every index seen, constructed from the complete finite
    graph rather than from current runtime nextValueId or declared ids alone. -/
def valueBound : List ValueId → Nat
  | [] => 0
  | id :: ids => max (id.index + 1) (valueBound ids)

def freshId (blocks : List (BlockId × BasicBlock)) (offset : Nat) : ValueId :=
  ⟨valueBound (graphValueIds blocks) + offset⟩

/-- Reserve above both every source use and the actual inferred table. The
    latter bound is certified by inference, not supplied by a caller. -/
def inferredFreshId (inference : LocalTypeInference)
    (blocks : List (BlockId × BasicBlock)) (offset : Nat) : ValueId :=
  ⟨max (valueBound (graphValueIds blocks)) inference.keyBound + offset⟩

theorem index_lt_valueBound (ids : List ValueId) (id : ValueId) (h : id ∈ ids) :
    id.index < valueBound ids := by
  induction ids with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with h | h
    · subst id
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)

theorem freshId_not_source (blocks : List (BlockId × BasicBlock)) (offset : Nat) :
    freshId blocks offset ∉ graphValueIds blocks := by
  intro h
  have hBound := index_lt_valueBound _ _ h
  exact Nat.not_lt_of_ge (Nat.le_add_right _ _) hBound

theorem freshId_offset_injective (blocks : List (BlockId × BasicBlock))
    (left right : Nat) (h : freshId blocks left = freshId blocks right) : left = right := by
  have hIndex := congrArg ValueId.index h
  exact Nat.add_left_cancel hIndex

theorem inferredFreshId_not_source (inference : LocalTypeInference)
    (blocks : List (BlockId × BasicBlock)) (offset : Nat) :
    inferredFreshId inference blocks offset ∉ graphValueIds blocks := by
  intro h
  have hBound := index_lt_valueBound _ _ h
  exact Nat.not_lt_of_ge
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)) hBound

theorem inferredFreshId_not_declared (inference : LocalTypeInference)
    (blocks : List (BlockId × BasicBlock)) (offset : Nat) :
    inference.table (inferredFreshId inference blocks offset) = none :=
  inference.outsideBound _
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _))

theorem inferredFreshId_offset_injective (inference : LocalTypeInference)
    (blocks : List (BlockId × BasicBlock)) (left right : Nat)
    (h : inferredFreshId inference blocks left = inferredFreshId inference blocks right) :
    left = right :=
  Nat.add_left_cancel (congrArg ValueId.index h)

theorem mem_map_of_mem {α β : Type} (f : α → β) (list : List α) (item : α)
    (member : item ∈ list) : f item ∈ list.map f := by
  induction list with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | old
    · subst item; exact (trustIrListMemConsSelf _ _)
    · exact List.mem_cons_of_mem (f head) (ih old)

theorem mem_bind_of_mem {α β : Type} (f : α → List β) (list : List α)
    (item : α) (value : β) (rowMember : item ∈ list) (valueMember : value ∈ f item) :
    value ∈ trustIrListBind list f := by
  induction list with
  | nil => cases rowMember
  | cons head rest ih =>
    rw [trustIrCoroListLemma List.cons_bind List.flatMap_cons]
    rcases List.mem_cons.mp rowMember with same | old
    · subst item
      exact trustIrListMemAppendLeft _ valueMember
    · exact trustIrListMemAppendRight _ (ih old)

theorem graphParam_mem (blocks : List (BlockId × BasicBlock))
    (row : ValueId × Ty) (member : row ∈ graphParams blocks) : row.fst ∈ graphValueIds blocks :=
  trustIrListMemAppendLeft _ (mem_map_of_mem Prod.fst _ _ member)

theorem graphNode_dest_mem (blocks : List (BlockId × BasicBlock))
    (row : Inst × List ValueId) (member : row ∈ graphNodes blocks)
    (id : ValueId) (destination : id ∈ row.snd) : id ∈ graphValueIds blocks := by
  have inner : id ∈ row.snd ++ operandIds row.fst := trustIrListMemAppendLeft _ destination
  have inNodes := mem_bind_of_mem (fun row => row.snd ++ operandIds row.fst)
    (graphNodes blocks) row id member inner
  exact trustIrListMemAppendRight _ (trustIrListMemAppendLeft _ inNodes)

theorem graphNode_operand_mem (blocks : List (BlockId × BasicBlock))
    (row : Inst × List ValueId) (member : row ∈ graphNodes blocks)
    (id : ValueId) (operand : id ∈ operandIds row.fst) : id ∈ graphValueIds blocks := by
  have inner : id ∈ row.snd ++ operandIds row.fst := trustIrListMemAppendRight _ operand
  have inNodes := mem_bind_of_mem (fun row => row.snd ++ operandIds row.fst)
    (graphNodes blocks) row id member inner
  exact trustIrListMemAppendRight _ (trustIrListMemAppendLeft _ inNodes)

def cfgOf (blocks : List (BlockId × BasicBlock)) : CFG :=
  fun pc => (blocks.find? (fun row => row.fst == pc)).map Prod.snd

/-- The same authoritative result classifier and original header inputs used
    by decoded functions. No caller-selected table or carrier-derived type is
    installed in a generated function. Metadata failures remain explicit. -/
def functionOfGraph (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) :
    Except SemError EvalFunction := do
  let types ← inferLocalTypes direct indirect (graphParams blocks) (graphNodes blocks)
  pure { header with cfg := cfgOf blocks, localTypes := some types }

/-- A graph function and its support certificate share the very same inference
    run. The table is the ordinary decoder inference projection. -/
def functionOfGraphWithEvidence (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) :
    Except SemError (EvalFunction × LocalTypeInference) := do
  let inferred ← inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks)
  pure ({ header with cfg := cfgOf blocks, localTypes := some inferred.table }, inferred)

theorem functionOfGraphWithEvidence_projection (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) :
    (functionOfGraphWithEvidence direct indirect header blocks).map Prod.fst =
      functionOfGraph direct indirect header blocks := by
  unfold functionOfGraphWithEvidence functionOfGraph inferLocalTypes inferLocalTypesWithWork
  cases inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) <;> rfl

structure Names where
  index : ValueId
  pointer : ValueId
  state : ValueId

def Names.ofTriple {domain : Nat} {used : List Nat}
    (names : GenericCoroFreshIds.Triple domain used) : Names :=
  ⟨⟨names.first⟩, ⟨names.second⟩, ⟨names.third⟩⟩

def graphReservations (blocks : List (BlockId × BasicBlock)) : List Nat :=
  (graphValueIds blocks).map ValueId.index

abbrev GraphNames (blocks : List (BlockId × BasicBlock)) :=
  GenericCoroFreshIds.Triple GenericCoroFreshIds.u32Domain (graphReservations blocks)

trustIrDenseMatch
def expandedEntry (names : Names) (block : BasicBlock) : BasicBlock :=
  match block.terminator with
  | .CoroSuspend frame slot next value =>
    { block with
      body := block.body ++ [.Const .I64 (.int slot), .GEP .I64 frame [names.index] false,
        .Const .I64 (.int next), .Store .I64 names.pointer names.state false none]
      -- Pair precisely the rows the original body actually executes. Raw
      -- trailing rows still reserve names through graphValueIds, but cannot
      -- become destinations of the newly appended instructions.
      bodyResultDests := (bodyInstsWithResultDests block.body block.bodyResultDests).map Prod.snd ++
        [[names.index], [names.pointer], [names.state], []]
      terminator := .Return [value]
      terminatorResultDests := [] }
  | _ => block

/-- Replace the first entry row only, preserving every other source row. In
    particular duplicate block ids do not create duplicate generated ids. -/
def expandFirstEntry (names : Names) (entry : BlockId) :
    List (BlockId × BasicBlock) → List (BlockId × BasicBlock)
  | [] => []
  | (id, block) :: rest =>
    if id == entry then (id, expandedEntry names block) :: rest
    else (id, block) :: expandFirstEntry names entry rest

def expandedGraph (names : Names)
    (blocks : List (BlockId × BasicBlock)) (entry : BlockId) :
    List (BlockId × BasicBlock) := expandFirstEntry names entry blocks

theorem expandedEntry_params (names : Names) (block : BasicBlock) :
    (expandedEntry names block).params = block.params := by
  cases block with
  | mk params body dests term termDests =>
    cases body <;> cases term <;> rfl

theorem graphParams_expandFirstEntry (names : Names) (entry : BlockId)
    (blocks : List (BlockId × BasicBlock)) :
    graphParams (expandFirstEntry names entry blocks) = graphParams blocks := by
  induction blocks with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    unfold expandFirstEntry
    split <;> simp only [graphParams, trustIrCoroListLemma List.cons_bind List.flatMap_cons, expandedEntry_params] <;>
      first | rfl | exact congrArg (block.params ++ ·) ih

theorem cfgOf_expandFirstEntry (names : Names) (entry : BlockId)
    (blocks : List (BlockId × BasicBlock)) :
    cfgOf (expandFirstEntry names entry blocks) entry =
      (cfgOf blocks entry).map (expandedEntry names) := by
  induction blocks with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨id, block⟩
    cases hMatch : id == entry <;>
      simp only [expandFirstEntry, hMatch, Bool.false_eq_true, if_false, if_true,
        cfgOf, List.find?, Option.map] at * <;> exact ih

inductive FunctionExpansion (blocks : List (BlockId × BasicBlock)) where
  | expanded (source target : EvalFunction) (names : GraphNames blocks)
  | capacity (source : EvalFunction)
      (certificate : GenericCoroFreshIds.Capacity GenericCoroFreshIds.u32Domain (graphReservations blocks))

/-- Metadata is inferred from each actual graph, using real bounded source
    names. Source errors precede allocation/target inference. Capacity is an
    explicit transformation outcome, never a source-execution outcome. -/
def functionsOfExpansion (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) :
    Except SemError (FunctionExpansion blocks) := do
  let (source, _inferred) ← functionOfGraphWithEvidence direct indirect header blocks
  match GenericCoroFreshIds.u32Names (graphReservations blocks) with
  | .capacity certificate => pure (.capacity source certificate)
  | .ready names =>
    let target ← functionOfGraph direct indirect header
      (expandedGraph (Names.ofTriple names) blocks header.entryBlock)
    pure (.expanded source target names)

/-- The target declarations are the actual ordered instruction/result rows,
    classified by the same authoritative bridge rule. -/
theorem expandedEntry_result_classifications (names : Names) (params : List (ValueId × Ty))
    (frame value : ValueId) (slot : Nat) (next : Int)
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable) :
    let expanded := expandedEntry names
      { params := params, body := [], terminator := .CoroSuspend frame slot next value }
    (bodyInstsWithResultDests expanded.body expanded.bodyResultDests).map
      (fun row => localResultTypes direct indirect row.fst) =
      [.ok [.declared .I64], .ok [.declared .Ptr], .ok [.declared .I64], .ok []] := rfl

/-- All fields except private SSA storage. This keeps memory, permissions,
    globals, exceptions and both float-choice fields EXACT. -/
def callerWorld (state : MachineState) : MachineState :=
  { state with locals := ValueMap.empty, nextValueId := 0 }

inductive EffectRelation :
    Except SemError (List Value × MachineState) →
    Except SemError (List Value × MachineState) → Prop where
  | error (error : SemError) : EffectRelation (.error error) (.error error)
  | returned (values : List Value) (source target : MachineState)
      (world : callerWorld source = callerWorld target) :
      EffectRelation (.ok (values, source)) (.ok (values, target))

/-- The complete intrinsic body, including the post-store yield lookup. -/
def suspendValues (model : ByteModel) (frame value : ValueId)
    (slot : Nat) (next : Int) : Sem (List Value) := do
  let pointer ← Sem.lookupValue frame
  let address ← semGEPValuesUsing (scalarMemoryLayout model)
    (fun (_ : Unit) input => typedIntegerValue model .I64 input)
    .I64 pointer [((), Value.intAt 64 slot)] model
  semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model .I64)
    .I64 address (Value.intAt 64 next) false none model
  let yielded ← Sem.lookupValue value
  pure [yielded]

/-- The actual contextual evaluator at an empty-body suspend entry has this
    full computation for every parameter list, incoming values, strategy and
    call depth. No successful parameter binding or valid frame is assumed. -/
theorem sourceEntry_eq (ctx : EvalContext) (fuel depth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) (strategy : PanicStrategy)
    (entry : cfg pc = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :
    stepNWithContext ctx (fuel + 1) depth cfg pc args strategy = (do
      bindBlockParamsChecked params args
      suspendValues ctx.byteModel frame value slot next) := by
  cases strategy <;>
    simp only [stepNWithContext, entry, EvalContext.resolveBlock, EvalContext.resolveDrop,
      List.map_nil, bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
      stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInst,
      semCoroSuspend, semReturn, suspendValues, List.mapM, List.mapM.loop,
      List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
      pure_bind, bind_pure, bind_assoc]

theorem restoreFrame_callerWorld (state : MachineState) (frame : StackFrame)
    (values : List Value) : restoreFrame (callerWorld state) frame values = restoreFrame state frame values := by
  rfl

/-- The real frame restoration turns the local relation into full equality;
    no choice cursor, memory field or error is erased at the public boundary. -/
theorem restoreFrame_eq_of_callerWorld (source target : MachineState)
    (frame : StackFrame) (values : List Value)
    (h : callerWorld source = callerWorld target) :
    restoreFrame source frame values = restoreFrame target frame values := by
  rw [← restoreFrame_callerWorld source frame values,
    ← restoreFrame_callerWorld target frame values, h]

/-- The exact continuation used by the real Call branch after evaluating its
    callee. Return arity and poison failures occur before restoring the frame. -/
def finishCall (returnTys : List Ty) (frame : StackFrame)
    (callee : Sem (List Value)) : Sem (List Value) := do
  let values ← callee
  match checkReturnArity values returnTys with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError ("Call: " ++ message)
  Sem.rejectPoisonValues values "Call returns"
  let state ← Sem.getState
  Sem.setState (restoreFrame state frame [])
  pure values

/-- Any complete callee relation with equal return values and equal non-SSA
    effects lifts through the real return checks to full caller-state equality.
    Error, unwind, resource exhaustion and poison outcomes are all retained. -/
theorem finishCall_eq_of_effectRelation (returnTys : List Ty) (frame : StackFrame)
    (source target : Sem (List Value)) (sourceState targetState : MachineState)
    (related : EffectRelation (Sem.run source sourceState) (Sem.run target targetState)) :
    Sem.run (finishCall returnTys frame source) sourceState =
      Sem.run (finishCall returnTys frame target) targetState := by
  unfold finishCall
  simp only [Sem.run_bind]
  generalize hSource : Sem.run source sourceState = sourceResult at related ⊢
  generalize hTarget : Sem.run target targetState = targetResult at related ⊢
  cases related with
  | error error => rfl
  | returned values source target world =>
    simp only [Except.bind]
    cases hArity : checkReturnArity values returnTys with
    | error message => simp only [hArity]; rfl
    | ok unit =>
      cases unit
      simp only [hArity, pure_bind]
      cases hPoison : values.any Value.isPoison with
      | true => simp only [Sem.rejectPoisonValues, hPoison, if_true]; rfl
      | false =>
        simp only [Sem.rejectPoisonValues, hPoison, Bool.false_eq_true, if_false, pure_bind]
        exact congrArg (fun state => Except.ok (values, state))
          (restoreFrame_eq_of_callerWorld source target frame [] world)

/-- The actual frame discipline of direct calls. The caller state supplies
    its frame, while the callee starts with empty SSA storage. -/
def callFrame (returnTys : List Ty) (callee : Sem (List Value)) : Sem (List Value) := do
  let caller ← Sem.getState
  Sem.setState (callerWorld caller)
  finishCall returnTys (saveFrame caller none) callee

theorem callFrame_eq_of_effectRelation (returnTys : List Ty)
    (source target : Sem (List Value))
    (related : ∀ world, EffectRelation
      (Sem.run source (callerWorld world)) (Sem.run target (callerWorld world))) :
    callFrame returnTys source = callFrame returnTys target := by
  funext world
  exact finishCall_eq_of_effectRelation returnTys (saveFrame world none)
    source target (callerWorld world) (callerWorld world) (related world)

def directCallHeader (body : FuncBody) (args : List Value) : Sem Unit := do
  requireUntypedAbi body.abi
  match checkCallArity args body.paramTys with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError ("Call: " ++ message)
  Sem.rejectPoisonValues args "Call arguments"

/-- An anchored factorization of the real Call helper. This introduces no new
    evaluator and retains both fuel and call-depth arguments exactly. -/
theorem runCallReq_found (ctx : EvalContext) (fuel depth : Nat) (id : FuncId)
    (args : List Value) (strategy : PanicStrategy) (callee : EvalFunction)
    (found : ctx.functions id = some callee) :
    runCallReq ctx fuel depth id args strategy = (do
      directCallHeader callee.body args
      callFrame callee.body.returnTys
        (stepNWithContext (ctx.forFunction callee) fuel depth callee.cfg callee.entryBlock args strategy)) := by
  cases hArity : checkCallArity args callee.body.paramTys with
  | error message =>
    simp only [runCallReq, found, directCallHeader, callFrame, finishCall, callerWorld,
      hArity, pure_bind, bind_assoc]
    rfl
  | ok unit =>
    cases unit
    simp only [runCallReq, found, directCallHeader, callFrame, finishCall, callerWorld,
      hArity, pure_bind, bind_assoc]
    rfl

/-- The graph proof's complete callee relation is sufficient for the real Call
    boundary. Header errors and resource failures are preserved, and the final
    caller world is compared in full. This is an intermediate composition
    lemma; the source/target graph relation is established separately. -/
theorem runCallReq_eq_of_effectRelation (sourceCtx targetCtx : EvalContext)
    (fuel depth : Nat) (id : FuncId) (args : List Value) (strategy : PanicStrategy)
    (source target : EvalFunction)
    (sourceFound : sourceCtx.functions id = some source)
    (targetFound : targetCtx.functions id = some target)
    (sameHeader : source.body = target.body)
    (related : ∀ world, EffectRelation
      (Sem.run (stepNWithContext (sourceCtx.forFunction source) fuel depth
        source.cfg source.entryBlock args strategy) (callerWorld world))
      (Sem.run (stepNWithContext (targetCtx.forFunction target) fuel depth
        target.cfg target.entryBlock args strategy) (callerWorld world))) :
    runCallReq sourceCtx fuel depth id args strategy =
      runCallReq targetCtx fuel depth id args strategy := by
  rw [runCallReq_found sourceCtx fuel depth id args strategy source sourceFound,
    runCallReq_found targetCtx fuel depth id args strategy target targetFound,
    ← sameHeader]
  exact congrArg (fun tail => directCallHeader source.body args >>= fun _ => tail)
    (callFrame_eq_of_effectRelation source.body.returnTys _ _ related)

open LocalTypeInference

theorem declared_map_avoids (fresh : Nat) (types : List Ty) (entry : LocalTypeSource)
    (member : entry ∈ types.map LocalTypeSource.declared) : SourceAvoids fresh entry := by
  induction types with
  | nil => cases member
  | cons ty rest ih =>
    rcases List.mem_cons.mp member with same | old
    · subst entry; trivial
    · exact ih old

theorem classified_sources_avoid (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (fresh : Nat) (inst : Inst)
    (original : ∀ id ∈ operandIds inst, id.index ≠ fresh)
    (types : List LocalTypeSource) (classified : localResultTypes direct indirect inst = .ok types)
    (entry : LocalTypeSource) (member : entry ∈ types) : SourceAvoids fresh entry := by
  cases entry with
  | declared ty => trivial
  | borrow operand =>
    cases inst <;> simp only [operandIds, localResultTypes] at original classified
    all_goals
      first
      | solve
          | have actual := Except.ok.inj classified
            subst types
            simp_all [List.mem_cons, SourceAvoids]
      | solve
          | have actual := Except.ok.inj classified
            subst types
            exact declared_map_avoids fresh _ (.borrow operand) member
      | solve
          | split at classified <;> cases classified
            all_goals exact declared_map_avoids fresh _ (.borrow operand) member

theorem graph_params_original (blocks : List (BlockId × BasicBlock)) (fresh : Nat)
    (unused : ValueId.mk fresh ∉ graphValueIds blocks) :
    ∀ row ∈ graphParams blocks, row.fst.index ≠ fresh := by
  intro row member same
  have rowEq : row.fst = ⟨fresh⟩ := by
    have value := row.fst
    cases value
    exact congrArg ValueId.mk same
  have found := graphParam_mem blocks row member
  rw [rowEq] at found
  exact unused found

theorem graph_destinations_original (blocks : List (BlockId × BasicBlock)) (fresh : Nat)
    (unused : ValueId.mk fresh ∉ graphValueIds blocks) :
    ∀ row ∈ graphNodes blocks, ∀ id ∈ row.snd, id.index ≠ fresh := by
  intro row member id destination same
  have idEq : id = ⟨fresh⟩ := by cases id; cases same; rfl
  have found := graphNode_dest_mem blocks row member id destination
  rw [idEq] at found
  exact unused found

theorem graph_sources_original (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : List (BlockId × BasicBlock)) (fresh : Nat)
    (unused : ValueId.mk fresh ∉ graphValueIds blocks) :
    ∀ row ∈ graphNodes blocks, ∀ types,
      localResultTypes direct indirect row.fst = .ok types →
      ∀ entry ∈ types, SourceAvoids fresh entry := by
  intro row member types classified entry inTypes
  apply classified_sources_avoid direct indirect fresh row.fst _ types classified entry inTypes
  intro id operand same
  have idEq : id = ⟨fresh⟩ := by cases id; cases same; rfl
  have found := graphNode_operand_mem blocks row member id operand
  rw [idEq] at found
  exact unused found

theorem graph_input_avoids (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : List (BlockId × BasicBlock)) (fresh : Nat)
    (unused : ValueId.mk fresh ∉ graphValueIds blocks) :
    InputAvoids direct indirect fresh (graphParams blocks) (graphNodes blocks) :=
  ⟨graph_params_original blocks fresh unused, graph_destinations_original blocks fresh unused,
    graph_sources_original direct indirect blocks fresh unused⟩

/-- Every fresh source-use gap is also absent from the ACTUALLY inferred
    table. This connects the allocator's finite reservation list to inferred
    support without assuming any map law or caller metadata. -/
theorem graph_inference_unused (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : List (BlockId × BasicBlock)) (fresh : Nat)
    (unused : ValueId.mk fresh ∉ graphValueIds blocks) (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred) : inferred.table ⟨fresh⟩ = none :=
  infer_missing direct indirect (graphParams blocks) (graphNodes blocks) fresh
    (graph_params_original blocks fresh unused) (graph_destinations_original blocks fresh unused)
    (graph_sources_original direct indirect blocks fresh unused) inferred run

theorem reservation_unused (blocks : List (BlockId × BasicBlock)) (fresh : Nat)
    (unused : fresh ∉ graphReservations blocks) : ValueId.mk fresh ∉ graphValueIds blocks := by
  intro member
  exact unused (mem_map_of_mem ValueId.index (graphValueIds blocks) ⟨fresh⟩ member)

theorem GraphNames.unused (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks) :
    (Names.ofTriple names).index ∉ graphValueIds blocks ∧
    (Names.ofTriple names).pointer ∉ graphValueIds blocks ∧
    (Names.ofTriple names).state ∉ graphValueIds blocks :=
  ⟨reservation_unused blocks names.first names.firstUnused,
    reservation_unused blocks names.second names.secondUnused,
    reservation_unused blocks names.third names.thirdUnused⟩

/-- A source metadata failure is returned unchanged before names or target
    metadata are considered. This is part of the total preparation domain. -/
theorem functionsOfExpansion_source_error (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : List (BlockId × BasicBlock))
    (error : SemError) (failed : functionOfGraphWithEvidence direct indirect header blocks = .error error) :
    functionsOfExpansion direct indirect header blocks = .error error := by
  simp only [functionsOfExpansion, failed, Bind.bind, Except.bind]

theorem functionsOfExpansion_capacity (direct : FuncId → Option FuncTyDef)
    (indirect : FuncTyTable) (header : EvalFunction) (blocks : List (BlockId × BasicBlock))
    (source : EvalFunction) (inferred : LocalTypeInference)
    (built : functionOfGraphWithEvidence direct indirect header blocks = .ok (source, inferred))
    (certificate : GenericCoroFreshIds.Capacity GenericCoroFreshIds.u32Domain (graphReservations blocks))
    (full : GenericCoroFreshIds.u32Names (graphReservations blocks) = .capacity certificate) :
    functionsOfExpansion direct indirect header blocks = .ok (.capacity source certificate) := by
  simp only [functionsOfExpansion, built, full, Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem cfgOf_decompose (blocks : List (BlockId × BasicBlock)) (entry : BlockId)
    (block : BasicBlock) (found : cfgOf blocks entry = some block) :
    ∃ before id after,
      blocks = before ++ (id, block) :: after ∧ (id == entry) = true ∧
      (∀ row ∈ before, (row.fst == entry) = false) := by
  induction blocks with
  | nil => cases found
  | cons row rest ih =>
    rcases row with ⟨id, current⟩
    cases matched : id == entry with
    | true =>
      simp only [cfgOf, List.find?, matched, if_true, Option.map] at found
      cases found
      exact ⟨[], id, rest, rfl, matched, by intro row member; cases member⟩
    | false =>
      simp only [cfgOf, List.find?, matched, Bool.false_eq_true, if_false] at found
      obtain ⟨before, selected, after, decomposition, selectedMatch, noMatch⟩ := ih found
      refine ⟨(id, current) :: before, selected, after, ?_, selectedMatch, ?_⟩
      · rw [decomposition]; rfl
      · intro row member
        rcases List.mem_cons.mp member with same | old
        · subst row; exact matched
        · exact noMatch row old

theorem expandFirstEntry_at (names : Names) (entry id : BlockId) (block : BasicBlock)
    (before after : List (BlockId × BasicBlock))
    (selected : (id == entry) = true)
    (noMatch : ∀ row ∈ before, (row.fst == entry) = false) :
    expandFirstEntry names entry (before ++ (id, block) :: after) =
      before ++ (id, expandedEntry names block) :: after := by
  induction before with
  | nil => simp only [List.nil_append, expandFirstEntry, selected, if_true]
  | cons row rest ih =>
    have head := noMatch row ((trustIrListMemConsSelf _ _))
    have tail := fun item member => noMatch item (List.mem_cons_of_mem row member)
    simp only [List.cons_append, expandFirstEntry, head, Bool.false_eq_true, if_false]
    exact congrArg (List.cons row) (ih tail)

theorem graphNodes_append (before after : List (BlockId × BasicBlock)) :
    graphNodes (before ++ after) = graphNodes before ++ graphNodes after := by
  simp only [graphNodes, trustIrCoroListLemma List.append_bind List.flatMap_append]

theorem graphNodes_cons (id : BlockId) (block : BasicBlock) (rest : List (BlockId × BasicBlock)) :
    graphNodes ((id, block) :: rest) =
      (bodyInstsWithResultDests block.body block.bodyResultDests ++
        [(block.terminator, block.terminatorResultDests)]) ++ graphNodes rest := by
  simp only [graphNodes, trustIrCoroListLemma List.cons_bind List.flatMap_cons]

theorem graphNodes_sourceEntry (before after : List (BlockId × BasicBlock)) (id : BlockId)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) :
    graphNodes (before ++ (id, {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :: after) =
      graphNodes before ++ (.CoroSuspend frame slot next value, termDests) :: graphNodes after := by
  rw [graphNodes_append, graphNodes_cons]
  rfl

theorem graphNodes_expandedEntry (names : Names) (before after : List (BlockId × BasicBlock)) (id : BlockId)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) :
    graphNodes (before ++ (id, expandedEntry names {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :: after) =
      (graphNodes before ++ [(.Const .I64 (.int slot), [names.index]),
        (.GEP .I64 frame [names.index] false, [names.pointer]),
        (.Const .I64 (.int next), [names.state]),
        (.Store .I64 names.pointer names.state false none, []), (.Return [value], [])]) ++
        graphNodes after := by
  rw [graphNodes_append, graphNodes_cons]
  simp only [expandedEntry, bodyInstsWithResultDests, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The actual expanded finite graph infers its three fresh result types and
    preserves every original use/definition association. Successful source
    inference is an intermediate branch fact; the total preparation theorem
    separately retains source inference errors and finite-domain capacity. -/
theorem expandedGraph_inference (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (blocks : List (BlockId × BasicBlock)) (entry : BlockId)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) (names : GraphNames blocks)
    (inferred : LocalTypeInference)
    (found : cfgOf blocks entry = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })
    (run : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred) :
    ∃ targetInferred,
      inferLocalTypesWithEvidence direct indirect
        (graphParams (expandedGraph (Names.ofTriple names) blocks entry))
        (graphNodes (expandedGraph (Names.ofTriple names) blocks entry)) = .ok targetInferred ∧
      targetInferred.table (Names.ofTriple names).index = some .I64 ∧
      targetInferred.table (Names.ofTriple names).pointer = some .Ptr ∧
      targetInferred.table (Names.ofTriple names).state = some .I64 ∧
      (∀ id ∈ graphValueIds blocks, inferred.table id = targetInferred.table id) := by
  obtain ⟨before, selectedId, after, decomposition, selected, noMatch⟩ :=
    cfgOf_decompose blocks entry _ found
  have sourceNodes : graphNodes blocks =
      graphNodes before ++ (.CoroSuspend frame slot next value, termDests) :: graphNodes after := by
    rw [decomposition]
    exact graphNodes_sourceEntry before after selectedId params bodyDests termDests frame value slot next
  have termMember : (.CoroSuspend frame slot next value, termDests) ∈ graphNodes blocks := by
    rw [sourceNodes]
    exact trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _))
  have census := infer_success_census direct indirect (graphParams blocks) (graphNodes blocks)
    (.CoroSuspend frame slot next value, termDests) [] termMember rfl inferred run
  have termEmpty : termDests = [] := by
    cases termDests with
    | nil => rfl
    | cons head rest =>
      simp only [List.length_nil, List.length_cons] at census <;> omega
  subst termDests
  have free := GraphNames.unused blocks names
  have firstAvoid := graph_input_avoids direct indirect blocks names.first free.1
  have secondAvoid := graph_input_avoids direct indirect blocks names.second free.2.1
  have thirdAvoid := graph_input_avoids direct indirect blocks names.third free.2.2
  rw [sourceNodes] at firstAvoid secondAvoid thirdAvoid
  have sourceRun := run
  rw [sourceNodes] at sourceRun
  have baseRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks)
      (graphNodes before ++ graphNodes after) = .ok inferred :=
    (infer_insert_empty direct indirect (graphParams blocks) (graphNodes before) (graphNodes after)
      (.CoroSuspend frame slot next value) rfl).symm.trans sourceRun
  obtain ⟨targetInferred, targetRows, indexType, pointerType, stateType, preserved⟩ :=
    infer_insert_three direct indirect (graphParams blocks) (graphNodes before) (graphNodes after)
      names.first names.second names.third .I64 .Ptr .I64
      (.Const .I64 (.int slot)) (.GEP .I64 frame [⟨names.first⟩] false) (.Const .I64 (.int next))
      rfl rfl rfl names.firstSecond names.firstThird names.secondThird
      firstAvoid.removeNode secondAvoid.removeNode thirdAvoid.removeNode inferred baseRun
  let temps := Names.ofTriple names
  let beforeReturn := graphNodes before ++
    [(.Const .I64 (.int slot), [temps.index]),
      (.GEP .I64 frame [temps.index] false, [temps.pointer]),
      (.Const .I64 (.int next), [temps.state])]
  have nonvoidRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks)
      (beforeReturn ++ graphNodes after) = .ok targetInferred := by
    simpa only [beforeReturn, temps, Names.ofTriple, List.append_assoc,
      List.cons_append, List.nil_append] using targetRows
  have removeStore := infer_insert_empty direct indirect (graphParams blocks) beforeReturn
    ((.Return [value], []) :: graphNodes after) (.Store .I64 temps.pointer temps.state false none) rfl
  have removeReturn := infer_insert_empty direct indirect (graphParams blocks) beforeReturn
    (graphNodes after) (.Return [value]) rfl
  refine ⟨targetInferred, ?_, indexType, pointerType, stateType, ?_⟩
  · have targetGraph : expandedGraph temps blocks entry = before ++
        (selectedId, expandedEntry temps {
          params := params
          body := []
          bodyResultDests := bodyDests
          terminator := .CoroSuspend frame slot next value
          terminatorResultDests := [] }) :: after := by
      unfold expandedGraph
      rw [decomposition]
      exact expandFirstEntry_at temps entry selectedId _ before after selected noMatch
    have targetParams : graphParams (expandedGraph temps blocks entry) = graphParams blocks :=
      graphParams_expandFirstEntry temps entry blocks
    change inferLocalTypesWithEvidence direct indirect
      (graphParams (expandedGraph temps blocks entry)) (graphNodes (expandedGraph temps blocks entry)) = _
    rw [targetParams, targetGraph, graphNodes_expandedEntry]
    simpa only [beforeReturn, List.append_assoc, List.cons_append, List.nil_append] using
      (removeStore.trans removeReturn).trans nonvoidRun
  · intro id member
    have original_ne (fresh : Nat) (unused : ValueId.mk fresh ∉ graphValueIds blocks) : id.index ≠ fresh := by
      intro same
      have idEq : id = ⟨fresh⟩ := by cases id; cases same; rfl
      apply unused
      rw [← idEq]
      exact member
    exact preserved id (original_ne names.first free.1) (original_ne names.second free.2.1)
      (original_ne names.third free.2.2)

theorem functionOfGraph_of_inference (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) (inferred : LocalTypeInference)
    (run : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) =
      .ok inferred) :
    functionOfGraph direct indirect header blocks =
      .ok {header with cfg := cfgOf blocks, localTypes := some inferred.table} := by
  unfold functionOfGraph inferLocalTypes inferLocalTypesWithWork
  rw [run]
  rfl

/-- Total metadata preparation: every actual source refusal is propagated
    first; otherwise there is a genuine u32-capacity result or an ACTUALLY
    decoded/inferred target with all required associations. Source inference
    success and target lookup facts are conclusions of their matching branch,
    not extra completion premises. Execution equivalence is a separate
    obligation composed at the real call boundary. -/
theorem functionsOfExpansion_metadata (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock))
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :
    match inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
    | .error error => functionsOfExpansion direct indirect header blocks = .error error
    | .ok inferred =>
      let source := {header with cfg := cfgOf blocks, localTypes := some inferred.table}
      match GenericCoroFreshIds.u32Names (graphReservations blocks) with
      | .capacity certificate =>
        functionsOfExpansion direct indirect header blocks = .ok (.capacity source certificate)
      | .ready names =>
        ∃ targetInferred : LocalTypeInference,
          functionsOfExpansion direct indirect header blocks = .ok (.expanded source
            {header with
              cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock)
              localTypes := some targetInferred.table} names) ∧
          targetInferred.table (Names.ofTriple names).index = some .I64 ∧
          targetInferred.table (Names.ofTriple names).pointer = some .Ptr ∧
          targetInferred.table (Names.ofTriple names).state = some .I64 ∧
          (∀ id ∈ graphValueIds blocks, inferred.table id = targetInferred.table id) := by
  cases sourceRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
  | error error =>
    simp only [sourceRun, functionsOfExpansion, functionOfGraphWithEvidence, Bind.bind, Except.bind]
  | ok inferred =>
    simp only [sourceRun]
    cases allocation : GenericCoroFreshIds.u32Names (graphReservations blocks) with
    | capacity certificate =>
      simp only [allocation, functionsOfExpansion, functionOfGraphWithEvidence, sourceRun,
        Bind.bind, Pure.pure, Except.bind, Except.pure]
    | ready names =>
      simp only [allocation]
      obtain ⟨targetInferred, targetRun, indexType, pointerType, stateType, preserved⟩ :=
        expandedGraph_inference direct indirect blocks header.entryBlock params bodyDests termDests
          frame value slot next names inferred found sourceRun
      have built := functionOfGraph_of_inference direct indirect header
        (expandedGraph (Names.ofTriple names) blocks header.entryBlock) targetInferred targetRun
      refine ⟨targetInferred, ?_, indexType, pointerType, stateType, preserved⟩
      simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, allocation,
        built, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Restoring selected SSA fields after clearing a frame retains all other
    fields literally, including the float choice tape and cursor. -/
theorem replaceSSA_of_callerWorld (source target : MachineState)
    (world : callerWorld source = callerWorld target) :
    target = HeldMemoryFrames.replaceSSA source target.locals target.nextValueId := by
  have equality := congrArg
    (fun state => HeldMemoryFrames.replaceSSA state target.locals target.nextValueId) world
  exact equality.symm

/-- Equivariance of a held-value core implies it preserves both SSA fields on
    every successful run. The result/error law itself remains unconditional. -/
theorem equivariant_preservesSSA {α : Type} (computation : Sem α)
    (equivariant : HeldMemoryFrames.Equivariant computation)
    (state after : MachineState) (result : α)
    (ran : Sem.run computation state = .ok (result, after)) :
    after.locals = state.locals ∧ after.nextValueId = state.nextValueId := by
  have equation := equivariant state state.locals state.nextValueId
  have same : HeldMemoryFrames.replaceSSA state state.locals state.nextValueId = state := rfl
  rw [same, ran] at equation
  have states := congrArg Prod.snd (Except.ok.inj equation)
  have locals := congrArg MachineState.locals states
  have counter := congrArg MachineState.nextValueId states
  exact ⟨locals, counter⟩

/-- Complete held-core transport across two SSA frames: errors are identical,
    and a successful target run has precisely its own original SSA storage. -/
theorem equivariant_transport {α : Type} (computation : Sem α)
    (equivariant : HeldMemoryFrames.Equivariant computation)
    (source target : MachineState) (world : callerWorld source = callerWorld target) :
    Sem.run computation target = (Sem.run computation source).map
      (fun result => (result.1,
        HeldMemoryFrames.replaceSSA result.2 target.locals target.nextValueId)) := by
  rw [replaceSSA_of_callerWorld source target world]
  exact equivariant source target.locals target.nextValueId

/-- The generated I64 index is interpreted through its actual declaration.
    This holds for every integer payload, including overflow/sign residues;
    the consumer's checked GEP plan retains all of its errors. -/
theorem carrierIntegerOperand_i64 (ctx : EvalContext) (table : LocalTypeTable)
    (index : ValueId) (raw : Int) (width : Nat)
    (types : ctx.localTypes = some table) (recorded : table index = some .I64) :
    ctx.carrierIntegerOperand index (.int width raw) =
      typedIntegerValue ctx.byteModel .I64 (.int width raw) := by
  simp only [EvalContext.carrierIntegerOperand, Value.isPoison, Value.isUninit,
    Bool.false_or, Bool.false_eq_true, if_false, types, recorded,
    Bind.bind, Pure.pure, Except.bind, Except.pure, typedIntegerCarrierValue]

/-- Singleton GEP plans depend on an index's declared interpretation, never
    on whether its key is an instruction immediate or an SSA identifier. -/
theorem gepOffset_singleton_keys {leftKey rightKey : Type}
    (layout : MemoryLayoutQuery) (leftReader : leftKey → Value → Except SemError Int)
    (rightReader : rightKey → Value → Except SemError Int) (ty : Ty)
    (left : leftKey) (right : rightKey) (value : Value)
    (readers : leftReader left value = rightReader right value) :
    gepOffsetUsing layout leftReader ty [(left, value)] =
      gepOffsetUsing layout rightReader ty [(right, value)] := by
  simp only [gepOffsetUsing, List.forIn_nil, List.forIn_cons]
  rw [readers]

theorem heldGEP_i64_index (ctx : EvalContext) (table : LocalTypeTable)
    (index : ValueId) (slot : Nat) (base : Value)
    (types : ctx.localTypes = some table) (recorded : table index = some .I64) :
    semGEPValuesUsing (scalarMemoryLayout ctx.byteModel) ctx.carrierIntegerOperand .I64 base
      [(index, Value.intAt 64 slot)] ctx.byteModel =
    semGEPValuesUsing (scalarMemoryLayout ctx.byteModel)
      (fun (_ : Unit) value => typedIntegerValue ctx.byteModel .I64 value) .I64 base
      [((), Value.intAt 64 slot)] ctx.byteModel := by
  unfold semGEPValuesUsing
  rw [gepOffset_singleton_keys (scalarMemoryLayout ctx.byteModel) ctx.carrierIntegerOperand
    (fun (_ : Unit) value => typedIntegerValue ctx.byteModel .I64 value) .I64 index () (Value.intAt 64 slot)
    (carrierIntegerOperand_i64 ctx table index _ 64 types recorded)]

/-- Contextual function-pointer encoding has no effect on an I64 store. This
    function equality also rewrites a partially applied encoder under binds. -/
theorem encodeMemoryWithFunctions_i64 (model : ByteModel) (order : FunctionAddressOrder) :
    encodeMemoryWithFunctions model order .I64 = encodeMemoryAt model .I64 := rfl

/-- The result checks for a void store neither publish aliases nor inspect
    unrelated metadata; they still use the authoritative classifier. -/
theorem bindInstructionResults_store (ctx : EvalContext) (pointer value : ValueId) :
    ctx.bindInstructionResults (.Store .I64 pointer value false none) (.value none) [] = pure () := by
  simp only [EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
    EvalContext.instructionResultTypes, ssaInstructionResultTypes, localResultTypes]
  cases ctx.localTypes <;> rfl

theorem instructionResultTypes_declared (ctx : EvalContext) (table : LocalTypeTable)
    (inst : Inst) (dest : ValueId) (ty : Ty)
    (types : ctx.localTypes = some table) (recorded : table dest = some ty)
    (classified : localResultTypes ctx.resultTypeHeaders ctx.funcTys inst = .ok [.declared ty]) :
    ctx.instructionResultTypes inst [dest] 1 = .ok [ty] := by
  simp only [EvalContext.instructionResultTypes, ssaInstructionResultTypes, types,
    List.length_cons, List.length_nil, recorded, classified, List.mapM, List.mapM.loop,
    ssaResultSourceType, List.zip_cons_cons, List.zip_nil_left, List.any_cons, List.any_nil,
    closureTyEq_refl, Bind.bind, Pure.pure, Except.bind, Except.pure]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.zip_cons_cons,
    List.zip_nil_left, List.any_cons, List.any_nil, closureTyEq_refl]
  rfl

/-- An explicit single-result node publishes the value at its source id and
    retires its private evaluator result. The index need not exceed any source
    id; the gap allocator may choose a low unused id. -/
def publishFresh (dest : ValueId) (value : Value) : Sem Unit := do
  let result ← Sem.bindFresh value
  bindInstrResultDests (.value (some result)) [dest]

def expandedValues (ctx : EvalContext) (names : Names) (frame value : ValueId)
    (slot : Nat) (next : Int) : Sem (List Value) := do
  publishFresh names.index (Value.intAt 64 slot)
  let address ← semGEPUsing (scalarMemoryLayout ctx.byteModel) ctx.carrierIntegerOperand
    .I64 frame [names.index] ctx.byteModel
  bindInstrResultDests (.value (some address)) [names.pointer]
  publishFresh names.state (Value.intAt 64 next)
  let pointer ← Sem.lookupValue names.pointer
  let stored ← Sem.lookupValue names.state
  semStoreValueUsing (scalarMemoryLayout ctx.byteModel) (encodeMemoryAt ctx.byteModel .I64)
    .I64 pointer stored false none ctx.byteModel
  let yielded ← Sem.lookupValue value
  pure [yielded]

/-- Exact evaluator normalization for the expanded entry. The three source
    associations are derived by expandedGraph_inference; this lemma makes no
    assumption that parameters, GEP, Store, or the returned value succeed. -/
theorem targetEntry_eq (ctx : EvalContext) (fuel depth : Nat) (cfg : CFG) (pc : BlockId)
    (names : Names) (params : List (ValueId × Ty)) (args : List Value)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) (strategy : PanicStrategy)
    (table : LocalTypeTable) (types : ctx.localTypes = some table)
    (indexType : table names.index = some .I64) (pointerType : table names.pointer = some .Ptr)
    (stateType : table names.state = some .I64)
    (entry : cfg pc = some (expandedEntry names {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })) :
    stepNWithContext ctx (fuel + 1) depth cfg pc args strategy = (do
      bindBlockParamsChecked params args
      expandedValues ctx names frame value slot next) := by
  trustIrCompilerProof {
    have slotBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int slot)) names.index result .I64
        (instructionResultTypes_declared ctx table _ _ _ types indexType rfl) (by intro h; cases h)
    have pointerBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.GEP .I64 frame [names.index] false) names.pointer result .Ptr
        (instructionResultTypes_declared ctx table _ _ _ types pointerType rfl) (by intro h; cases h)
    have stateBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int next)) names.state result .I64
        (instructionResultTypes_declared ctx table _ _ _ types stateType rfl) (by intro h; cases h)
    cases strategy <;>
      simp only [stepNWithContext, entry, expandedEntry, EvalContext.resolveBlock,
        EvalContext.resolveDrop, List.map_nil, List.map_cons, bodyInstsWithResultDests,
        forIn, List.forIn, List.forIn.loop, stepTermWithContext, closureTermWithContext,
        stepTermUnwind, stepInstWithContext, stepInst, semStoreUsing,
        EvalContext.semGEPUsing_canonical, EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout,
        encodeMemoryWithFunctions_i64, slotBind, pointerBind, stateBind,
        bindInstructionResults_store, Constant.hasSymbolAddr, constValueAtChecked_i64,
        constWidthAmbiguous, constHasInexactFloat, constPointerFormsSupported, Ty.isInteger,
        Bool.not_true, Bool.false_eq_true, if_false,
        semReturn, expandedValues, publishFresh, List.mapM, List.mapM.loop,
        List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
        pure_bind, bind_pure, bind_assoc]
  } {
    have slotBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int slot)) names.index result .I64
        (instructionResultTypes_declared ctx table _ _ _ types indexType rfl) (by intro h; cases h)
    have pointerBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.GEP .I64 frame [names.index] false) names.pointer result .Ptr
        (instructionResultTypes_declared ctx table _ _ _ types pointerType rfl) (by intro h; cases h)
    have stateBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int next)) names.state result .I64
        (instructionResultTypes_declared ctx table _ _ _ types stateType rfl) (by intro h; cases h)
    cases strategy <;>
      simp only [stepNWithContext, entry, expandedEntry, EvalContext.resolveBlock,
        EvalContext.resolveDrop, List.map_nil, List.map_cons, bodyInstsWithResultDests,
        List.forIn_nil, List.forIn_cons, stepTermWithContext, closureTermWithContext,
        stepTermUnwind, stepInstWithContext, stepInst, semStoreUsing,
        EvalContext.semGEPUsing_canonical, EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout,
        encodeMemoryWithFunctions_i64, slotBind, pointerBind, stateBind,
        bindInstructionResults_store, Constant.hasSymbolAddr, constValueAtChecked_i64,
        constWidthAmbiguous, constHasInexactFloat, constPointerFormsSupported, Ty.isInteger,
        Bool.not_true, Bool.false_eq_true, if_false, if_true,
        semReturn, expandedValues, publishFresh, List.mapM, List.mapM.loop,
        List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
        pure_bind, bind_pure, bind_assoc]
  }

def publishState (state : MachineState) (dest : ValueId) (value : Value) : MachineState :=
  { state with
    locals := state.locals.set dest value
    nextValueId := max (state.nextValueId + 1) (dest.index + 1) }

theorem publishFresh_run (state : MachineState) (dest : ValueId) (value : Value)
    (fresh : SSAFreshFrames.FreshState state) :
    Sem.run (publishFresh dest value) state = .ok ((), publishState state dest value) :=
  SSAFreshFrames.bindFresh_publish_run state value dest fresh

theorem publishState_fresh (state : MachineState) (dest : ValueId) (value : Value)
    (fresh : SSAFreshFrames.FreshState state) :
    SSAFreshFrames.FreshState (publishState state dest value) :=
  SSAFreshFrames.publish_fresh state dest value fresh

theorem publishState_world (state : MachineState) (dest : ValueId) (value : Value) :
    callerWorld (publishState state dest value) = callerWorld state := rfl

theorem publishState_lookup_same (state : MachineState) (dest : ValueId) (value : Value) :
    (publishState state dest value).lookupValue dest = some value := by
  simp only [publishState, MachineState.lookupValue, ValueMap.get, ValueMap.set, beq_self_eq_true, if_true]

theorem publishState_lookup_other (state : MachineState) (dest id : ValueId) (value : Value)
    (different : id ≠ dest) :
    (publishState state dest value).lookupValue id = state.lookupValue id := by
  trustIrCompilerProof {
    simp only [publishState, MachineState.lookupValue, ValueMap.get, ValueMap.set,
      (beq_eq_false_iff_ne id dest).mpr different, if_false]
  } {
    simp only [publishState, MachineState.lookupValue, ValueMap.get, ValueMap.set,
      beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, if_false]
  }

theorem replaceSSA_fresh (after source : MachineState) (fresh : SSAFreshFrames.FreshState source) :
    SSAFreshFrames.FreshState
      (HeldMemoryFrames.replaceSSA after source.locals source.nextValueId) := fresh

theorem replaceSSA_world (after source : MachineState) :
    callerWorld (HeldMemoryFrames.replaceSSA after source.locals source.nextValueId) = callerWorld after := rfl

theorem replaceSSA_lookup (after source : MachineState) (id : ValueId) :
    (HeldMemoryFrames.replaceSSA after source.locals source.nextValueId).lookupValue id =
      source.lookupValue id := rfl

theorem lookupValue_run (state : MachineState) (id : ValueId) :
    Sem.run (Sem.lookupValue id) state = match state.lookupValue id with
      | none => .error (.typeError s!"undefined SSA value: {repr id}")
      | some value => .ok (value, state) := by
  trustIrCompilerProof {
  cases lookup : state.lookupValue id <;>
    simp only [Sem.run, Sem.lookupValue, sr_bind, sr_get, Except.bind, lookup,
      sr_pure, sr_throwTE]
  } {
  cases lookup : state.lookupValue id <;>
    simp only [Sem.run, Sem.lookupValue, sr_bind, sr_get, Except.bind, lookup,
      sr_pure, sr_throwTE] <;> rfl
  }

theorem expandedValues_held (ctx : EvalContext) (names : Names) (frame value : ValueId)
    (slot : Nat) (next : Int) :
    expandedValues ctx names frame value slot next = (do
      publishFresh names.index (Value.intAt 64 slot)
      let base ← Sem.lookupValue frame
      let index ← Sem.lookupValue names.index
      let pointer ← semGEPValuesUsing (scalarMemoryLayout ctx.byteModel) ctx.carrierIntegerOperand
        .I64 base [(names.index, index)] ctx.byteModel
      publishFresh names.pointer pointer
      publishFresh names.state (Value.intAt 64 next)
      let pointer ← Sem.lookupValue names.pointer
      let stored ← Sem.lookupValue names.state
      semStoreValueUsing (scalarMemoryLayout ctx.byteModel) (encodeMemoryAt ctx.byteModel .I64)
        .I64 pointer stored false none ctx.byteModel
      let yielded ← Sem.lookupValue value
      pure [yielded]) := by
  simp only [expandedValues, semGEPUsing, publishFresh, List.mapM, List.mapM.loop,
    List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
    pure_bind, bind_assoc]

/-- Complete body simulation. Only the graph-derived generated-id exclusions
    are used: neither parameter/value validity nor a successful memory access
    is assumed. The final yield lookup remains after the store on both sides. -/
theorem expandedValues_effect (ctx : EvalContext) (table : LocalTypeTable)
    (names : Names) (frame value : ValueId) (slot : Nat) (next : Int)
    (types : ctx.localTypes = some table) (indexType : table names.index = some .I64)
    (pointerState : names.pointer ≠ names.state)
    (frameIndex : frame ≠ names.index)
    (valueIndex : value ≠ names.index) (valuePointer : value ≠ names.pointer)
    (valueState : value ≠ names.state)
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation (Sem.run (suspendValues ctx.byteModel frame value slot next) state)
      (Sem.run (expandedValues ctx names frame value slot next) state) := by
  let indexed := publishState state names.index (Value.intAt 64 slot)
  have indexedFresh : SSAFreshFrames.FreshState indexed := publishState_fresh _ _ _ fresh
  have frameSame : indexed.lookupValue frame = state.lookupValue frame :=
    publishState_lookup_other _ _ _ _ frameIndex
  have indexHere : indexed.lookupValue names.index = some (Value.intAt 64 slot) :=
    publishState_lookup_same _ _ _
  rw [expandedValues_held]
  unfold suspendValues
  simp only [Sem.run_bind]
  rw [publishFresh_run state names.index (Value.intAt 64 slot) fresh]
  simp only [Except.bind]
  rw [lookupValue_run state frame, lookupValue_run indexed frame, frameSame]
  cases frameRead : state.lookupValue frame with
  | none =>
    simp only [frameRead, Except.bind]
    exact .error _
  | some base =>
    simp only [frameRead, Except.bind]
    rw [lookupValue_run indexed names.index, indexHere]
    simp only [Except.bind]
    rw [heldGEP_i64_index ctx table names.index slot base types indexType]
    let gep := semGEPValuesUsing (scalarMemoryLayout ctx.byteModel)
      (fun (_ : Unit) input => typedIntegerValue ctx.byteModel .I64 input)
      .I64 base [((), Value.intAt 64 slot)] ctx.byteModel
    have gepEquivariant : HeldMemoryFrames.Equivariant gep :=
      HeldMemoryFrames.semGEPValuesUsing_eqv _ _ _ _ _ _
    have gepTransport := equivariant_transport gep gepEquivariant state indexed
      (publishState_world state names.index (Value.intAt 64 slot)).symm
    rw [gepTransport]
    cases gepRun : Sem.run gep state with
    | error error =>
      simp only [gepRun, Except.map, Except.bind]
      exact .error error
    | ok result =>
      rcases result with ⟨pointer, afterGEP⟩
      simp only [gepRun, Except.map, Except.bind]
      let targetGEP := HeldMemoryFrames.replaceSSA afterGEP indexed.locals indexed.nextValueId
      have targetFresh : SSAFreshFrames.FreshState targetGEP := replaceSSA_fresh _ _ indexedFresh
      let pointed := publishState targetGEP names.pointer pointer
      have pointedFresh : SSAFreshFrames.FreshState pointed := publishState_fresh _ _ _ targetFresh
      rw [publishFresh_run targetGEP names.pointer pointer targetFresh]
      simp only [Except.bind]
      let stated := publishState pointed names.state (Value.intAt 64 next)
      rw [publishFresh_run pointed names.state (Value.intAt 64 next) pointedFresh]
      simp only [Except.bind]
      have pointerHere : stated.lookupValue names.pointer = some pointer := by
        rw [publishState_lookup_other pointed names.state names.pointer _ pointerState]
        exact publishState_lookup_same _ _ _
      have stateHere : stated.lookupValue names.state = some (Value.intAt 64 next) :=
        publishState_lookup_same _ _ _
      rw [lookupValue_run stated names.pointer, pointerHere]
      simp only [Except.bind]
      rw [lookupValue_run stated names.state, stateHere]
      simp only [Except.bind]
      let store := semStoreValueUsing (scalarMemoryLayout ctx.byteModel) (encodeMemoryAt ctx.byteModel .I64)
        .I64 pointer (Value.intAt 64 next) false none ctx.byteModel
      have storeEquivariant : HeldMemoryFrames.Equivariant store :=
        HeldMemoryFrames.semStoreValueUsing_eqv _ _ _ _ _ _ _ _
      have sameWorld : callerWorld afterGEP = callerWorld stated := by
        simp only [stated, pointed, targetGEP, publishState_world, replaceSSA_world]
      have storeTransport := equivariant_transport store storeEquivariant afterGEP stated sameWorld
      rw [storeTransport]
      cases storeRun : Sem.run store afterGEP with
      | error error =>
        simp only [storeRun, Except.map, Except.bind]
        exact .error error
      | ok result =>
        rcases result with ⟨unit, afterStore⟩
        cases unit
        simp only [storeRun, Except.map, Except.bind]
        have gepSSA := equivariant_preservesSSA gep gepEquivariant state afterGEP pointer gepRun
        have storeSSA := equivariant_preservesSSA store storeEquivariant afterGEP afterStore () storeRun
        have yieldedSame :
            (HeldMemoryFrames.replaceSSA afterStore stated.locals stated.nextValueId).lookupValue value =
              afterStore.lookupValue value := by
          rw [replaceSSA_lookup, publishState_lookup_other pointed names.state value _ valueState,
            publishState_lookup_other targetGEP names.pointer value _ valuePointer,
            replaceSSA_lookup, publishState_lookup_other state names.index value _ valueIndex]
          change state.locals.get value = afterStore.locals.get value
          rw [storeSSA.1, gepSSA.1]
        rw [lookupValue_run afterStore value,
          lookupValue_run (HeldMemoryFrames.replaceSSA afterStore stated.locals stated.nextValueId) value,
          yieldedSame]
        cases yielded : afterStore.lookupValue value with
        | none =>
          simp only [Except.bind]
          exact .error _
        | some returned =>
          simp only [Except.bind, Sem.run_pure]
          exact .returned [returned] _ _ rfl

/-- The entry operands belong to the complete original graph reservation
    set, whether they are declared, missing, or referenced by another row. -/
theorem suspend_entry_operands (blocks : List (BlockId × BasicBlock)) (entry : BlockId)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks entry = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :
    frame ∈ graphValueIds blocks ∧ value ∈ graphValueIds blocks := by
  obtain ⟨before, selectedId, after, decomposition, _, _⟩ := cfgOf_decompose blocks entry _ found
  have member : (.CoroSuspend frame slot next value, termDests) ∈ graphNodes blocks := by
    rw [decomposition, graphNodes_sourceEntry]
    exact trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _))
  constructor
  · exact graphNode_operand_mem blocks _ member frame ((trustIrListMemConsSelf _ _))
  · exact graphNode_operand_mem blocks _ member value
      (List.mem_cons_of_mem frame ((trustIrListMemConsSelf _ _)))

theorem GraphNames.different_original (blocks : List (BlockId × BasicBlock))
    (names : GraphNames blocks) (id : ValueId) (member : id ∈ graphValueIds blocks) :
    id ≠ (Names.ofTriple names).index ∧ id ≠ (Names.ofTriple names).pointer ∧
      id ≠ (Names.ofTriple names).state := by
  have unused := GraphNames.unused blocks names
  exact ⟨(fun same => unused.1 (same ▸ member)),
    (fun same => unused.2.1 (same ▸ member)),
    (fun same => unused.2.2 (same ▸ member))⟩

/-- Full callee outcomes from the actual cleared Call frame. Parameter
    arity/Char failures and fuel exhaustion are matching branches, not
    successful-input assumptions. Every non-SSA field is retained exactly. -/
theorem expandedGraph_effect (sourceCtx targetCtx : EvalContext) (models : sourceCtx.byteModel = targetCtx.byteModel)
    (header : EvalFunction)
    (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64)
    (fuel depth : Nat) (args : List Value) (strategy : PanicStrategy) (world : MachineState) :
    let source := {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
    let target := {header with
      cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock)
      localTypes := some targetTypes}
    EffectRelation
      (Sem.run (stepNWithContext (sourceCtx.forFunction source) fuel depth source.cfg source.entryBlock args strategy)
        (callerWorld world))
      (Sem.run (stepNWithContext (targetCtx.forFunction target) fuel depth target.cfg target.entryBlock args strategy)
        (callerWorld world)) := by
  dsimp only
  cases fuel with
  | zero => exact .error .outOfFuel
  | succ fuel =>
    let temps := Names.ofTriple names
    let target : EvalFunction := {header with
      cfg := cfgOf (expandedGraph temps blocks header.entryBlock)
      localTypes := some targetTypes}
    have targetFound : target.cfg header.entryBlock = some (expandedEntry temps {
        params := params
        body := []
        bodyResultDests := bodyDests
        terminator := .CoroSuspend frame slot next value
        terminatorResultDests := termDests }) := by
      change cfgOf (expandFirstEntry temps header.entryBlock blocks) header.entryBlock = _
      rw [cfgOf_expandFirstEntry, found]
      rfl
    rw [sourceEntry_eq _ fuel depth _ _ params args bodyDests termDests frame value slot next strategy found,
      targetEntry_eq (targetCtx.forFunction target) fuel depth target.cfg header.entryBlock temps params args
        bodyDests termDests frame value slot next strategy targetTypes rfl indexType pointerType stateType targetFound]
    rw [show (sourceCtx.forFunction {header with cfg := cfgOf blocks, localTypes := some sourceTypes}).byteModel =
      (targetCtx.forFunction target).byteModel from models]
    simp only [Sem.run_bind]
    cases parameterRun : Sem.run (bindBlockParamsChecked params args) (callerWorld world) with
    | error error => exact .error error
    | ok bound =>
      rcases bound with ⟨unit, afterParams⟩
      cases unit
      have fresh := SSAFreshFrames.bindBlockParamsChecked_preserves_fresh params args
        (callerWorld world) afterParams (SSAFreshFrames.cleared_fresh world) parameterRun
      have operands := suspend_entry_operands blocks header.entryBlock params bodyDests termDests
        frame value slot next found
      have frameFree := GraphNames.different_original blocks names frame operands.1
      have valueFree := GraphNames.different_original blocks names value operands.2
      have pointerState : temps.pointer ≠ temps.state := by
        intro same
        exact names.secondThird (congrArg ValueId.index same)
      exact expandedValues_effect (targetCtx.forFunction target) targetTypes temps frame value slot next
        rfl indexType pointerState frameFree.1 valueFree.1 valueFree.2.1 valueFree.2.2 afterParams fresh

private theorem bind_congr {α β : Type} (first : Sem α) {left right : α → Sem β}
    (tails : ∀ value, left value = right value) : first >>= left = first >>= right :=
  congrArg (first >>= ·) (funext tails)

/-- A real empty-body Call terminator enters the anchored Call helper under
    either panic strategy. Both resource indices are those of the actual
    evaluator, with the caller's one block/depth step removed exactly once. -/
theorem callEntry_succ (ctx : EvalContext) (fuel depth : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value) (callee : FuncId)
    (argIds : List ValueId) (strategy : PanicStrategy)
    (found : cfg pc = some {params := params, body := [], terminator := .Call callee argIds}) :
    stepNWithContext ctx (fuel + 1) (depth + 1) cfg pc args strategy = (do
      bindBlockParamsChecked params args
      let values ← argIds.mapM Sem.lookupValue
      runCallReq ctx fuel depth callee values strategy) := by
  cases strategy <;>
    simp only [stepNWithContext, found, EvalContext.resolveBlock, EvalContext.resolveDrop,
      List.map_nil, bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
      stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInst,
      runCallReq, EvalContext.lookupDirectCallee, pure_bind, bind_assoc]
  all_goals
    refine bind_congr _ fun _ => ?_
    refine bind_congr _ fun values => ?_
    cases lookup : ctx.functions callee with
    | none => cases ctx.declared callee <;> rfl
    | some function =>
      simp only [pure_bind]
      cases arity : checkCallArity values function.body.paramTys with
      | error message => simp only [arity]; rfl
      | ok unit => cases unit; simp only [arity, pure_bind]; rfl

theorem callEntry_zero_depth (ctx : EvalContext) (fuel : Nat) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value) (callee : FuncId)
    (argIds : List ValueId) (strategy : PanicStrategy)
    (found : cfg pc = some {params := params, body := [], terminator := .Call callee argIds}) :
    stepNWithContext ctx (fuel + 1) 0 cfg pc args strategy = (do
      bindBlockParamsChecked params args
      let _ ← argIds.mapM Sem.lookupValue
      throw SemError.outOfFuel) := by
  cases strategy <;>
    simp only [stepNWithContext, found, EvalContext.resolveBlock, EvalContext.resolveDrop,
      List.map_nil, bodyInstsWithResultDests, List.forIn_nil, List.forIn_cons,
      stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInst, pure_bind, bind_assoc]

def withFunction (ctx : EvalContext) (id : FuncId) (function : EvalFunction) : EvalContext :=
  {ctx with functions := fun query => if query == id then some function else ctx.functions query}

theorem withFunction_found (ctx : EvalContext) (id : FuncId) (function : EvalFunction) :
    (withFunction ctx id function).functions id = some function := by
  simp only [withFunction, beq_self_eq_true, if_true]

/-- Exact real-Call equality, including arbitrary caller bindings and both
    zero-budget branches. The only premise is a complete anchored Call-helper
    equality; it is supplied below by actual graph preparation and simulation. -/
theorem callEntry_eq_of_runCallReq (sourceCtx targetCtx : EvalContext)
    (callee : FuncId) (cfg : CFG) (pc : BlockId) (params : List (ValueId × Ty))
    (args : List Value) (argIds : List ValueId) (strategy : PanicStrategy)
    (found : cfg pc = some {params := params, body := [], terminator := .Call callee argIds})
    (calls : ∀ fuel depth values, runCallReq sourceCtx fuel depth callee values strategy =
      runCallReq targetCtx fuel depth callee values strategy) (fuel depth : Nat) :
    stepNWithContext sourceCtx fuel depth cfg pc args strategy =
      stepNWithContext targetCtx fuel depth cfg pc args strategy := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases depth with
    | zero => rw [callEntry_zero_depth _ _ _ _ _ _ _ _ strategy found,
        callEntry_zero_depth _ _ _ _ _ _ _ _ strategy found]
    | succ depth =>
      rw [callEntry_succ _ fuel depth _ _ _ _ _ _ strategy found,
        callEntry_succ _ fuel depth _ _ _ _ _ _ strategy found]
      exact bind_congr _ (fun _ => bind_congr _ (fun values => calls fuel depth values))

/-- Equality of the shared helper actually used by body Call/CallIndirect
    and their contextual evaluator paths. This quantifies the whole Sem
    computation, including every caller state and all header/body errors. -/
def RunCallEquivalent (source target : EvalFunction) : Prop :=
  ∀ (ctx : EvalContext) (callee : FuncId) (fuel depth : Nat)
    (values : List Value) (strategy : PanicStrategy),
    runCallReq (withFunction ctx callee source) fuel depth callee values strategy =
      runCallReq (withFunction ctx callee target) fuel depth callee values strategy

/-- Equality at the actual Call boundary for every caller context and state,
    arbitrary caller parameter/operand rows, both strategies and both resource
    budgets. Equality of Sem computations compares the complete caller world,
    including the original SSA frame and float-choice fields. -/
def CallEquivalent (source target : EvalFunction) : Prop :=
  ∀ (ctx : EvalContext) (callee : FuncId) (cfg : CFG) (pc : BlockId)
    (params : List (ValueId × Ty)) (args : List Value) (argIds : List ValueId)
    (strategy : PanicStrategy),
    cfg pc = some {params := params, body := [], terminator := .Call callee argIds} →
    ∀ fuel depth,
      stepNWithContext (withFunction ctx callee source) fuel depth cfg pc args strategy =
        stepNWithContext (withFunction ctx callee target) fuel depth cfg pc args strategy

theorem expandedGraph_runCallEquivalent (header : EvalFunction)
    (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64) :
    RunCallEquivalent {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
      {header with
        cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock)
        localTypes := some targetTypes} := by
  intro ctx callee fuel depth values strategy
  let source : EvalFunction := {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
  let target : EvalFunction := {header with
    cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock)
    localTypes := some targetTypes}
  apply runCallReq_eq_of_effectRelation (withFunction ctx callee source) (withFunction ctx callee target)
    fuel depth callee values strategy source target
    (withFunction_found ctx callee source) (withFunction_found ctx callee target) rfl
  intro world
  exact expandedGraph_effect (withFunction ctx callee source) (withFunction ctx callee target) rfl
    header blocks names sourceTypes targetTypes params bodyDests termDests frame value slot next
    found indexType pointerType stateType fuel depth values strategy world

theorem expandedGraph_callEquivalent (header : EvalFunction)
    (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64) :
    CallEquivalent {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
      {header with
        cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock)
        localTypes := some targetTypes} := by
  intro ctx callee callerCFG pc callerParams args argIds strategy callerEntry fuel depth
  apply callEntry_eq_of_runCallReq _ _ callee callerCFG pc callerParams args argIds strategy callerEntry
    (fuel := fuel) (depth := depth)
  intro calleeFuel calleeDepth values
  exact expandedGraph_runCallEquivalent header blocks names sourceTypes targetTypes params bodyDests
    termDests frame value slot next found indexType pointerType stateType
    ctx callee calleeFuel calleeDepth values strategy

/-- The preparation result has three explicit meanings. Source metadata
    failure is unchanged, capacity means that three distinct unused u32 ids
    genuinely do not exist, and a completed expansion connects BOTH actual
    inferred graphs and every full Call outcome. -/
def ExpansionCorrect (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) :
    Except SemError (FunctionExpansion blocks) → Prop
  | .error error => functionOfGraph direct indirect header blocks = .error error
  | .ok (.capacity source _certificate) =>
    functionOfGraph direct indirect header blocks = .ok source ∧ ¬ Nonempty (GraphNames blocks)
  | .ok (.expanded source target names) =>
    functionOfGraph direct indirect header blocks = .ok source ∧
    functionOfGraph direct indirect header
      (expandedGraph (Names.ofTriple names) blocks header.entryBlock) = .ok target ∧
    RunCallEquivalent source target ∧ CallEquivalent source target

/-- Generic source-aware CoroSuspend entry expansion at the REAL Call frame
    boundary. The complete finite graph supplies every reservation and both
    inferred tables. No source-inference success, capacity, freshness, type,
    non-poison, argument-validity or successful-run premise is added. Missing
    inputs, metadata errors, all body failures, zero budgets and both panic
    strategies remain explicit outcomes. Only the selected empty-body suspend
    entry is expanded; all other source blocks and headers are retained.
    The ready branch exposes the actual shared Call helper as well as the
    manual empty-caller wrapper, so body calls can consume the equality. -/
theorem functionsOfExpansion_correct (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock))
    (params : List (ValueId × Ty)) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params
      body := []
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :
    ExpansionCorrect direct indirect header blocks
      (functionsOfExpansion direct indirect header blocks) := by
  cases sourceRun : inferLocalTypesWithEvidence direct indirect (graphParams blocks) (graphNodes blocks) with
  | error error =>
    simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, Bind.bind,
      Pure.pure, Except.bind, Except.pure, ExpansionCorrect,
      functionOfGraph, inferLocalTypes, inferLocalTypesWithWork]
  | ok inferred =>
    have sourceBuilt := functionOfGraph_of_inference direct indirect header blocks inferred sourceRun
    cases allocation : GenericCoroFreshIds.u32Names (graphReservations blocks) with
    | capacity certificate =>
      simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, allocation,
        Bind.bind, Pure.pure, Except.bind, Except.pure, ExpansionCorrect]
      refine ⟨sourceBuilt, ?_⟩
      intro available
      obtain ⟨names⟩ := available
      exact GenericCoroFreshIds.capacity_excludes_triple certificate names
    | ready names =>
      obtain ⟨targetInferred, targetRun, indexType, pointerType, stateType, _⟩ :=
        expandedGraph_inference direct indirect blocks header.entryBlock params bodyDests termDests
          frame value slot next names inferred found sourceRun
      have targetBuilt := functionOfGraph_of_inference direct indirect header
        (expandedGraph (Names.ofTriple names) blocks header.entryBlock) targetInferred targetRun
      simp only [functionsOfExpansion, functionOfGraphWithEvidence, sourceRun, allocation,
        targetBuilt, Bind.bind, Pure.pure, Except.bind, Except.pure, ExpansionCorrect]
      exact ⟨sourceBuilt, True.intro,
        expandedGraph_runCallEquivalent header blocks names inferred.table targetInferred.table
          params bodyDests termDests frame value slot next found indexType pointerType stateType,
        expandedGraph_callEquivalent header blocks names inferred.table targetInferred.table
          params bodyDests termDests frame value slot next found indexType pointerType stateType⟩

end TrustIr.GenericCoro

#trustIrAxiomsExact TrustIr.GenericCoro.lookupValue_run == [propext]

#trustIrAxiomsExact TrustIr.GenericCoro.expandedEntry == []
#trustIrAxiomsExact TrustIr.GenericCoro.expandedEntry_params == []
#trustIrAxiomsExact TrustIr.GenericCoro.expandedEntry_result_classifications == []
