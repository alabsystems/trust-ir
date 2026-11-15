-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixStep
import TrustIr.Proofs.GenericCoroPrefixLoop

namespace TrustIr.GenericCoro.Prefix

theorem bind_same {α β : Type} (first : Sem α) {source target : α → Sem β}
    (same : ∀ value, source value = target value) : (first >>= source) = (first >>= target) :=
  congrArg (fun next => first >>= next) (funext same)

theorem throw_bind_sem {α β : Type} (error : SemError) (next : α → Sem β) :
    ((throw error : Sem α) >>= next) = (throw error : Sem β) := rfl

theorem run_throw_sem {α : Type} (error : SemError) (state : MachineState) :
    Sem.run (throw error : Sem α) state = .error error := rfl

theorem run_get_sem (state : MachineState) :
    Sem.run Sem.getState state = .ok (state, state) := rfl

theorem run_set_sem (replacement state : MachineState) :
    Sem.run (Sem.setState replacement) state = .ok ((), replacement) := rfl

theorem bind_match_except {ε α β γ : Type} (choice : Except ε α)
    (success : α → Sem β) (failure : ε → Sem β) (next : β → Sem γ) :
    ((match choice with | .ok value => success value | .error error => failure error) >>= next) =
      (match choice with
       | .ok value => success value >>= next
       | .error error => failure error >>= next) := by
  cases choice <;> rfl

theorem bind_match_option {α β γ : Type} (choice : Option α)
    (success : α → Sem β) (failure : Sem β) (next : β → Sem γ) :
    ((match choice with | some value => success value | none => failure) >>= next) =
      (match choice with
       | some value => success value >>= next
       | none => failure >>= next) := by
  cases choice <;> rfl

theorem bind_match_unit {ε β γ : Type} (choice : Except ε Unit)
    (success : Sem β) (failure : ε → Sem β) (next : β → Sem γ) :
    ((match choice with | .ok () => success | .error error => failure error) >>= next) =
      (match choice with
       | .ok () => success >>= next
       | .error error => failure error >>= next) := by
  cases choice with
  | ok unit => cases unit; rfl
  | error error => rfl

theorem bind_ite_sem {α β : Type} (condition : Prop) [Decidable condition]
    (yes no : Sem α) (next : α → Sem β) :
    ((if condition then yes else no) >>= next) =
      (if condition then yes >>= next else no >>= next) := by
  split <;> rfl

theorem typedClosure_ite {α : Type} (held : Value) (yes no : Sem α) :
    (if (match held with | .typedClosure _ _ _ => true | _ => false) then yes else no) =
      (match held with | .typedClosure _ _ _ => yes | _ => no) := by
  cases held <;> rfl

theorem forIn_equivariant {α β : Type} (items : List α) (initial : β)
    (action : α → β → Sem (ForInStep β))
    (equivariant : ∀ item ∈ items, ∀ state, HeldMemoryFrames.Equivariant (action item state)) :
    HeldMemoryFrames.Equivariant (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact HeldMemoryFrames.pure_eqv initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply HeldMemoryFrames.bind_eqv _ _ (equivariant item ((trustIrListMemConsSelf _ _)) initial)
    intro step
    cases step with
    | done value => exact HeldMemoryFrames.pure_eqv value
    | yield value => exact ih value (fun item member => equivariant item (List.mem_cons_of_mem _ member))

/-- The return checks may inspect values and the non-SSA world. Restoring the
    actual saved frame still yields full caller equality for every outcome. -/
def finishCalleeWith (check : List Value → Sem Unit) (frame : StackFrame)
    (callee : Sem (List Value)) : Sem (List Value) := do
  let values ← callee
  check values
  let state ← Sem.getState
  Sem.setState (restoreFrame state frame [])
  pure values

theorem finishCalleeWith_eq_of_effectRelation (check : List Value → Sem Unit)
    (equivariant : ∀ values, HeldMemoryFrames.Equivariant (check values))
    (frame : StackFrame) (source target : Sem (List Value))
    (sourceState targetState : MachineState)
    (related : EffectRelation (Sem.run source sourceState) (Sem.run target targetState)) :
    Sem.run (finishCalleeWith check frame source) sourceState =
      Sem.run (finishCalleeWith check frame target) targetState := by
  unfold finishCalleeWith
  simp only [Sem.run_bind]
  generalize sourceRun : Sem.run source sourceState = sourceResult at related ⊢
  generalize targetRun : Sem.run target targetState = targetResult at related ⊢
  cases related with
  | error error => rfl
  | returned values source target world =>
    simp only [Except.bind]
    rw [equivariant_transport (check values) (equivariant values) source target world]
    cases checked : Sem.run (check values) source with
    | error error => rfl
    | ok result => rfl

def callFrameWith (check : List Value → Sem Unit) (callee : Sem (List Value)) : Sem (List Value) := do
  let caller ← Sem.getState
  Sem.setState (callerWorld caller)
  finishCalleeWith check (saveFrame caller none) callee

theorem callFrameWith_eq_of_effectRelation (check : List Value → Sem Unit)
    (equivariant : ∀ values, HeldMemoryFrames.Equivariant (check values))
    (source target : Sem (List Value))
    (related : ∀ world, EffectRelation
      (Sem.run source (callerWorld world)) (Sem.run target (callerWorld world))) :
    callFrameWith check source = callFrameWith check target := by
  funext world
  exact finishCalleeWith_eq_of_effectRelation check equivariant (saveFrame world none)
    source target (callerWorld world) (callerWorld world) (related world)

def checkReturns (ctx : EvalContext) (returnTys : List Ty)
    (poison : Bool) (closure : Bool) (message : String) (values : List Value) : Sem Unit :=
  (match checkReturnArity values returnTys with
   | .ok () => pure ()
   | .error error => Sem.throwTypeError (message ++ error)) >>= fun _ =>
  (if poison then Sem.rejectPoisonValues values "Call returns" else pure ()) >>= fun _ =>
  if closure then do
    for (ty, value) in returnTys.zip values do
      match checkClosureValue ctx ty value with
      | .ok () => pure ()
      | .error error => throw error
  else pure ()

theorem checkReturns_equivariant (ctx : EvalContext) (returnTys : List Ty)
    (poison closure : Bool) (message : String) (values : List Value) :
    HeldMemoryFrames.Equivariant (checkReturns ctx returnTys poison closure message values) := by
  unfold checkReturns
  apply HeldMemoryFrames.bind_eqv
  · split <;> first
    | exact HeldMemoryFrames.pure_eqv _
    | exact HeldMemoryFrames.throw_eqv _
  · intro unit
    apply HeldMemoryFrames.bind_eqv
    · cases poison <;>
        simp only [Bool.false_eq_true, if_false, if_true]
      · exact HeldMemoryFrames.pure_eqv _
      · unfold Sem.rejectPoisonValues
        split <;> first
          | exact HeldMemoryFrames.pure_eqv _
          | exact HeldMemoryFrames.throw_eqv _
    · intro unit
      cases closure <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact HeldMemoryFrames.pure_eqv _
      · apply HeldMemoryFrames.bind_eqv
        · apply forIn_equivariant
          intro input member state
          cases input
          dsimp only
          split <;> first
            | exact HeldMemoryFrames.pure_eqv _
            | exact HeldMemoryFrames.throw_bind_eqv _ _
        · intro unit
          exact HeldMemoryFrames.pure_eqv _

theorem checkReturns_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (returnTys : List Ty) (poison closure : Bool) (message : String) (values : List Value) :
    checkReturns (scopedContext base functions types) returnTys poison closure message values =
      checkReturns base returnTys poison closure message values := by
  simp only [checkReturns, checkClosureValue_scoped]

theorem checkReturns_scoped_function (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (returnTys : List Ty) (poison closure : Bool) (message : String) :
    checkReturns (scopedContext base functions types) returnTys poison closure message =
      checkReturns base returnTys poison closure message :=
  funext (fun values => checkReturns_scoped base functions types returnTys poison closure message values)

/-- Continuation normalization keeps the return checker abstract until its
    own small match is selected; it never unfolds the recursive callee. -/
theorem callFrameWith_checkReturns_bind {α : Type} (ctx : EvalContext)
    (returnTys : List Ty) (poison closure : Bool) (message : String)
    (callee : Sem (List Value)) (next : List Value → Sem α) :
    (callFrameWith (checkReturns ctx returnTys poison closure message) callee >>= next) = (do
      let caller ← Sem.getState
      Sem.setState (callerWorld caller)
      let values ← callee
      match checkReturnArity values returnTys with
      | .ok () => pure ()
      | .error error => Sem.throwTypeError (message ++ error)
      if poison then Sem.rejectPoisonValues values "Call returns"
      if closure then
        for (ty, value) in returnTys.zip values do
          match checkClosureValue ctx ty value with
          | .ok () => pure ()
          | .error error => throw error
      let state ← Sem.getState
      Sem.setState (restoreFrame state (saveFrame caller none) [])
      next values) := by
  simp only [callFrameWith, finishCalleeWith, bind_assoc]
  apply bind_same
  intro caller
  apply bind_same
  intro unit
  apply bind_same
  intro values
  cases arity : checkReturnArity values returnTys with
  | error error =>
    cases poison <;> cases closure <;>
      simp only [checkReturns, arity, Bool.true_eq, Bool.false_eq_true,
        if_true, if_false, bind_assoc, pure_bind]

  | ok unit =>
    cases unit
    cases poison <;> cases closure <;>
      simp only [checkReturns, arity, Bool.true_eq, Bool.false_eq_true,
        if_true, if_false, bind_assoc, pure_bind]

theorem callFrameWith_arity_bind {α : Type} (ctx : EvalContext)
    (returnTys : List Ty) (message : String) (callee : Sem (List Value))
    (next : List Value → Sem α) :
    (callFrameWith (checkReturns ctx returnTys false false message) callee >>= next) = (do
      let caller ← Sem.getState
      Sem.setState (callerWorld caller)
      let values ← callee
      match checkReturnArity values returnTys with
      | .ok () => pure ()
      | .error error => Sem.throwTypeError (message ++ error)
      let state ← Sem.getState
      Sem.setState (restoreFrame state (saveFrame caller none) [])
      next values) := by
  simpa only [Bool.false_eq_true, if_false, pure_bind] using
    callFrameWith_checkReturns_bind ctx returnTys false false message callee next

/-- Recursive hypotheses are stated at actual function-table lookups. The
    callee starts in a cleared frame; no condition is imposed on the caller. -/
def CalleeEffects (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) : Prop :=
  ∀ id sourceFunction targetFunction,
    source id = some sourceFunction → target id = some targetFunction →
    ∀ depth args strat world,
      EffectRelation
        (Sem.run (sourceRecurse (scopedContext base source sourceFunction.localTypes)
          depth sourceFunction.cfg sourceFunction.entryBlock args strat) (callerWorld world))
        (Sem.run (targetRecurse (scopedContext base target targetFunction.localTypes)
          depth targetFunction.cfg targetFunction.entryBlock args strat) (callerWorld world))

def bodyCall (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (id : FuncId) (args : List ValueId)
    (dests : List ValueId) : Sem (ForInStep Unit) := do
  let values ← args.mapM Sem.lookupValue
  match depth with
  | 0 => throw SemError.outOfFuel
  | depth + 1 =>
    let callee ← ctx.lookupDirectCallee id
      "Call: callee is a bodyless declaration" "Call: undefined function"
    directCallHeader callee.body values
    let results ← callFrame callee.body.returnTys
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock values strat)
    ctx.bindCallResults (.Call id args) dests results
  pure (.yield ())

theorem evalBodyStep_call (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (id : FuncId) (args dests : List ValueId) :
    evalBodyStep recurse ctx depth strat (.Call id args, dests) =
      bodyCall recurse ctx depth strat id args dests := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [evalBodyStep, bodyCall, bind_assoc]
    congr 1
    funext values
    congr 1
    funext callee
    cases arity : checkCallArity values callee.body.paramTys with
    | error message =>
      simp only [directCallHeader, callFrame, finishCall, callerWorld,
        arity, pure_bind, bind_assoc]
      funext state
      change Sem.run _ state = Sem.run _ state
      simp only [Sem.run_bind, Sem.run_pure, Except.bind]
      repeat' (first | rfl | simp_all only [Sem.run_bind, Sem.run_pure, Except.bind] | split)
    | ok unit =>
      cases unit
      simp only [directCallHeader, callFrame, finishCall, callerWorld,
        arity, pure_bind, bind_assoc]
      funext state
      change Sem.run _ state = Sem.run _ state
      simp only [Sem.run_bind, Sem.run_pure, Except.bind]
      repeat' (first | rfl | simp_all only [Sem.run_bind, Sem.run_pure, Except.bind] | split)

theorem scopedContext_forFunction (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (function : EvalFunction) :
    (scopedContext base functions types).forFunction function =
      scopedContext base functions function.localTypes := rfl

theorem bodyCall_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (strat : PanicStrategy) (id : FuncId) (args dests : List ValueId)
    (types : TypesAgreeOn (dests ++ args) sourceTypes targetTypes) :
    bodyCall sourceRecurse (scopedContext base source sourceTypes) depth strat id args dests =
      bodyCall targetRecurse (scopedContext base target targetTypes) depth strat id args dests := by
  unfold bodyCall
  congr 1
  funext values
  cases depth with
  | zero => rfl
  | succ depth =>
    have related := headers id
    cases sourceFound : source id with
    | none =>
      cases targetFound : target id with
      | none =>
        simp only [EvalContext.lookupDirectCallee, scopedContext, sourceFound, targetFound]
        split <;> rfl
      | some targetFunction => rw [sourceFound, targetFound] at related; cases related
    | some sourceFunction =>
      cases targetFound : target id with
      | none => rw [sourceFound, targetFound] at related; cases related
      | some targetFunction =>
        rw [sourceFound, targetFound] at related
        cases related with
        | present _ _ body convention =>
          have framed := callFrame_eq_of_effectRelation sourceFunction.body.returnTys
            (sourceRecurse (scopedContext base source sourceFunction.localTypes)
              depth sourceFunction.cfg sourceFunction.entryBlock values strat)
            (targetRecurse (scopedContext base target targetFunction.localTypes)
              depth targetFunction.cfg targetFunction.entryBlock values strat)
            (effects id sourceFunction targetFunction sourceFound targetFound depth values strat)
          simp only [EvalContext.lookupDirectCallee,
            show (scopedContext base source sourceTypes).functions id = some sourceFunction from sourceFound,
            show (scopedContext base target targetTypes).functions id = some targetFunction from targetFound,
            pure_bind, scopedContext_forFunction, ← body, framed,
            bindCallResults_congr base source target headers sourceTypes targetTypes (.Call id args) dests _ types]

end TrustIr.GenericCoro.Prefix
