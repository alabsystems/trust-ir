-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCalls

namespace TrustIr.GenericCoro.Prefix

def rawIndirectArguments (ctx : EvalContext) (address : Addr) (sig : FuncTyId)
    (args : List Value) : Sem (FuncId × List Value) := do
  let id ← match ctx.funcPtrs address with
    | some id => pure id
    | none => Sem.throwUB "CallIndirect: invalid function pointer"
  let signature ← match ctx.funcTys sig with
    | some signature => pure signature
    | none => Sem.throwTypeError "CallIndirect: undefined function type"
  let callee ← match ctx.functions id with
    | some callee => pure callee
    | none => Sem.throwTypeError "CallIndirect: undefined function"
  requireUntypedAbi signature.abi
  match checkIndirectSignature signature callee.body with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError (trustIrStringBuild ("CallIndirect: " ++ message))
  pure (id, args)

def rawIndirectArgumentsWith {α : Type} (ctx : EvalContext) (address : Addr) (sig : FuncTyId)
    (args : List Value) (next : FuncId × List Value → Sem α) : Sem α := do
  let id ← match ctx.funcPtrs address with
    | some id => pure id
    | none => Sem.throwUB "CallIndirect: invalid function pointer"
  let signature ← match ctx.funcTys sig with
    | some signature => pure signature
    | none => Sem.throwTypeError "CallIndirect: undefined function type"
  let callee ← match ctx.functions id with
    | some callee => pure callee
    | none => Sem.throwTypeError "CallIndirect: undefined function"
  requireUntypedAbi signature.abi
  match checkIndirectSignature signature callee.body with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError (trustIrStringBuild ("CallIndirect: " ++ message))
  next (id, args)

theorem rawIndirectArguments_bind {α : Type} (ctx : EvalContext) (address : Addr) (sig : FuncTyId)
    (args : List Value) (next : FuncId × List Value → Sem α) :
    (rawIndirectArguments ctx address sig args >>= next) =
      rawIndirectArgumentsWith ctx address sig args next := by
  cases pointer : ctx.funcPtrs address with
  | none => simp only [rawIndirectArguments, rawIndirectArgumentsWith, pointer]; rfl
  | some id =>
    cases signature : ctx.funcTys sig with
    | none => simp only [rawIndirectArguments, rawIndirectArgumentsWith, pointer, signature, pure_bind]; rfl
    | some declaration =>
      cases function : ctx.functions id with
      | none =>
        simp only [rawIndirectArguments, rawIndirectArgumentsWith, pointer, signature, function, pure_bind]
        rfl
      | some callee =>
        cases checked : checkIndirectSignature declaration callee.body with
        | error message =>
          simp only [rawIndirectArguments, rawIndirectArgumentsWith, pointer, signature, function,
            checked, pure_bind, bind_assoc]
        | ok unit =>
          cases unit
          simp only [rawIndirectArguments, rawIndirectArgumentsWith, pointer, signature, function,
            checked, pure_bind, bind_assoc]

theorem rawIndirectArguments_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (address : Addr) (sig : FuncTyId)
    (args : List Value) :
    rawIndirectArguments (scopedContext base source sourceTypes) address sig args =
      rawIndirectArguments (scopedContext base target targetTypes) address sig args := by
  unfold rawIndirectArguments
  cases pointer : base.funcPtrs address with
  | none =>
    simp only [scopedContext, pointer]
    rfl
  | some id =>
    cases signature : base.funcTys sig with
    | none =>
      simp only [scopedContext, pointer, signature, pure_bind]
      rfl
    | some signatureDefinition =>
      have related := headers id
      cases sourceFound : source id with
      | none =>
        cases targetFound : target id with
        | none =>
          simp only [scopedContext, pointer, signature, sourceFound, targetFound, pure_bind]
        | some targetFunction => rw [sourceFound, targetFound] at related; cases related
      | some sourceFunction =>
        cases targetFound : target id with
        | none => rw [sourceFound, targetFound] at related; cases related
        | some targetFunction =>
          rw [sourceFound, targetFound] at related
          cases related with
          | present _ _ body convention =>
            simp only [scopedContext, pointer, signature, sourceFound, targetFound, body, pure_bind]

def indirectArguments (ctx : EvalContext) (value : Value) (address : Addr)
    (sig : FuncTyId) (args : List Value) (conv : CallingConv) : Sem (FuncId × List Value) :=
  match value with
  | .fnDef held target =>
    match functionCallWithConvention ctx held target sig conv with
    | .ok fn => pure (fn, args)
    | .error error => throw error
  | .typedClosure cid fn captures =>
    match closureCall ctx cid fn captures sig args conv with
    | .ok call => pure call
    | .error error => throw error
  | _ => rawIndirectArguments ctx address sig args

def indirectArgumentsWith {α : Type} (ctx : EvalContext) (value : Value) (address : Addr)
    (sig : FuncTyId) (args : List Value) (conv : CallingConv)
    (next : FuncId × List Value → Sem α) : Sem α :=
  match value with
  | .fnDef held target =>
    match functionCallWithConvention ctx held target sig conv with
    | .ok fn => next (fn, args)
    | .error error => throw error
  | .typedClosure cid fn captures =>
    match closureCall ctx cid fn captures sig args conv with
    | .ok call => next call
    | .error error => throw error
  | _ => rawIndirectArgumentsWith ctx address sig args next

theorem indirectArguments_bind {α : Type} (ctx : EvalContext) (value : Value) (address : Addr)
    (sig : FuncTyId) (args : List Value) (conv : CallingConv)
    (next : FuncId × List Value → Sem α) :
    (indirectArguments ctx value address sig args conv >>= next) =
      indirectArgumentsWith ctx value address sig args conv next := by
  cases value
  case fnDef held fn =>
    cases found : functionCallWithConvention ctx held fn sig conv <;>
      simp only [indirectArguments, indirectArgumentsWith, found, pure_bind] <;> rfl
  case typedClosure cid fn captures =>
    cases found : closureCall ctx cid fn captures sig args conv <;>
      simp only [indirectArguments, indirectArgumentsWith, found, pure_bind] <;> rfl
  all_goals exact rawIndirectArguments_bind ctx address sig args next

theorem indirectArguments_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (value : Value) (address : Addr)
    (sig : FuncTyId) (args : List Value) (conv : CallingConv) :
    indirectArguments (scopedContext base source sourceTypes) value address sig args conv =
      indirectArguments (scopedContext base target targetTypes) value address sig args conv := by
  cases value <;>
    simp only [indirectArguments,
      functionCallWithConvention_congr base source target headers sourceTypes targetTypes,
      closureCall_congr base source target headers sourceTypes targetTypes,
      rawIndirectArguments_congr base source target headers sourceTypes targetTypes]

trustIrDenseMatch
def indirectAddress (value : Value) : Sem Addr :=
  match value with
  | .ptr address _ => pure address
  | .fnDef _ _ | .fnItem _ | .typedClosure _ _ _ => pure 0
  | .nullPtr => Sem.throwTypeError "CallIndirect: null function pointer"
  | _ => Sem.throwTypeError "CallIndirect: callee is not a pointer or typed closure"

/-- The actual nominal-item branch checks its original contract before
    looking up arguments. Other modes retain their pre-depth lookup order. -/
def deferredIndirectArguments (ctx : EvalContext) (value : Value) (address : Addr)
    (sig : FuncTyId) (argIds : List ValueId) (args : List Value) (conv : CallingConv) :
    Sem (FuncId × List Value) :=
  match value with
  | .fnItem target =>
    match functionItemCall ctx target sig conv with
    | .ok fn => do pure (fn, ← argIds.mapM Sem.lookupValue)
    | .error error => throw error
  | _ => indirectArguments ctx value address sig args conv

private def deferredIndirectArgumentsWith {α : Type} (ctx : EvalContext) (value : Value)
    (address : Addr) (sig : FuncTyId) (argIds : List ValueId) (args : List Value)
    (conv : CallingConv) (next : FuncId × List Value → Sem α) : Sem α :=
  match value with
  | .fnItem target =>
    match functionItemCall ctx target sig conv with
    | .ok fn => do next (fn, ← argIds.mapM Sem.lookupValue)
    | .error error => throw error
  | _ => indirectArgumentsWith ctx value address sig args conv next

private theorem deferredIndirectArguments_bind {α : Type} (ctx : EvalContext) (value : Value)
    (address : Addr) (sig : FuncTyId) (argIds : List ValueId) (args : List Value)
    (conv : CallingConv) (next : FuncId × List Value → Sem α) :
    (deferredIndirectArguments ctx value address sig argIds args conv >>= next) =
      deferredIndirectArgumentsWith ctx value address sig argIds args conv next := by
  cases value
  case fnItem target =>
    cases found : functionItemCall ctx target sig conv <;>
      simp only [deferredIndirectArguments, deferredIndirectArgumentsWith, found, pure_bind, bind_assoc]
    all_goals rfl
  all_goals
    simp only [deferredIndirectArguments, deferredIndirectArgumentsWith, indirectArguments_bind]

private theorem deferredIndirectArguments_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (value : Value) (address : Addr)
    (sig : FuncTyId) (argIds : List ValueId) (args : List Value) (conv : CallingConv) :
    deferredIndirectArguments (scopedContext base source sourceTypes) value address sig argIds args conv =
      deferredIndirectArguments (scopedContext base target targetTypes) value address sig argIds args conv := by
  cases value <;>
    simp only [deferredIndirectArguments, functionItemCall_scoped,
      indirectArguments_congr base source target headers sourceTypes targetTypes]

def bodyIndirect (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (dests : List ValueId) : Sem (ForInStep Unit) := do
  let held ← Sem.lookupValue calleeId
  let _ ← Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx calleeId held)
  let address ← indirectAddress held
  let values ← match held with
    | .fnItem _ => pure []
    | _ => args.mapM Sem.lookupValue
  match depth with
  | 0 => throw SemError.outOfFuel
  | depth + 1 =>
    let (id, values) ← deferredIndirectArguments ctx held address sig args values conv
    let callee ← match ctx.functions id with
      | some callee => pure callee
      | none =>
        match held with
        | .fnItem _ => Sem.fromMemoryExcept (resolveFunctionItemBody ctx id)
        | _ => Sem.throwTypeError "CallIndirect: undefined function"
    requireUntypedAbi callee.body.abi
    match checkCallArity values callee.body.paramTys with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("CallIndirect: " ++ message)
    Sem.rejectPoisonValues values "CallIndirect arguments"
    let results ← callFrameWith
      (checkReturns ctx callee.body.returnTys true
        (match held with | .typedClosure _ _ _ => true | _ => false) "CallIndirect: ")
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock values strat)
    ctx.bindCallResults (.CallIndirect calleeId sig args conv) dests results
  pure (.yield ())

theorem evalBodyStep_indirect (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (callee : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (dests : List ValueId) :
    evalBodyStep recurse ctx depth strat (.CallIndirect callee sig args conv, dests) =
      bodyIndirect recurse ctx depth strat callee sig args conv dests := by
  simp only [evalBodyStep, bodyIndirect, bind_assoc]
  apply bind_same
  intro held
  apply bind_same
  intro checked
  cases held <;> simp only [indirectAddress, pure_bind, bind_assoc]
  all_goals first
    | rfl
    | simp only [deferredIndirectArguments_bind, deferredIndirectArgumentsWith,
        indirectArguments_bind, indirectArgumentsWith, rawIndirectArgumentsWith, callFrameWith_checkReturns_bind,
        callerWorld, bind_assoc, pure_bind, bind_match_option, bind_match_except,
        bind_match_unit, bind_ite_sem, Bool.true_eq, Bool.false_eq_true, if_true, if_false]
      repeat' (first
        | rw (config := { transparency := .default }) [callFrameWith_checkReturns_bind]
        | rw (config := { transparency := .default }) [deferredIndirectArguments_bind]
        | rw (config := { transparency := .default }) [indirectArguments_bind]
        | rw (config := { transparency := .default }) [bind_match_option]
        | rw (config := { transparency := .default }) [bind_match_except]
        | rw (config := { transparency := .default }) [bind_match_unit])
      rfl

/-- Factor the actual mode-dependent lookup prefix while the continuation
    remains abstract. FnItems defer lookups; every legacy mode still performs
    the same eager traversal. No lookup success is assumed. -/
private theorem modeArguments_congr {α : Type} (held : Value) (args : List ValueId)
    (source target : List Value → Sem α) (same : ∀ values, source values = target values) :
    (match held with
      | .fnItem _ => do let values ← pure []; source values
      | _ => do let values ← args.mapM Sem.lookupValue; source values) =
    (match held with
      | .fnItem _ => do let values ← pure []; target values
      | _ => do let values ← args.mapM Sem.lookupValue; target values) := by
  cases held
  case fnItem targetId => simpa only [pure_bind] using same []
  all_goals exact bind_same _ same

/-- A guaranteed pure error erases its continuation. The Unit observation
    preserves the complete error, including bodyless/undefined distinctions. -/
private theorem failingMemoryExcept_congr {α β : Type}
    (source target : Except SemError α)
    (observation : source.map (fun _ => ()) = target.map (fun _ => ()))
    (fails : ∀ value, source ≠ .ok value) (sourceNext targetNext : α → Sem β) :
    (Sem.fromMemoryExcept source >>= sourceNext) =
      (Sem.fromMemoryExcept target >>= targetNext) := by
  cases source with
  | ok value => exact False.elim (fails value rfl)
  | error error =>
    cases target with
    | ok value => cases observation
    | error targetError =>
      simp only [Except.map] at observation
      cases observation
      rfl

private theorem missingBody_not_ok (ctx : EvalContext) (id : FuncId)
    (missing : ctx.functions id = none) :
    ∀ value, resolveFunctionItemBody ctx id ≠ .ok value := by
  intro value
  cases errorFound : ctx.functionErrors id with
  | some error =>
    simp only [resolveFunctionItemBody, missing, errorFound]
    intro impossible
    cases impossible
  | none =>
    simp only [resolveFunctionItemBody, missing, errorFound]
    split <;> intro impossible <;> cases impossible

/-- Erase callbacks before instantiating the real contexts or splitting their
    resolver metadata. Legacy modes retain the same direct undefined error. -/
private theorem absentBody_congr {α : Type} (held : Value)
    (source target : Except SemError EvalFunction)
    (observation : source.map (fun _ => ()) = target.map (fun _ => ()))
    (fails : ∀ value, source ≠ .ok value)
    (sourceNext targetNext : EvalFunction → Sem α) :
    (match held with
      | .fnItem _ => Sem.fromMemoryExcept source >>= sourceNext
      | _ => Sem.throwTypeError "CallIndirect: undefined function" >>= sourceNext) =
    (match held with
      | .fnItem _ => Sem.fromMemoryExcept target >>= targetNext
      | _ => Sem.throwTypeError "CallIndirect: undefined function" >>= targetNext) := by
  cases held
  case fnItem id => exact failingMemoryExcept_congr source target observation fails sourceNext targetNext
  all_goals rfl

theorem bodyIndirect_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (strat : PanicStrategy) (calleeId : ValueId) (sig : FuncTyId)
    (args : List ValueId) (conv : CallingConv) (dests : List ValueId)
    (types : TypesAgreeOn (dests ++ calleeId :: args) sourceTypes targetTypes) :
    bodyIndirect sourceRecurse (scopedContext base source sourceTypes) depth strat calleeId sig args conv dests =
      bodyIndirect targetRecurse (scopedContext base target targetTypes) depth strat calleeId sig args conv dests := by
  have calleeTypes (held : Value) :
      checkFunctionItemCalleeType (scopedContext base source sourceTypes) calleeId held =
        checkFunctionItemCalleeType (scopedContext base target targetTypes) calleeId held := by
    apply checkFunctionItemCalleeType_scoped_congr
    cases types with
    | absent => rfl
    | present sourceTable targetTable agree =>
      exact agree calleeId (trustIrListMemAppendRight _ (trustIrListMemConsSelf _ _))
  unfold bodyIndirect
  apply bind_same
  intro held
  rw [calleeTypes]
  apply bind_same
  intro checked
  apply bind_same
  intro address
  apply modeArguments_congr held args
  intro values
  dsimp only
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [deferredIndirectArguments_congr base source target headers sourceTypes targetTypes]
    apply bind_same
    intro resolved
    rcases resolved with ⟨id, callArgs⟩
    dsimp only
    have related := headers id
    cases sourceFound : source id with
    | none =>
      cases targetFound : target id with
      | none =>
        simp only [show (scopedContext base source sourceTypes).functions id = none from sourceFound,
          show (scopedContext base target targetTypes).functions id = none from targetFound]
        exact absentBody_congr held
          (resolveFunctionItemBody (scopedContext base source sourceTypes) id)
          (resolveFunctionItemBody (scopedContext base target targetTypes) id)
          (resolveFunctionItemBody_congr base source target headers sourceTypes targetTypes id)
          (missingBody_not_ok (scopedContext base source sourceTypes) id sourceFound) _ _
      | some targetFunction => rw [sourceFound, targetFound] at related; cases related
    | some sourceFunction =>
      cases targetFound : target id with
      | none => rw [sourceFound, targetFound] at related; cases related
      | some targetFunction =>
        rw [sourceFound, targetFound] at related
        cases related with
        | present _ _ body convention =>
          have framed := callFrameWith_eq_of_effectRelation
            (checkReturns base sourceFunction.body.returnTys true
              (match held with | .typedClosure _ _ _ => true | _ => false) "CallIndirect: ")
            (fun values => checkReturns_equivariant _ _ _ _ _ values)
            (sourceRecurse (calleeContext base source sourceFunction)
              depth sourceFunction.cfg sourceFunction.entryBlock callArgs strat)
            (targetRecurse (calleeContext base target targetFunction)
              depth targetFunction.cfg targetFunction.entryBlock callArgs strat)
            (effects id sourceFunction targetFunction sourceFound targetFound depth callArgs strat)
          simp only [show (scopedContext base source sourceTypes).functions id = some sourceFunction from sourceFound,
            show (scopedContext base target targetTypes).functions id = some targetFunction from targetFound,
            pure_bind, scopedContext_forFunction, checkReturns_scoped_function, ← body, framed,
            bindCallResults_congr base source target headers sourceTypes targetTypes
              (.CallIndirect calleeId sig args conv) dests _ types]

end TrustIr.GenericCoro.Prefix

#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.rawIndirectArguments == []
#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.rawIndirectArgumentsWith == []
#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.indirectAddress == []
