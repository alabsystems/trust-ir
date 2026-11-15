-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCalls
import TrustIr.Proofs.GenericCoroInvoke

namespace TrustIr.GenericCoro.Prefix

/-- Invoke uses a real saved caller frame and a cleared callee frame. Both
    normal and caught-unwind continuations run after exact restoration. -/
def invokeFrameWith {α : Type} (strategy : PanicStrategy)
    (check : List Value → Sem Unit) (callee : Sem (List Value))
    (normal : List Value → Sem α) (unwind : Addr → Sem α) : Sem α := do
  let caller ← Sem.getState
  Sem.setState (callerWorld caller)
  finishInvokeWith strategy check (saveFrame caller none) callee normal unwind

/-- Equal complete callee errors and equal returned values/non-SSA worlds
    suffice at an arbitrary caller frame. The caller need not be Fresh. -/
theorem invokeFrameWith_eq_of_effectRelation {α : Type} (strategy : PanicStrategy)
    (check : List Value → Sem Unit)
    (equivariant : ∀ values, HeldMemoryFrames.Equivariant (check values))
    (source target : Sem (List Value))
    (normal : List Value → Sem α) (unwind : Addr → Sem α)
    (related : ∀ world, EffectRelation
      (Sem.run source (callerWorld world)) (Sem.run target (callerWorld world))) :
    invokeFrameWith strategy check source normal unwind =
      invokeFrameWith strategy check target normal unwind := by
  funext world
  exact finishInvokeWith_eq_of_effectRelation strategy check equivariant
    (saveFrame world none) source target normal unwind
    (callerWorld world) (callerWorld world) (related world)

/-- Continuation normalization of the actual Invoke return protocol. Invoke
    checks arity and poison, with no typed-closure return loop. The callee
    and invokeCatch stay opaque; only the selected return-check match opens. -/
theorem invokeFrameWith_checkReturns_bind {α β : Type} (strategy : PanicStrategy)
    (ctx : EvalContext) (returnTys : List Ty) (message : String)
    (callee : Sem (List Value)) (normal : List Value → Sem α) (unwind : Addr → Sem α)
    (next : α → Sem β) :
    (invokeFrameWith strategy (checkReturns ctx returnTys true false message)
      callee normal unwind >>= next) = (do
      let caller ← Sem.getState
      Sem.setState (callerWorld caller)
      let outcome ← invokeCatch strategy callee
      match outcome with
      | .inl values =>
        match checkReturnArity values returnTys with
        | .ok () => pure ()
        | .error error => Sem.throwTypeError (message ++ error)
        Sem.rejectPoisonValues values "Call returns"
        let state ← Sem.getState
        Sem.setState (restoreFrame state (saveFrame caller none) [])
        normal values >>= next
      | .inr (exception, state) =>
        Sem.setState (restoreFrame state (saveFrame caller none) [])
        unwind exception >>= next) := by
  simp only [invokeFrameWith, finishInvokeWith, bind_assoc]
  apply bind_same
  intro caller
  apply bind_same
  intro _
  apply bind_same
  intro outcome
  cases outcome with
  | inl values =>
    cases arity : checkReturnArity values returnTys with
    | error error =>
      simp only [finishInvokeReturnWith, checkReturns, arity, Bool.true_eq,
        Bool.false_eq_true, if_true, if_false, bind_assoc, pure_bind]
    | ok unit =>
      cases unit
      simp only [finishInvokeReturnWith, checkReturns, arity, Bool.true_eq,
        Bool.false_eq_true, if_true, if_false, bind_assoc, pure_bind]
  | inr pair => cases pair; rfl

/-- The same normalization without an additional outer continuation. -/
theorem invokeFrameWith_checkReturns {α : Type} (strategy : PanicStrategy)
    (ctx : EvalContext) (returnTys : List Ty) (message : String)
    (callee : Sem (List Value)) (normal : List Value → Sem α) (unwind : Addr → Sem α) :
    invokeFrameWith strategy (checkReturns ctx returnTys true false message)
      callee normal unwind = (do
      let caller ← Sem.getState
      Sem.setState (callerWorld caller)
      let outcome ← invokeCatch strategy callee
      match outcome with
      | .inl values =>
        match checkReturnArity values returnTys with
        | .ok () => pure ()
        | .error error => Sem.throwTypeError (message ++ error)
        Sem.rejectPoisonValues values "Call returns"
        let state ← Sem.getState
        Sem.setState (restoreFrame state (saveFrame caller none) [])
        normal values
      | .inr (exception, state) =>
        Sem.setState (restoreFrame state (saveFrame caller none) [])
        unwind exception) := by
  simpa only [bind_pure] using
    invokeFrameWith_checkReturns_bind strategy ctx returnTys message callee normal unwind pure

end TrustIr.GenericCoro.Prefix

#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.invokeFrameWith == []
#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.invokeFrameWith_eq_of_effectRelation == [Quot.sound]
