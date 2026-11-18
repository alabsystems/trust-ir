-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Monad

namespace TrustIr

theorem sr_throw {α : Type} (e : SemError) (s : MachineState) :
    StateT.run (throw e : Sem α) s = .error e := rfl

theorem sr_bind {α β : Type} (m : Sem α) (f : α → Sem β) (s : MachineState) :
    StateT.run (m >>= f) s
      = (StateT.run m s).bind (fun p => StateT.run (f p.1) p.2) := rfl

theorem sr_lookup (id : ValueId) (s : MachineState) :
    StateT.run (Sem.lookupValue id) s
      = match s.lookupValue id with
        | some v => .ok (v, s)
        | none => .error (.typeError s!"undefined SSA value: {repr id}") := by
  trustIrCompilerProof {
  unfold Sem.lookupValue
  cases h : s.lookupValue id <;>
    simp [h, Sem.getState, Sem.throwTypeError, bind, StateT.bind, StateT.get,
      StateT.run, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, Except.bind,
      Except.pure, StateT.lift]
  } {
  unfold Sem.lookupValue
  cases h : s.lookupValue id <;>
    simp [h, Sem.getState, Sem.throwTypeError, bind, StateT.bind, StateT.get,
      StateT.run, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, Except.bind,
      Except.pure, StateT.lift] <;> rfl
  }

end TrustIr
