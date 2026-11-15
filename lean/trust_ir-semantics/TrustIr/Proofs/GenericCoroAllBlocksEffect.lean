-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixEntryEffect

namespace TrustIr.GenericCoro.AllBlocksEffect

/-- Compose identical actual preludes with paired continuations. Prelude
    errors are retained exactly; successful intermediate freshness is derived
    from the prelude's preservation law rather than assumed as an outcome. -/
theorem bind_effect {α : Type} (first : Sem α)
    (source target : α → Sem (List Value))
    (firstFresh : SSAFreshStep.KeepsFresh first)
    (tails : ∀ value state, SSAFreshFrames.FreshState state →
      EffectRelation (Sem.run (source value) state) (Sem.run (target value) state))
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation (Sem.run (first >>= source) state) (Sem.run (first >>= target) state) := by
  simp only [Sem.run_bind]
  cases ran : Sem.run first state with
  | error error => exact .error error
  | ok result =>
    exact tails result.1 result.2 (firstFresh state result fresh ran)

end TrustIr.GenericCoro.AllBlocksEffect
