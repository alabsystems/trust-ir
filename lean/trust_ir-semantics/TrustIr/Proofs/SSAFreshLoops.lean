-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshStep

namespace TrustIr.SSAFreshLoops
open SSAFreshStep

/-- Every actual list iteration preserves freshness, including early exit,
    when its handler does so at each reachable list member and accumulator. -/
theorem forIn_fresh {α β : Type} (items : List α) (initial : β)
    (action : α → β → Sem (ForInStep β))
    (handlers : ∀ item ∈ items, ∀ accumulator, KeepsFresh (action item accumulator)) :
    KeepsFresh (forIn items initial action) := by
  trustIrCompilerProof {
    induction items generalizing initial with
    | nil => exact pure_fresh initial
    | cons item rest ih =>
      rw [List.forIn_cons]
      apply bind_fresh _ _ (handlers item ((trustIrListMemConsSelf _ _)) initial)
      intro step
      cases step with
      | done value => exact pure_fresh value
      | yield value => exact ih value (fun item member => handlers item (List.mem_cons_of_mem _ member))
  } {
    have loopFresh (remaining : List α) : ∀ (accumulator : β)
        (suffix : ∃ previous, previous ++ remaining = items),
        KeepsFresh (List.forIn'.loop items (fun item _ accumulator => action item accumulator)
          remaining accumulator suffix) := by
      induction remaining with
      | nil =>
        intro accumulator suffix
        exact pure_fresh accumulator
      | cons item rest ih =>
        intro accumulator suffix
        have member : item ∈ items := by
          obtain ⟨previous, same⟩ := suffix
          rw [← same]
          exact trustIrListMemAppendRight _ (trustIrListMemConsSelf _ _)
        apply bind_fresh _ _ (handlers item member accumulator)
        intro step
        cases step with
        | done value => exact pure_fresh value
        | yield value => exact ih value _
    exact loopFresh items initial ⟨[], rfl⟩
  }

end TrustIr.SSAFreshLoops

#trustIrAxiomsExact TrustIr.SSAFreshLoops.forIn_fresh == [propext]
