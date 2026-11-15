-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutBounds

namespace TrustIr.SourceLayout

/-- A finite node derivation necessarily names an equation in the exact graph. -/
theorem NodeDerivation.present {graph : Graph} {node : Nat} {value : Summary}
    (derived : NodeDerivation graph node value) : (graph.nodes.find node).isSome = true := by
  cases derived with
  | equation found initial steps finished => rw [found]; rfl

/-- A completed leaf is justified by its actual result, not merely its name. -/
theorem NodeDerivation.done_result {graph : Graph} {node : Nat} {value : Summary}
    {result : Except Error Summary}
    (found : graph.nodes.find node = some (.done result))
    (derived : NodeDerivation graph node value) : result = .ok value := by
  cases derived with
  | equation lookup initial steps finished =>
    rw [found] at lookup
    cases lookup
    cases steps
    exact initial.trans finished

/-- Connect the production overflow guard to the actual graph solver at a
    guarded leaf. The fresh-query proof discharges all cache requirements. -/
theorem Graph.query_finished_bounds (graph : Graph) (node : Nat) (mode : Mode)
    (input output : Summary)
    (found : graph.nodes.find node = some (.done (finish mode input)))
    (run : graph.query node = .ok output) : output = input ∧ FinishBounds mode input := by
  exact (finish_ok_iff mode input output).mp
    ((graph.query_derivation node output run).done_result found)

namespace DerivationControls

private def absent : Graph := {}
private def payload : Summary := { size := 7, align := some 1 }
private def forged : Memo := NatIndexTree.empty.insert 0 payload

/-- The implementation really can return a caller-supplied cached value even
    when no equation exists. Cache validity must therefore be explicit. -/
theorem forged_cache_is_returned :
    solve absent .empty 0 forged = .ok (payload, forged) := by
  apply solve_cached
  rfl

/-- The returned cache value has no derivation in the empty graph. -/
theorem forged_cache_has_no_derivation : ¬ NodeDerivation absent 0 payload := by
  intro derived
  have present := derived.present
  cases present

/-- The memo premise is substantive: this concrete cache fails it. -/
theorem forged_cache_is_invalid : ¬ MemoDerivation absent forged := by
  intro valid
  exact forged_cache_has_no_derivation (valid 0 payload rfl)

/-- A fresh query cannot use that forged value: it refuses the missing root. -/
theorem fresh_missing_root_refuses :
    absent.query 0 = .error (.cycle 0) := rfl

end DerivationControls
end TrustIr.SourceLayout
