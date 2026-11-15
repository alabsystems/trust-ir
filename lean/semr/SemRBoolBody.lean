/- Copyright 2026 Andrew Yates. Apache-2.0.
   The conjunction leaf reads original SemR nodes and proves their original
   operational step. This is not Rust-reader soundness or source refinement. -/
import SemR

namespace SemR.BoolBody

/-- A structural reader over the canonical SemR node, not another evaluator. -/
def readAndNode (node : Node) : Option (Nat × Nat × Nat) :=
  match node with
  | ⟨.binop .bAnd .bool left right, [result]⟩ => some (left, right, result)
  | _ => none

theorem readAndNode_sound {node : Node} {left right result : Nat}
    (h : readAndNode node = some (left, right, result)) :
    node.inst = .binop .bAnd .bool left right ∧ node.results = [result] := by
  unfold readAndNode at h
  split at h <;> simp_all

/-- This is the existing operator's value-level semantics on every Bool input. -/
theorem eval_and (pointerBits : Nat) (left right : Bool) :
    evalBinop pointerBits .bAnd .bool (.bool left) (.bool right) =
      .ok (.bool (left && right)) := rfl

/-- The original operational step preserves the original state, advances its
    actual PC, and prepends the actual SSA result binding. No fresh state,
    environment, memory or lineage is synthesized by the theorem. -/
theorem readAndNode_step {node : Node} {left right result : Nat}
    (read : readAndNode node = some (left, right, result))
    (pointerBits : Nat) (state : Core) (a b : Bool)
    (hl : getV state left = .ok (.bool a))
    (hr : getV state right = .ok (.bool b)) :
    node.inst = .binop .bAnd .bool left right ∧
    binopStep pointerBits state node .bAnd .bool left right =
      .ok { next state with env := (result, .bool (a && b)) :: state.env } := by
  obtain ⟨inst, results⟩ := readAndNode_sound read
  refine ⟨inst, ?_⟩
  simp only [binopStep, hl, ok_bind, hr, eval_and]
  simp [bindResults, results, next]

/-- A wrong implementation node cannot borrow the conjunction reader. -/
theorem or_mutant_refused (left right result : Nat) :
    readAndNode ⟨.binop .bOr .bool left right, [result]⟩ = none := rfl

theorem missing_result_refused (left right : Nat) :
    readAndNode ⟨.binop .bAnd .bool left right, []⟩ = none := rfl

theorem extra_result_refused (left right a b : Nat) :
    readAndNode ⟨.binop .bAnd .bool left right, [a, b]⟩ = none := rfl

/-- The original universal proof can be rechecked against this positive goal. -/
def AndGoal : Prop := ∀ (pointerBits : Nat) (left right : Bool),
  evalBinop pointerBits .bAnd .bool (.bool left) (.bool right) =
    .ok (.bool (left && right))

/-- The original universal proof must not transfer to this false goal. -/
def OrInsteadOfAnd : Prop := ∀ (pointerBits : Nat) (left right : Bool),
  evalBinop pointerBits .bAnd .bool (.bool left) (.bool right) =
    .ok (.bool (left || right))

theorem or_counterexample : ¬ OrInsteadOfAnd := by
  intro wrong
  have impossible := wrong 64 true false
  cases impossible

end SemR.BoolBody
