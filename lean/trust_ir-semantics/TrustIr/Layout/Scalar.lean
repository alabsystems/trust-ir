-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Bounds
import TrustIr.Layout.Extension

namespace TrustIr.SourceLayout

/-- The exact key used by the production scalar interner. It is not injective
on arbitrary summaries; the target-specific scalar image is essential. -/
def scalarKey (value : Summary) : Nat :=
  64 * value.size + (value.align.map Nat.succ).getD 0

/-- Every successful scalar layout has one of these exact metadata records.
The same pointer width is shared by all scalar queries in one source index. -/
inductive ScalarSummary (pointerBytes : Nat) : Summary → Prop where
  | plain (size : Nat)
      (allowed : size = 1 ∨ size = 2 ∨ size = 4 ∨ size = 8 ∨ size = 16 ∨ size = pointerBytes) :
      ScalarSummary pointerBytes { size, align := some size }
  | fat : ScalarSummary pointerBytes { size := 2 * pointerBytes, align := some pointerBytes }
  | unit : ScalarSummary pointerBytes { size := 0, align := some 1 }
  | never : ScalarSummary pointerBytes { size := 0, align := none }

/-- Scalar-key equality means equality of the entire scalar summary, including
its absent/default field and enumeration metadata. No target-validity assumption
or machine-word bound is needed, including for a zero pointer width. -/
theorem ScalarSummary.key_injective {pointerBytes : Nat} {left right : Summary}
    (leftScalar : ScalarSummary pointerBytes left) (rightScalar : ScalarSummary pointerBytes right)
    (same : scalarKey left = scalarKey right) : left = right := by
  cases leftScalar <;> cases rightScalar
  all_goals simp only [scalarKey, Option.map, Option.getD] at same
  case plain.plain size allowed other otherAllowed =>
    have equal : size = other := by omega
    cases equal
    rfl
  case plain.fat size allowed =>
    rcases allowed with h | h | h | h | h | h <;> subst size
    all_goals first
      | (exfalso; omega)
      | (have zero : pointerBytes = 0 := by omega
         simp only [zero, Nat.mul_zero])
  case fat.plain size allowed =>
    rcases allowed with h | h | h | h | h | h <;> subst size
    all_goals first
      | (exfalso; omega)
      | (have zero : pointerBytes = 0 := by omega
         simp only [zero, Nat.mul_zero])
  all_goals first | rfl | (exfalso; omega)

theorem ScalarSummary.of_finish {pointerBytes : Nat} {mode : Mode} {input value : Summary}
    (scalar : ScalarSummary pointerBytes input) (success : finish mode input = .ok value) :
    ScalarSummary pointerBytes value :=
  ((finish_ok_iff mode input value).mp success).1 ▸ scalar

/-- On either supported target every scalar fits both byte and bit carriers,
including a leaf first interned by an execution-mode request. -/
theorem ScalarSummary.finish_bounds (model : ByteModel) {value : Summary}
    (scalar : ScalarSummary model.pointerBytes value) (mode : Mode) : FinishBounds mode value := by
  cases scalar with
  | plain size allowed =>
    rcases allowed with h | h | h | h | h | h <;> subst size
    all_goals cases model <;> cases mode <;> decide
  | fat => cases model <;> cases mode <;> decide
  | unit => exact FinishBounds.unit mode
  | never => exact FinishBounds.never mode

/-- Every scalar leaf records the exact successful result and its key. `lower`
separates allocated scalar leaves from preparation's replaceable reserved slots. -/
def Graph.ScalarInvariant (lower pointerBytes : Nat) (graph : Graph) : Prop :=
  ∀ key node, graph.leaves.find key = some node →
    ∃ value, lower ≤ node ∧ ScalarSummary pointerBytes value ∧ scalarKey value = key ∧
      graph.nodes.find node = some (Equation.done (.ok value))

theorem Graph.ScalarInvariant.empty (lower pointerBytes count : Nat) :
    ({ count := count } : Graph).ScalarInvariant lower pointerBytes := by
  intro key node impossible
  cases impossible

/-- A key hit can be used at either mode without substituting another scalar's
byte geometry or metadata. This is stronger than knowing a cached node is bounded. -/
theorem Graph.ScalarInvariant.lookup {lower pointerBytes : Nat} {graph : Graph}
    (valid : graph.ScalarInvariant lower pointerBytes) {value : Summary}
    (scalar : ScalarSummary pointerBytes value) {node : Nat}
    (found : graph.leaves.find (scalarKey value) = some node) :
    lower ≤ node ∧ graph.nodes.find node = some (Equation.done (.ok value)) := by
  rcases valid _ _ found with ⟨original, inside, originalScalar, key, equation⟩
  have same := originalScalar.key_injective scalar key
  exact ⟨inside, same ▸ equation⟩

theorem Graph.ScalarInvariant.weaken {lower pointerBytes : Nat} {before after : Graph}
    (valid : before.ScalarInvariant lower pointerBytes) (extended : before.Extends after)
    (leaves : after.leaves = before.leaves) : after.ScalarInvariant lower pointerBytes := by
  intro key node found
  rw [leaves] at found
  rcases valid key node found with ⟨value, inside, scalar, keyed, equation⟩
  exact ⟨value, inside, scalar, keyed, extended _ _ equation⟩

/-- Replacing a reserved equation cannot change an allocated scalar leaf. -/
theorem Graph.ScalarInvariant.put {lower pointerBytes : Nat} {graph : Graph}
    (valid : graph.ScalarInvariant lower pointerBytes) (node : Nat) (reserved : node < lower)
    (equation : Equation) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).ScalarInvariant lower pointerBytes := by
  intro key leaf found
  rcases valid key leaf found with ⟨value, inside, scalar, keyed, original⟩
  refine ⟨value, inside, scalar, keyed, ?_⟩
  change (graph.nodes.insert node equation).find leaf = some (Equation.done (.ok value))
  rw [NatIndexTree.find_insert, if_neg (by omega : leaf ≠ node)]
  exact original

theorem Graph.ScalarInvariant.cache {lower pointerBytes : Nat} {graph : Graph}
    (valid : graph.ScalarInvariant lower pointerBytes) (node : Nat) (inside : lower ≤ node)
    (value : Summary) (scalar : ScalarSummary pointerBytes value)
    (equation : graph.nodes.find node = some (Equation.done (.ok value))) :
    ({ graph with leaves := graph.leaves.insert (scalarKey value) node } : Graph).ScalarInvariant lower pointerBytes := by
  intro key leaf found
  change (graph.leaves.insert (scalarKey value) node).find key = some leaf at found
  rw [NatIndexTree.find_insert] at found
  by_cases same : key = scalarKey value
  · rw [if_pos same] at found
    cases found
    exact ⟨value, inside, scalar, same.symm, equation⟩
  · rw [if_neg same] at found
    exact valid key leaf found

/-- A successful derivation at an interned scalar leaf returns that entire
summary, including when the solver obtained the derivation from its memo. -/
theorem Graph.ScalarInvariant.derivation_value {lower pointerBytes : Nat} {graph : Graph}
    (valid : graph.ScalarInvariant lower pointerBytes) {expected value : Summary}
    (scalar : ScalarSummary pointerBytes expected) {node : Nat}
    (found : graph.leaves.find (scalarKey expected) = some node)
    (derived : NodeDerivation graph node value) : value = expected := by
  have exactEquation := (valid.lookup scalar found).2
  cases derived with
  | equation actual initial steps finished =>
    rw [exactEquation] at actual
    cases actual
    cases steps
    exact (Except.ok.inj (initial.trans finished)).symm

end TrustIr.SourceLayout
