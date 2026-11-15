-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Graph

namespace TrustIr.SourceLayout

/-- Existing equations keep their exact contents when a graph is extended. -/
def Graph.Extends (before after : Graph) : Prop :=
  ∀ node equation, before.nodes.find node = some equation → after.nodes.find node = some equation

theorem Graph.Extends.refl (graph : Graph) : graph.Extends graph := fun _ _ found => found

theorem Graph.Extends.trans {first middle last : Graph}
    (left : first.Extends middle) (right : middle.Extends last) : first.Extends last :=
  fun node equation found => right node equation (left node equation found)

/-- Filling a previously empty reserved slot preserves every existing equation. -/
theorem Graph.Extends.insert_fresh (graph : Graph) (node : Nat) (equation : Equation)
    (absent : graph.nodes.find node = none) :
    graph.Extends { graph with nodes := graph.nodes.insert node equation } := by
  intro query original found
  by_cases same : query = node
  · subst query
    rw [absent] at found
    cases found
  · change (graph.nodes.insert node equation).find query = some original
    rw [NatIndexTree.find_insert,if_neg same]
    exact found

/-- A finite derivation survives exact preservation of all old equations. -/
theorem NodeDerivation.weaken {before after : Graph} (extended : before.Extends after)
    {node : Nat} {value : Summary} (derived : NodeDerivation before node value) :
    NodeDerivation after node value := by
  induction derived using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ => StepsDerivation after steps first last) with
  | equation found initial steps finished later =>
    exact .equation (extended _ _ found) initial later finished
  | nil state => exact .nil state
  | check updated later transferred => exact .check updated transferred
  | child solved updated later childTransferred restTransferred =>
    exact .child childTransferred updated restTransferred

theorem MemoDerivation.weaken {before after : Graph} {memo : Memo}
    (extended : before.Extends after) (valid : MemoDerivation before memo) :
    MemoDerivation after memo :=
  fun node value found => (valid node value found).weaken extended

/-- The next allocation index is outside the entire existing equation domain. -/
def Graph.Bounded (graph : Graph) : Prop :=
  ∀ node, graph.count ≤ node → graph.nodes.find node = none

theorem Graph.Bounded.empty (count : Nat) :
    ({ count := count } : Graph).Bounded := fun _ _ => rfl

theorem Graph.Bounded.allocate {graph : Graph} (bounded : graph.Bounded) (equation : Equation) :
    ({ graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } : Graph).Bounded := by
  intro node outside
  change graph.count + 1 ≤ node at outside
  change (graph.nodes.insert graph.count equation).find node = none
  rw [NatIndexTree.find_insert, if_neg (by omega : node ≠ graph.count)]
  exact bounded node (by omega)

theorem Graph.Extends.allocate {graph : Graph} (bounded : graph.Bounded) (equation : Equation) :
    graph.Extends { graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } := by
  intro node original found
  have different : node ≠ graph.count := by
    intro same
    subst node
    rw [bounded graph.count (Nat.le_refl _)] at found
    cases found
  change (graph.nodes.insert graph.count equation).find node = some original
  rw [NatIndexTree.find_insert, if_neg different]
  exact found

theorem Graph.Bounded.put {graph : Graph} (bounded : graph.Bounded) (node : Nat)
    (inside : node < graph.count) (equation : Equation) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).Bounded := by
  intro query outside
  change graph.count ≤ query at outside
  change (graph.nodes.insert node equation).find query = none
  rw [NatIndexTree.find_insert, if_neg (by omega : query ≠ node)]
  exact bounded query outside

/-- Query-time compilation preserves existing equations and the allocation
frontier. Preparation may replace reserved equations before any memo exists. -/
structure Graph.Growth (before after : Graph) : Prop where
  count_mono : before.count ≤ after.count
  bounded : after.Bounded
  equations : before.Extends after

theorem Graph.Growth.refl {graph : Graph} (bounded : graph.Bounded) : graph.Growth graph :=
  ⟨Nat.le_refl _, bounded, Graph.Extends.refl graph⟩

theorem Graph.Growth.trans {first middle last : Graph}
    (left : first.Growth middle) (right : middle.Growth last) : first.Growth last :=
  ⟨Nat.le_trans left.count_mono right.count_mono, right.bounded,
    left.equations.trans right.equations⟩

/-- A state action only extends a well-bounded equation graph. -/
def PreservesGraph {α : Type} (action : StateM Graph α) : Prop :=
  ∀ (graph : Graph), graph.Bounded → graph.Growth (action graph).2

theorem PreservesGraph.pure {α : Type} (value : α) :
    PreservesGraph (pure value : StateM Graph α) := fun _ bounded => .refl bounded

theorem PreservesGraph.get : PreservesGraph (get : StateM Graph Graph) :=
  fun _ bounded => .refl bounded

theorem PreservesGraph.bind {α β : Type} {action : StateM Graph α}
    {next : α → StateM Graph β} (first : PreservesGraph action)
    (later : ∀ value, PreservesGraph (next value)) : PreservesGraph (action >>= next) := by
  intro graph bounded
  have initial := first graph bounded
  exact initial.trans (later (action graph).1 (action graph).2 initial.bounded)

theorem PreservesGraph.leaves (update : NatIndexTree Nat → NatIndexTree Nat) :
    PreservesGraph (modify fun graph => { graph with leaves := update graph.leaves } : StateM Graph Unit) := by
  intro graph bounded
  exact ⟨Nat.le_refl _, bounded, fun _ _ found => found⟩

/-- A graph-state predicate is preserved by every result of a state action. -/
def PreservesState (invariant : Graph → Prop) {α : Type} (action : StateM Graph α) : Prop :=
  ∀ (graph : Graph), invariant graph → invariant (action graph).2

theorem PreservesState.run {invariant : Graph → Prop} {α : Type} {action : StateM Graph α}
    (preserved : PreservesState invariant action) (graph : Graph) (initial : invariant graph) :
    invariant (action graph).2 := preserved graph initial

theorem PreservesState.pure (invariant : Graph → Prop) {α : Type} (value : α) :
    PreservesState invariant (pure value : StateM Graph α) := fun _ initial => initial

theorem PreservesState.get (invariant : Graph → Prop) :
    PreservesState invariant (get : StateM Graph Graph) := fun _ initial => initial

theorem PreservesState.bind {invariant : Graph → Prop} {α β : Type}
    {action : StateM Graph α} {next : α → StateM Graph β}
    (first : PreservesState invariant action)
    (later : ∀ value, PreservesState invariant (next value)) :
    PreservesState invariant (action >>= next) :=
  fun graph initial => later (action graph).1 (action graph).2 (first graph initial)

theorem PreservesState.forIn {invariant : Graph → Prop} {α β : Type}
    (rows : List α) (initial : β) (body : α → β → StateM Graph (ForInStep β))
    (preserved : ∀ row, row ∈ rows → ∀ state, PreservesState invariant (body row state)) :
    PreservesState invariant (forIn rows initial body) := by
  induction rows generalizing initial with
  | nil => rw [List.forIn_nil]; exact PreservesState.pure invariant initial
  | cons first rest ih =>
    rw [List.forIn_cons]
    apply PreservesState.bind (preserved first ((trustIrListMemConsSelf _ _)) initial)
    intro step
    cases step with
    | done result => exact PreservesState.pure invariant result
    | yield next =>
      apply ih
      intro row member state
      exact preserved row (List.mem_cons_of_mem _ member) state

/-- Query-time growth also preserves any already-reserved prefix frontier. -/
theorem PreservesGraph.reserved {α : Type} {action : StateM Graph α}
    (preserved : PreservesGraph action) (reserved : Nat) :
    PreservesState (fun graph => graph.Bounded ∧ reserved ≤ graph.count) action := by
  intro graph initial
  have growth := preserved graph initial.1
  exact ⟨growth.bounded, Nat.le_trans initial.2 growth.count_mono⟩

end TrustIr.SourceLayout
