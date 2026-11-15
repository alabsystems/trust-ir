-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.EnumGeometry
import TrustIr.Layout.Scalar

namespace TrustIr.SourceLayout

/-- Direct fields and each mutually exclusive enum row have valid storage. -/
def StorageGeometry (value : Summary) : Prop := FieldGeometry value ∧ EnumerationGeometry value

/-- Only dynamically allocated equations must survive a preparation write.
Reserved nominal slots may still be filled or replaced. -/
def Graph.DynamicExtends (lower : Nat) (before after : Graph) : Prop :=
  ∀ node equation, lower ≤ node → before.nodes.find node = some equation →
    after.nodes.find node = some equation

theorem Graph.DynamicExtends.refl (lower : Nat) (graph : Graph) : graph.DynamicExtends lower graph :=
  fun _ _ _ found => found

theorem Graph.DynamicExtends.trans {lower : Nat} {first middle last : Graph}
    (left : first.DynamicExtends lower middle) (right : middle.DynamicExtends lower last) :
    first.DynamicExtends lower last := fun node equation inside found =>
  right node equation inside (left node equation inside found)

theorem Graph.Extends.dynamic {before after : Graph} (extended : before.Extends after) (lower : Nat) :
    before.DynamicExtends lower after := fun node equation _ found => extended node equation found

theorem Graph.DynamicExtends.put_below (graph : Graph) (lower node : Nat) (inside : node < lower)
    (equation : Equation) :
    graph.DynamicExtends lower { graph with nodes := graph.nodes.insert node equation } := by
  intro child original outside found
  change (graph.nodes.insert node equation).find child = some original
  rw [NatIndexTree.find_insert, if_neg (by omega)]
  exact found

/-- A rule remains valid after any changes to reserved slots and any growth
that keeps the existing dynamic equations. Its witnesses are logical only. -/
def Equation.StorageRule (lower : Nat) (graph : Graph) (equation : Equation) : Prop :=
  ∀ after, graph.DynamicExtends lower after →
    equation.ContextualRule after (fun _ value => StorageGeometry value) 0

def Graph.StorageInvariant (lower : Nat) (graph : Graph) : Prop :=
  ∀ node equation, graph.nodes.find node = some equation → equation.StorageRule lower graph

theorem Equation.StorageRule.weaken {lower : Nat} {before after : Graph} {equation : Equation}
    (safe : equation.StorageRule lower before) (extended : before.DynamicExtends lower after) :
    equation.StorageRule lower after :=
  fun next growth => safe next (extended.trans growth)

theorem Graph.StorageInvariant.contextual {lower : Nat} {graph : Graph}
    (safe : graph.StorageInvariant lower) : graph.ContextualInvariant (fun _ value => StorageGeometry value) := by
  intro node equation found
  exact ((safe node equation found) graph (Graph.DynamicExtends.refl lower graph)).reowner (fun _ good => good)

theorem Graph.StorageInvariant.empty (lower count : Nat) :
    ({ count } : Graph).StorageInvariant lower := by
  intro node equation impossible
  cases impossible

theorem Graph.StorageInvariant.insert {lower : Nat} {graph : Graph}
    (safe : graph.StorageInvariant lower) (node : Nat) (equation : Equation)
    (extended : graph.DynamicExtends lower { graph with nodes := graph.nodes.insert node equation })
    (guarded : equation.StorageRule lower graph) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).StorageInvariant lower := by
  intro child original found
  change (graph.nodes.insert node equation).find child = some original at found
  rw [NatIndexTree.find_insert] at found
  by_cases same : child = node
  · rw [if_pos same] at found
    cases found
    exact guarded.weaken extended
  · rw [if_neg same] at found
    exact (safe child original found).weaken extended

theorem Graph.StorageInvariant.allocate {lower : Nat} {graph : Graph}
    (safe : graph.StorageInvariant lower) (bounded : graph.Bounded) (equation : Equation)
    (guarded : equation.StorageRule lower graph) :
    ({ graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } : Graph).StorageInvariant lower := by
  have extension := (Graph.Extends.allocate bounded equation).dynamic lower
  have inserted := safe.insert graph.count equation extension guarded
  exact inserted

theorem Graph.StorageInvariant.put_below {lower : Nat} {graph : Graph}
    (safe : graph.StorageInvariant lower) (node : Nat) (inside : node < lower) (equation : Equation)
    (guarded : equation.StorageRule lower graph) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).StorageInvariant lower :=
  safe.insert node equation (Graph.DynamicExtends.put_below graph lower node inside equation) guarded

theorem Graph.StorageInvariant.leaves {lower : Nat} {graph : Graph}
    (safe : graph.StorageInvariant lower) (leaves : NatIndexTree Nat) :
    ({ graph with leaves } : Graph).StorageInvariant lower := by
  intro node equation found
  exact (safe node equation found).weaken (fun _ _ _ old => old)

/-- Equations whose own execution validates all storage need no child oracle. -/
def Equation.StorageGuarded (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → StorageGeometry value

theorem Equation.StorageGuarded.rule {equation : Equation} (safe : equation.StorageGuarded)
    (lower : Nat) (graph : Graph) : equation.StorageRule lower graph := by
  intro after extended first last value initial steps finished
  exact safe after value ⟨first, last, initial, steps.derivation, finished⟩

theorem StorageGeometry.empty_fields {value : Summary}
    (fields : value.fields = []) (enumeration : value.enumeration = none) : StorageGeometry value := by
  refine ⟨?_, ?_⟩
  · constructor
    · rw [fields]; trivial
    · rw [fields]; intro field impossible; cases impossible
  · intro actual impossible
    rw [enumeration] at impossible
    cases impossible

theorem ScalarSummary.storage_geometry {pointerBytes : Nat} {value : Summary}
    (scalar : ScalarSummary pointerBytes value) : StorageGeometry value := by
  cases scalar <;> exact StorageGeometry.empty_fields rfl rfl

theorem Equation.StorageGuarded.done (result : Except Error Summary)
    (safe : ∀ value, result = .ok value → StorageGeometry value) :
    (Equation.done result).StorageGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.StorageGuarded.failed (error : Error) : (Equation.done (.error error)).StorageGuarded :=
  Equation.StorageGuarded.done _ (by intro value impossible; cases impossible)

theorem Equation.StorageGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).StorageGuarded := by
  intro graph value run
  have geometry := run.canonicalFields_geometry mode kind id fields
  rcases run with ⟨first, last, initial, steps, finished⟩
  dsimp only [TrustIr.SourceLayout.canonicalFields] at finished
  cases aligned : alignUp last.cursor last.align with
  | error error => simp [aligned, Bind.bind, Except.bind] at finished
  | ok size =>
    simp only [aligned, Bind.bind, Except.bind] at finished
    have same := (finish_ok_iff mode _ value).mp finished
    refine ⟨geometry, ?_⟩
    rw [same.1]
    intro actual impossible
    cases impossible

theorem Equation.StorageGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).StorageGuarded := by
  intro graph value run
  have geometry := run.declaredFields_geometry mode kind id size align clamp transparent fields
  rcases run with ⟨first, last, initial, steps, finished⟩
  have same := declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished
  refine ⟨geometry, ?_⟩
  rw [same]
  intro actual impossible
  cases impossible

theorem Equation.StorageGuarded.scaled (mode : Mode) (count child : Nat) :
    (scaled mode count child).StorageGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps with
  | child solved updated later =>
    cases later
    cases finished
    dsimp only [scaled] at updated
    simp only [Except.bind, Bind.bind] at updated
    split at updated
    · cases updated
    · have same := (finish_ok_iff mode _ value).mp updated
      rw [same.1]
      exact StorageGeometry.empty_fields rfl rfl

theorem Equation.StorageGuarded.sequence (children : List Nat) {next : Equation}
    (safe : next.StorageGuarded) : (Equation.sequence children next).StorageGuarded :=
  fun graph value run => safe graph value run.sequence_body

theorem Equation.StorageGuarded.unit (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps, finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).StorageGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases finished
  exact StorageGeometry.empty_fields rfl rfl

theorem Equation.StorageRule.alias (lower : Nat) (graph : Graph) (child : Nat) :
    (Equation.alias child).StorageRule lower graph :=
  fun after extended => Equation.ContextualRule.alias after 0 child (fun _ safe => safe)

theorem Equation.StorageRule.canonicalEnum (lower : Nat) (graph : Graph)
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (canonical : definition.layout = none) :
    (enumEquation mode definition uninhabited nodes).StorageRule lower graph :=
  fun after extended => Equation.ContextualRule.canonicalEnum_geometry after 0 mode definition uninhabited nodes canonical

theorem Equation.StorageRule.descriptorEnum (lower : Nat) (graph : Graph)
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (children : graph.ParentFieldCertificates descriptor.size nodes)
    (outside : ∀ child, child ∈ nodes → lower ≤ child) :
    (enumEquation mode definition uninhabited nodes).StorageRule lower graph := by
  intro after extended
  apply Equation.ContextualRule.descriptorEnum_geometry after 0 mode definition uninhabited nodes descriptor authored
  intro child member
  rcases children child member with ⟨equation, found, guarded⟩
  exact ⟨equation, extended child equation (outside child member) found, guarded⟩

theorem Graph.query_storage_geometry {lower : Nat} (graph : Graph) (safe : graph.StorageInvariant lower)
    (node : Nat) (value : Summary) (run : graph.query node = .ok value) : StorageGeometry value :=
  graph.query_satisfies_contextual safe.contextual node value run

end TrustIr.SourceLayout
