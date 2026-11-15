-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutEquationBounds
import TrustIr.Layout.Enums

namespace TrustIr.SourceLayout

theorem Equation.Executes.finalizes {graph : Graph} {equation : Equation}
    {value : Summary} {property : Summary → Prop}
    (run : equation.Executes graph value) (safe : equation.Finalizes property) :
    property value := by
  rcases run with ⟨first, last, _initial, _steps, finished⟩
  exact safe last value finished

/-- Successful enum execution rules out the refusal equation and bounds the
actual final result for every canonical and producer-authored encoding. -/
theorem Equation.Executes.enum_bounds {graph : Graph} {value : Summary}
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (variants : List Nat)
    (run : (enumEquation mode definition uninhabited variants).Executes graph value) :
    FinishBounds mode value := by
  rcases run with ⟨first, last, initial, _steps, finished⟩
  apply enumEquation_finish_property mode definition uninhabited variants
    (FinishBounds mode) _ last value finished ⟨first, initial⟩
  intro input output success
  have bounded := (finish_ok_iff mode input output).mp success
  exact bounded.1 ▸ bounded.2

/-- The prefix may validate unrelated source declarations, but the returned
summary still comes from the guarded body. -/
theorem Equation.Executes.sequence_finalizes {graph : Graph} {children : List Nat}
    {next : Equation} {value : Summary} {property : Summary → Prop}
    (run : (Equation.sequence children next).Executes graph value)
    (safe : next.Finalizes property) : property value :=
  run.sequence_body.finalizes safe

theorem Graph.query_alias_derivation (graph : Graph) (node child : Nat) (value : Summary)
    (found : graph.nodes.find node = some (Equation.alias child))
    (run : graph.query node = .ok value) : NodeDerivation graph child value :=
  ((graph.query_derivation node value run).execution found).alias_child

theorem Graph.query_enum_bounds (graph : Graph) (node : Nat) (mode : Mode)
    (definition : EnumDef) (uninhabited : List Bool) (variants : List Nat) (value : Summary)
    (found : graph.nodes.find node = some (enumEquation mode definition uninhabited variants))
    (run : graph.query node = .ok value) : FinishBounds mode value :=
  ((graph.query_derivation node value run).execution found).enum_bounds mode definition uninhabited variants

theorem Graph.query_sequence_body (graph : Graph) (node : Nat) (children : List Nat)
    (next : Equation) (value : Summary)
    (found : graph.nodes.find node = some (Equation.sequence children next))
    (run : graph.query node = .ok value) : next.Executes graph value :=
  ((graph.query_derivation node value run).execution found).sequence_body

/-- In particular, sequencing also preserves scaled bounds, whose guard is
inside the child update and cannot be justified by finalizer-only reasoning. -/
theorem Graph.query_sequence_scaled_bounds (graph : Graph) (node : Nat)
    (children : List Nat) (mode : Mode) (count child : Nat) (value : Summary)
    (found : graph.nodes.find node = some (Equation.sequence children (scaled mode count child)))
    (run : graph.query node = .ok value) : FinishBounds mode value :=
  (graph.query_sequence_body node children _ value found run).scaled_bounds mode count child

namespace CombinatorControls

private def payload : Summary := { size := 7, align := some 1 }
private def prefixRefusal : Graph :=
  { nodes := NatIndexTree.empty.insert 0 (.done (.error .sizeOverflow)) |>.insert 1
      (Equation.sequence [0] (.done (.ok payload))), count := 2 }
private def bodyRefusal : Graph :=
  { nodes := NatIndexTree.empty.insert 0 (.done (.ok payload)) |>.insert 1
      (Equation.sequence [0] (.done (.error .sizeOverflow))), count := 2 }
private def aliasGraph : Graph :=
  { nodes := NatIndexTree.empty.insert 0 (.done (.ok payload)) |>.insert 1
      (Equation.alias 0), count := 2 }

/-- A successful body cannot bypass an earlier prefix refusal. -/
theorem prefix_refusal : prefixRefusal.query 1 = .error .sizeOverflow := by trustIrReduce

/-- A successful prefix cannot mask a refused body. -/
theorem body_refusal : bodyRefusal.query 1 = .error .sizeOverflow := by trustIrReduce

theorem alias_exact : aliasGraph.query 1 = .ok payload := by trustIrReduce

theorem alias_child_derived : NodeDerivation aliasGraph 0 payload :=
  aliasGraph.query_alias_derivation 1 0 payload (by trustIrReduce) alias_exact

private def emptyEnum : EnumDef := { id := ⟨0⟩, name := "Empty", variants := [] }

/-- A refused enum's identity finalizer accepts an arbitrary state when
viewed alone. This is why the enum law also requires successful initialization. -/
theorem refused_enum_finalizer (state : Summary) :
    (enumEquation .execution emptyEnum [] []).finish state = .ok state := rfl

theorem refused_enum_cannot_execute (value : Summary) :
    ¬ (enumEquation .execution emptyEnum [] []).Executes aliasGraph value := by
  rintro ⟨first, last, impossible, steps, finished⟩
  cases impossible

end CombinatorControls
end TrustIr.SourceLayout
