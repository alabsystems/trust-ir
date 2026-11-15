-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutRootFrontier

/- Enable kernel reduction through the imported mutual compiler equations.
The metadata is local to these proofs; no executable definition is replaced. -/
run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.SourceLayout

/-- Both cached and freshly compiled actual queries preserve an existing
reference-bound certificate. Source preparation is a separate obligation. -/
theorem Session.Reachable.query_reference_bounds {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (references : session.graph.ReferenceBounds)
    (mode : Mode) (ty : Ty) (value : Summary) (run : session.query mode ty = .ok (value,next)) :
    next.graph.ReferenceBounds := by
  obtain ⟨root,graph,reused,selected,_,graphSame,_,_⟩ :=
    Session.query_selection session mode ty value next history.invariant run
  rw [graphSame]
  cases selected with
  | cached hit => exact references
  | compiled graph compiled =>
    have frontier := history.invariant.1.2
    have scalars := history.scalar_invariant
    rw [history.index_eq] at compiled frontier scalars
    exact compiled.preserves_references history.invariant.1.1 frontier scalars references

theorem Session.QueryChain.reference_bounds {source : Environment} {first last : Session}
    (chain : Session.QueryChain first last) (history : Session.Reachable source first)
    (references : first.graph.ReferenceBounds) : last.graph.ReferenceBounds := by
  induction chain with
  | refl => exact references
  | queried chain mode ty value run ih =>
    exact (chain.reachable history).query_reference_bounds ih mode ty value run

namespace ReferenceControls
private def scalar : Summary := { size := 2, align := some 2 }
private def unitValue : Summary := { size := 0, align := some 1 }
private def unitEquation : Equation :=
  { kind := .unit, initial := .ok (), steps := [], finish := fun _ => .ok unitValue }
private def source : Environment := { types := [some .U16] }
private def preparedGraph : Graph :=
  { nodes := ((((NatIndexTree.empty.insert 4 (.done (.ok scalar))).insert 0 (.done (.ok scalar))).insert 1
      (.done (.ok scalar))).insert 2 unitEquation).insert 3 unitEquation,
    count := 5, leaves := NatIndexTree.empty.insert 131 4 }

theorem actual_prepared_graph : (prepare source).graph = preparedGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_prepared_references : (prepare source).graph.ReferenceBounds := by
  rw [actual_prepared_graph]
  exact (((((Graph.ReferenceBounds.empty 5).insert 5 (Nat.le_refl _) 4 (.done (.ok scalar)) True.intro).insert
    5 (Nat.le_refl _) 0 (.done (.ok scalar)) True.intro).insert
    5 (Nat.le_refl _) 1 (.done (.ok scalar)) True.intro).insert
    5 (Nat.le_refl _) 2 unitEquation True.intro).insert
    5 (Nat.le_refl _) 3 unitEquation True.intro

private def arrayValue : Summary := { size := 6, align := some 2 }
private def afterArray : Session :=
  (((prepare source).query .execution (.Array ⟨0⟩ 3)).toOption.getD (arrayValue,prepare source)).2

theorem actual_array_query_references : afterArray.graph.ReferenceBounds := by
  trustIrCompilerProof {
    exact (Session.Reachable.prepared (source := source)).query_reference_bounds actual_prepared_references
      .execution (.Array ⟨0⟩ 3) arrayValue (by rfl)
  } {
    exact (Session.Reachable.prepared (source := source)).query_reference_bounds actual_prepared_references
      .execution (.Array ⟨0⟩ 3) arrayValue (by trustIrReduce)
  }

theorem actual_cached_query_references :
    ∃ next, afterArray.query .execution (.Array ⟨0⟩ 3) = .ok (arrayValue,next) ∧ next.graph.ReferenceBounds := by
  trustIrCompilerProof {
    refine ⟨afterArray,by rfl,?_⟩
    have history : Session.Reachable source afterArray :=
      .queried (mode := .execution) (ty := .Array ⟨0⟩ 3) (value := arrayValue) .prepared (by rfl)
    exact history.query_reference_bounds actual_array_query_references .execution (.Array ⟨0⟩ 3) arrayValue (by rfl)
  } {
    refine ⟨afterArray,by trustIrReduce,?_⟩
    have history : Session.Reachable source afterArray :=
      .queried (mode := .execution) (ty := .Array ⟨0⟩ 3) (value := arrayValue) .prepared (by trustIrReduce)
    exact history.query_reference_bounds actual_array_query_references .execution (.Array ⟨0⟩ 3) arrayValue (by trustIrReduce)
  }

private def unitGraph : Graph := { count := 2 }
private def vectorGraph : Graph :=
  { nodes := ((NatIndexTree.empty.insert 2 (.done (.ok scalar))).insert 3
      (scaled .execution 2 2)).insert 4 (scaled .execution 3 3),
    count := 5, leaves := NatIndexTree.empty.insert 131 2 }

theorem actual_nested_vector_references : vectorGraph.ReferenceBounds := by
  trustIrCompilerProof {
    have compiled : RootCompilation (Index.ofEnvironment {}) .execution
        (.Vector 3 (.Vector 2 .U16)) unitGraph 4 vectorGraph := rfl
    exact compiled.preserves_references (Graph.Bounded.empty 2) (by decide)
      (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)
  } {
    have compiled : RootCompilation (Index.ofEnvironment {}) .execution
        (.Vector 3 (.Vector 2 .U16)) unitGraph 4 vectorGraph := by trustIrReduce
    exact compiled.preserves_references (Graph.Bounded.empty 2) (by decide)
      (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)
  }

private def fields : List FieldDef :=
  [{ name := "wide", ty := .U16, offset := none },{ name := "byte", ty := .U8, offset := none }]
private def definition : StructDef := { id := ⟨7⟩, name := "Pair", fields, size := none, align := none }
private def fieldGraph : Graph :=
  { nodes := (NatIndexTree.empty.insert 2 (.done (.ok scalar))).insert 3
      (.done (.ok { size := 1, align := some 1 })), count := 4,
    leaves := (NatIndexTree.empty.insert 131 2).insert 66 3 }
private def fieldEquation : Equation := canonicalFields .execution "struct" 7 [(.U16,2),(.U8,3)]

theorem actual_struct_construction :
    StructCompilation (Index.ofEnvironment {}) .execution definition unitGraph fieldEquation fieldGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_struct_references : fieldGraph.ReferenceBounds ∧ StepsIn (fun child => child < 4) fieldEquation.steps :=
  actual_struct_construction.references (Graph.Bounded.empty 2) (by decide)
    (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)

private def closure : ClosureTy := { ClosureTy.bare ⟨0⟩ with captures := [.U16] }
private def closureSource : Environment :=
  { closures := [closure], hasTargetInfo := true,
    closureLayouts := [{ closure := ⟨0⟩, size := 2, align := 2, captureOffsets := [0] }] }
private def closureBefore : Graph := { count := 4 }
private def closureAfter : Graph :=
  { nodes := NatIndexTree.empty.insert 4 (.done (.ok scalar)), count := 5, leaves := NatIndexTree.empty.insert 131 4 }
private def closureEquation : Equation := declaredFields .shape "closure" 0 2 2 word64Max false [(.U16,some 0,4)]

theorem actual_closure_construction :
    ClosureCompilation (Index.ofEnvironment closureSource) 0 closure closureBefore closureEquation closureAfter := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_closure_references : closureAfter.ReferenceBounds ∧ StepsIn (fun child => child < 5) closureEquation.steps :=
  actual_closure_construction.references (Graph.Bounded.empty 4) (by decide)
    (Graph.ScalarInvariant.empty 4 8 4) (Graph.ReferenceBounds.empty 4)

private def outside : Graph := { nodes := NatIndexTree.empty.insert 0 (.alias 100), count := 1 }

theorem complete_does_not_bound_references : outside.Complete := by
  intro node inside
  have same : node = 0 := by change node < 1 at inside; omega
  subst node
  exact ⟨.alias 100,rfl⟩

theorem outside_reference_is_rejected : ¬ outside.ReferenceBounds := by
  intro valid
  have bound := valid 0 (.alias 100) rfl
  have impossible : ¬ (100 < 1) := by decide
  exact impossible bound.1

theorem bounds_do_not_install_equations : ({ count := 1 } : Graph).ReferenceBounds :=
  Graph.ReferenceBounds.empty 1

theorem empty_reserved_prefix_is_incomplete : ¬ ({ count := 1 } : Graph).Complete := by
  intro complete
  obtain ⟨equation,found⟩ := complete 0 (by decide)
  cases found

private def cyclic : Graph := { nodes := (NatIndexTree.empty.insert 0 (.alias 1)).insert 1 (.alias 0), count := 2 }

theorem cycle_references_bounded : cyclic.ReferenceBounds :=
  ((Graph.ReferenceBounds.empty 2).insert 2 (Nat.le_refl _) 0 (.alias 1) ⟨by decide,True.intro⟩).insert
    2 (Nat.le_refl _) 1 (.alias 0) ⟨by decide,True.intro⟩

theorem cycle_prefix_complete : cyclic.Complete := by
  intro node inside
  have choices : node = 0 ∨ node = 1 := by change node < 2 at inside; omega
  rcases choices with rfl | rfl
  · exact ⟨.alias 1,rfl⟩
  · exact ⟨.alias 0,rfl⟩

theorem cycle_closed_without_termination : cyclic.ClosedRegion (fun node => node < 2) ∧ cyclic.query 0 = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact ⟨Graph.closed_prefix cycle_references_bounded cycle_prefix_complete,rfl⟩
  } {
    exact ⟨Graph.closed_prefix cycle_references_bounded cycle_prefix_complete,(by trustIrReduce)⟩
  }

end ReferenceControls
end TrustIr.SourceLayout
