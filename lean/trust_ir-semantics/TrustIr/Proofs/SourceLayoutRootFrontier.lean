-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutClosedRegions

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

/-- Any typed compilation from a real session returns an in-range root, even
before the solver accepts or refuses its equation. -/
theorem Session.Reachable.compiled_root_bound {source : Environment} {session : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (root : Nat) (after : Graph)
    (compiled : RootCompilation session.index mode ty session.graph root after) : root < after.count := by
  have frontier := history.invariant.1.2
  have scalars := history.scalar_invariant
  rw [history.index_eq] at compiled frontier scalars
  exact compiled.root_bound history.invariant.1.1 frontier scalars

theorem Session.Reachable.compiled_types_bounds {source : Environment} {session : Session}
    (history : Session.Reachable source session) (mode : Mode) (types : List Ty) (roots : List Nat) (after : Graph)
    (compiled : TypesCompilation session.index mode types session.graph roots after) :
    ∀ root ∈ roots, root < after.count := by
  have frontier := history.invariant.1.2
  have scalars := history.scalar_invariant
  rw [history.index_eq] at compiled frontier scalars
  exact compiled.roots_bound history.invariant.1.1 frontier scalars

namespace RootFrontierControls
private def unitGraph : Graph := { count := 2 }
private def scalar : Summary := { size := 2, align := some 2 }
private def allocated : Graph :=
  { nodes := NatIndexTree.empty.insert 2 (.done (.ok scalar)), count := 3,
    leaves := NatIndexTree.empty.insert 131 2 }
private def vectorGraph : Graph :=
  { allocated with nodes := (allocated.nodes.insert 3 (scaled .execution 2 2)).insert 4 (scaled .execution 3 3), count := 5 }

theorem actual_nested_vector_compilation :
    RootCompilation (Index.ofEnvironment {}) .execution (.Vector 3 (.Vector 2 .U16)) unitGraph 4 vectorGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_nested_vector_root_bound : 4 < vectorGraph.count :=
  actual_nested_vector_compilation.root_bound (Graph.Bounded.empty 2) (by decide) (Graph.ScalarInvariant.empty 2 8 2)

theorem actual_repeated_children :
    TypesCompilation (Index.ofEnvironment {}) .execution [.U16,.U16] unitGraph [2,2] allocated := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_repeated_children_bounded : ∀ root ∈ [2,2], root < allocated.count :=
  actual_repeated_children.roots_bound (Graph.Bounded.empty 2) (by decide) (Graph.ScalarInvariant.empty 2 8 2)

private def scalarSource : Environment := { types := [some .U16] }

theorem actual_scalar_cache_hit :
    RootCompilation (Index.ofEnvironment scalarSource) .execution .U16
      (prepare scalarSource).graph 4 (prepare scalarSource).graph := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_cached_root_bound : 4 < (prepare scalarSource).graph.count :=
  Session.Reachable.compiled_root_bound (source := scalarSource) .prepared .execution .U16 4 _ actual_scalar_cache_hit

private def nominal (name : String) : StructDef :=
  { id := ⟨1⟩, name, fields := [], size := none, align := none }
private def nominalSource : Environment := { structs := [nominal "first",nominal "matching-position"] }
private def nominalGraph : Graph := { count := 6 }

/-- Matching-position execution lookup and first-definition shape lookup must
not be conflated, including duplicates in unvalidated source tables. -/
theorem actual_nominal_execution_root :
    RootCompilation (Index.ofEnvironment nominalSource) .execution (.Struct ⟨1⟩) nominalGraph 3 nominalGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_nominal_shape_root :
    RootCompilation (Index.ofEnvironment nominalSource) .shape (.Struct ⟨1⟩) nominalGraph 0 nominalGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_nominal_both_bounded : 3 < nominalGraph.count ∧ 0 < nominalGraph.count :=
  ⟨actual_nominal_execution_root.root_bound (Graph.Bounded.empty 6) (by decide) (Graph.ScalarInvariant.empty 6 8 6),
   actual_nominal_shape_root.root_bound (Graph.Bounded.empty 6) (by decide) (Graph.ScalarInvariant.empty 6 8 6)⟩

/-- A reserved root can be in range before its equation is installed. The
frontier theorem deliberately does not claim dependency closure. -/
theorem bounded_nominal_root_can_be_absent : nominalGraph.nodes.find 3 = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def rowGraph : Graph := { count := 4 }

theorem actual_refinement_shape_root :
    RootCompilation (Index.ofEnvironment scalarSource) .shape (.Refine ⟨0⟩ ⟨0⟩) rowGraph 0 rowGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def closureSource : Environment := { closures := [ClosureTy.bare ⟨0⟩] }

theorem actual_closure_shape_root :
    RootCompilation (Index.ofEnvironment closureSource) .shape (.Closure ⟨0⟩) rowGraph 0 rowGraph := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def refused : Graph :=
  { unitGraph with nodes := unitGraph.nodes.insert 2 (.done (.error (.unsupported (.Vector 0 .U8)))), count := 3 }

theorem actual_checked_failure_root :
    RootCompilation (Index.ofEnvironment {}) .execution (.Vector 0 .U8) unitGraph 2 refused := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_failure_root_bounded : 2 < refused.count :=
  actual_checked_failure_root.root_bound (Graph.Bounded.empty 2) (by decide) (Graph.ScalarInvariant.empty 2 8 2)

private def forged : Graph := { count := 2, leaves := NatIndexTree.empty.insert 66 100 }

/-- The actual compiler trusts its internal scalar cache: with a forged cache
it really can return an out-of-range node. -/
theorem forged_cache_returns_outside_root :
    RootCompilation (Index.ofEnvironment {}) .execution .U8 forged 100 forged := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forged_cache_breaks_scalar_invariant : ¬ forged.ScalarInvariant 2 8 := by
  intro valid
  have bound := forged_cache_returns_outside_root.root_bound (Graph.Bounded.empty 2) (by decide) valid
  have impossible : ¬ (100 < 2) := by decide
  exact impossible bound

end RootFrontierControls
end TrustIr.SourceLayout
