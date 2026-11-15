-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutReferenceBounds

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

/-- Reference bounds now follow from actual source history without a caller
certificate for preparation. No acyclicity or source-validity premise is used. -/
theorem Session.Reachable.reference_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.ReferenceBounds := by
  induction history with
  | prepared => exact prepare_references source
  | queried prior run ih => exact prior.query_reference_bounds ih _ _ _ run

theorem Session.Reachable.query_reference_invariant {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (ty : Ty) (value : Summary)
    (run : session.query mode ty = .ok (value,next)) : next.graph.ReferenceBounds :=
  history.query_reference_bounds history.reference_invariant mode ty value run

/-- Reference bounds plus a supplied installation certificate close the prepared prefix. -/
theorem prepared_closed_if_complete (source : Environment) (complete : (prepare source).graph.Complete) :
    (prepare source).graph.ClosedRegion (fun node => node < (prepare source).graph.count) :=
  Graph.closed_prefix (prepare_references source) complete

theorem Session.Reachable.restrict_prepared_if_complete {source : Environment} {session : Session}
    (history : Session.Reachable source session) (complete : (prepare source).graph.Complete)
    {node : Nat} (inside : node < (prepare source).graph.count) {value : Summary}
    (derived : NodeDerivation session.graph node value) : NodeDerivation (prepare source).graph node value :=
  history.prepared_region_derivation (prepared_closed_if_complete source complete) inside derived

/-- Actual cached and compiled query paths preserve equation installation. -/
theorem Session.Reachable.query_complete {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (complete : session.graph.Complete)
    (mode : Mode) (ty : Ty) (value : Summary) (run : session.query mode ty = .ok (value,next)) :
    next.graph.Complete := by
  obtain ⟨root,graph,reused,selected,_,graphSame,_,_⟩ :=
    Session.query_selection session mode ty value next history.invariant run
  rw [graphSame]
  cases selected with
  | cached hit => exact complete
  | compiled graph compiled => exact compiled.preserves_complete complete

theorem Session.Reachable.complete_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) : session.graph.Complete := by
  induction history with
  | prepared => exact prepare_complete source
  | queried prior run ih => exact prior.query_complete ih _ _ _ run

/-- Every actual source history has a closed installed prefix, including
histories starting from malformed or cyclic source declarations. -/
theorem Session.Reachable.closed_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) :
    session.graph.ClosedRegion (fun node => node < session.graph.count) :=
  Graph.closed_prefix history.reference_invariant history.complete_invariant

theorem prepared_closed (source : Environment) :
    (prepare source).graph.ClosedRegion (fun node => node < (prepare source).graph.count) :=
  Graph.closed_prefix (prepare_references source) (prepare_complete source)

/-- A later finite derivation rooted in the prepared prefix already existed in
that exact prepared graph; no caller completeness or closure premise is needed. -/
theorem Session.Reachable.restrict_prepared {source : Environment} {session : Session}
    (history : Session.Reachable source session) {node : Nat}
    (inside : node < (prepare source).graph.count) {value : Summary}
    (derived : NodeDerivation session.graph node value) : NodeDerivation (prepare source).graph node value :=
  history.prepared_region_derivation (prepared_closed source) inside derived

/-- Successful cached roots retain the source-index and count checks made by
actual array compilation, even after arbitrary later query growth. -/
theorem Session.CompiledRoot.array_source_bounds {source : Environment} {mode : Mode}
    {id : TyId} {count root : Nat} {graph : Graph} {value : Summary}
    (origin : Session.CompiledRoot source mode (.Array id count) root graph)
    (derived : NodeDerivation graph root value) :
    id.index < (Index.ofEnvironment source).typeRows.size ∧ count ≤ word64Max := by
  obtain ⟨before,history,compiledGraph,compiled,growth⟩ := origin
  rw [history.index_eq] at compiled
  obtain ⟨equation,found,kind⟩ := compiled.array_equation_source
  have retained := growth root equation found
  rcases kind with ⟨same,inside,bounded⟩ | ⟨error,same⟩
  · exact ⟨inside,bounded⟩
  · cases same
    have impossible := derived.done_result retained
    cases impossible

/-- Every successful array query has an original prepared child derivation.
The source-index bound and closed dependency region are derived, not supplied. -/
theorem Session.Reachable.query_array_prepared_child {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : TyId) (count : Nat)
    (value : Summary) (run : session.query mode (.Array id count) = .ok (value,next)) :
    ∃ child, NodeDerivation (prepare source).graph ((Index.ofEnvironment source).node mode id.index) child ∧
      value.size = child.size * count ∧ value.align = child.align ∧ count ≤ word64Max := by
  obtain ⟨root,origin,rootDerived⟩ := history.query_compilation_origin mode (.Array id count) value run
  have bounds := origin.array_source_bounds rootDerived
  obtain ⟨_,child,_,derived,size,align⟩ := history.query_array_child mode id count value run
  have inside : (Index.ofEnvironment source).node mode id.index < (prepare source).graph.count := by
    let index := Index.ofEnvironment source
    have frontier := (prepare_derivation source).1.2
    change 2 * index.count + 2 ≤ (prepare source).graph.count at frontier
    have sourceSlot : id.index < index.count := by
      have rowBound := bounds.1
      change id.index < index.typeRows.size at rowBound
      unfold Index.count Index.closureBase Index.enumBase Index.structBase
      omega
    change index.node mode id.index < (prepare source).graph.count
    unfold Index.node
    split <;> omega
  exact ⟨child,(Session.Reachable.queried history run).restrict_prepared inside derived,size,align,bounds.2⟩

/-- Independently reached actual sessions agree on their original array child,
without a caller source-validity, completeness, region or node-bound premise. -/
theorem Session.Reachable.forked_array_prepared {source : Environment}
    {left leftNext right rightNext : Session} (leftHistory : Session.Reachable source left)
    (rightHistory : Session.Reachable source right) (mode : Mode) (id : TyId)
    (leftCount rightCount : Nat) (leftValue rightValue : Summary)
    (leftRun : left.query mode (.Array id leftCount) = .ok (leftValue,leftNext))
    (rightRun : right.query mode (.Array id rightCount) = .ok (rightValue,rightNext)) :
    ∃ child, NodeDerivation (prepare source).graph ((Index.ofEnvironment source).node mode id.index) child ∧
      leftValue.size = child.size * leftCount ∧ rightValue.size = child.size * rightCount ∧
      leftValue.align = child.align ∧ rightValue.align = child.align := by
  obtain ⟨child,first,size,align,_⟩ := leftHistory.query_array_prepared_child mode id leftCount leftValue leftRun
  obtain ⟨other,second,otherSize,otherAlign,_⟩ :=
    rightHistory.query_array_prepared_child mode id rightCount rightValue rightRun
  have same := first.functional _ second
  cases same
  exact ⟨child,first,size,otherSize,align,otherAlign⟩

theorem Session.Reachable.forked_array_layout {source : Environment}
    {left leftNext right rightNext : Session} (leftHistory : Session.Reachable source left)
    (rightHistory : Session.Reachable source right) (mode : Mode) (id : TyId) (count : Nat)
    (leftValue rightValue : Summary)
    (leftRun : left.query mode (.Array id count) = .ok (leftValue,leftNext))
    (rightRun : right.query mode (.Array id count) = .ok (rightValue,rightNext)) :
    leftValue.size = rightValue.size ∧ leftValue.align = rightValue.align := by
  obtain ⟨_,_,leftSize,rightSize,leftAlign,rightAlign⟩ :=
    leftHistory.forked_array_prepared rightHistory mode id count count leftValue rightValue leftRun rightRun
  exact ⟨leftSize.trans rightSize.symm,leftAlign.trans rightAlign.symm⟩

namespace PreparedReferenceControls
private def before : Graph := { count := 2 }
private def unitValue : Summary := { size := 0, align := some 1 }
private def neverValue : Summary := { size := 0, align := none }
private def physical : Graph :=
  { nodes := (NatIndexTree.empty.insert 2 (.done (.ok unitValue))).insert 3 (.done (.ok unitValue)), count := 4 }
private def logical : Graph :=
  { nodes := NatIndexTree.empty.insert 2 (.done (.ok neverValue)), count := 3, leaves := NatIndexTree.empty.insert 0 2 }

theorem physical_never_children :
    EnumNodesCompilation (Index.ofEnvironment {}) .execution true [.Never,.Never] before
      [(.Never,2),(.Never,3)] physical := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem logical_never_children :
    EnumNodesCompilation (Index.ofEnvironment {}) .shape false [.Never,.Never] before
      [(.Never,2),(.Never,2)] logical := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

/-- Physical placeholders allocate separate Unit summaries; ordinary shape-mode Never
compilation interns the actual unaligned Never summary. Neither path changes Ty labels. -/
theorem physical_and_logical_references : physical.ReferenceBounds ∧ logical.ReferenceBounds :=
  ⟨(physical_never_children.references (Graph.Bounded.empty 2) (by decide)
      (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)).1,
   (logical_never_children.references (Graph.Bounded.empty 2) (by decide)
      (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)).1⟩

private def executionNever : Graph :=
  { nodes := (NatIndexTree.empty.insert 2 (.done (.error (.unsupported .Never)))).insert 3
      (.done (.error (.unsupported .Never))), count := 4 }

theorem ordinary_execution_never_refuses :
    EnumNodesCompilation (Index.ofEnvironment {}) .execution false [.Never,.Never] before
      [(.Never,2),(.Never,3)] executionNever := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem refused_execution_never_references : executionNever.ReferenceBounds :=
  (ordinary_execution_never_refuses.references (Graph.Bounded.empty 2) (by decide)
    (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)).1

private def refused : Graph :=
  { nodes := NatIndexTree.empty.insert 2 (.done (.error (.missingType 99))), count := 3 }

theorem refused_field_still_bounded :
    EnumNodesCompilation (Index.ofEnvironment {}) .execution true [.Array ⟨99⟩ 3] before
      [(.Array ⟨99⟩ 3,2)] refused := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem refused_field_references : refused.ReferenceBounds :=
  (refused_field_still_bounded.references (Graph.Bounded.empty 2) (by decide)
    (Graph.ScalarInvariant.empty 2 8 2) (Graph.ReferenceBounds.empty 2)).1

private def enumeration : EnumDef :=
  { id := ⟨7⟩, name := "Pair", variants := [{ name := "Byte", fields := [.U8] },{ name := "Word", fields := [.U16] }] }
private def enumSource : Environment := { enums := [enumeration] }

set_option maxRecDepth 4096 in
theorem actual_enum_extent : (query enumSource .execution (.Enum ⟨7⟩)).map Summary.size = .ok 4 := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem actual_enum_prepared_references : (prepare enumSource).graph.ReferenceBounds := prepare_references enumSource

private def badTuple : Environment :=
  { tupleLayouts := [{ tupleType := ⟨99⟩, size := 1, align := 1, fieldOffsets := [] }] }
private def badClosure : Environment :=
  { closureLayouts := [{ closure := ⟨99⟩, size := 0, align := 1, captureOffsets := [] }] }

theorem missing_tuple_validator_refuses : (prepare badTuple).graph.query 0 = .error (.missingType 99) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem missing_closure_validator_refuses : (prepare badClosure).graph.query 1 = .error (.incoherent "closure" 99) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem refusing_validators_still_bounded :
    (prepare badTuple).graph.ReferenceBounds ∧ (prepare badClosure).graph.ReferenceBounds :=
  ⟨prepare_references badTuple,prepare_references badClosure⟩

private def cycleSource : Environment := { types := [some (.Array ⟨0⟩ 1)] }

theorem source_cycle_refuses : query cycleSource .execution (.Array ⟨0⟩ 2) = .error (.cycle 1) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem source_cycle_references : (prepare cycleSource).graph.ReferenceBounds := prepare_references cycleSource

private def forwardSource : Environment := { types := [some (.Array ⟨1⟩ 3),some .U16] }
private def thirty : Summary := { size := 30, align := some 2 }
private def afterForward : Session :=
  (((prepare forwardSource).query .execution (.Array ⟨0⟩ 5)).toOption.getD (thirty,prepare forwardSource)).2

theorem forward_array_extent : query forwardSource .execution (.Array ⟨0⟩ 5) = .ok thirty := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem forward_query_references : afterForward.graph.ReferenceBounds := by
  trustIrCompilerProof {
    exact (Session.Reachable.prepared (source := forwardSource)).query_reference_invariant .execution (.Array ⟨0⟩ 5) thirty (by rfl)
  } {
    exact (Session.Reachable.prepared (source := forwardSource)).query_reference_invariant .execution (.Array ⟨0⟩ 5) thirty (by trustIrReduce)
  }

theorem forward_cached_references :
    afterForward.query .execution (.Array ⟨0⟩ 5) = .ok (thirty,afterForward) ∧ afterForward.graph.ReferenceBounds := by
  trustIrCompilerProof {
    exact ⟨rfl,forward_query_references⟩
  } {
    exact ⟨(by trustIrReduce),forward_query_references⟩
  }

private def mixedSource : Environment :=
  { types := [none,some .U8],
    structs := [{ id := ⟨42⟩, name := "MissingChild", fields := [{ name := "bad", ty := .Array ⟨99⟩ 2, offset := none }], size := none, align := none }],
    enums := [enumeration], closures := [ClosureTy.bare ⟨17⟩] }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Check the actual lookup for every reserved slot of all four row kinds,
in both modes, plus both validators, independently of the completeness proof. -/
theorem mixed_reserved_lookups :
    (List.range 12).all (fun node => ((prepare mixedSource).graph.nodes.find node).isSome) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem mixed_complete : (prepare mixedSource).graph.Complete := prepare_complete mixedSource

theorem refusing_validators_complete :
    (prepare badTuple).graph.Complete ∧ (prepare badClosure).graph.Complete :=
  ⟨prepare_complete badTuple,prepare_complete badClosure⟩

/-- Completeness and closure do not imply termination or successful layout. -/
theorem cyclic_source_complete : (prepare cycleSource).graph.Complete := prepare_complete cycleSource

theorem cyclic_source_closed :
    (prepare cycleSource).graph.ClosedRegion (fun node => node < (prepare cycleSource).graph.count) :=
  prepared_closed cycleSource

theorem forward_query_complete : afterForward.graph.Complete := by
  trustIrCompilerProof {
    exact (Session.Reachable.prepared (source := forwardSource)).query_complete (prepare_complete forwardSource)
      .execution (.Array ⟨0⟩ 5) thirty (by rfl)
  } {
    exact (Session.Reachable.prepared (source := forwardSource)).query_complete (prepare_complete forwardSource)
      .execution (.Array ⟨0⟩ 5) thirty (by trustIrReduce)
  }

theorem forward_cached_complete :
    afterForward.query .execution (.Array ⟨0⟩ 5) = .ok (thirty,afterForward) ∧ afterForward.graph.Complete := by
  trustIrCompilerProof {
    exact ⟨rfl,forward_query_complete⟩
  } {
    exact ⟨(by trustIrReduce),forward_query_complete⟩
  }

theorem forward_query_closed :
    afterForward.graph.ClosedRegion (fun node => node < afterForward.graph.count) :=
  Graph.closed_prefix forward_query_references forward_query_complete

/-- Both actual forks start at the same prepared source, but allocate different
array roots before the right fork continues with a third count. -/
theorem automatic_forked_array_origin :
    ∃ child, NodeDerivation (prepare forwardSource).graph
      ((Index.ofEnvironment forwardSource).node .execution 0) child ∧
      18 = child.size * 3 ∧ 42 = child.size * 7 ∧
      some 2 = child.align ∧ some 2 = child.align := by
  trustIrCompilerProof {
    exact (Session.Reachable.prepared (source := forwardSource)).forked_array_prepared
      (.queried (Session.Reachable.prepared (source := forwardSource)) (mode := .execution)
        (ty := .Array ⟨0⟩ 5) (value := thirty) (by rfl)) .execution ⟨0⟩ 3 7
        { size := 18, align := some 2 } { size := 42, align := some 2 } (by rfl) (by rfl)
  } {
    exact (Session.Reachable.prepared (source := forwardSource)).forked_array_prepared
      (.queried (Session.Reachable.prepared (source := forwardSource)) (mode := .execution)
        (ty := .Array ⟨0⟩ 5) (value := thirty) (by trustIrReduce)) .execution ⟨0⟩ 3 7
        { size := 18, align := some 2 } { size := 42, align := some 2 } (by trustIrReduce) (by trustIrReduce)
  }

theorem automatic_cached_array_origin :
    ∃ child, NodeDerivation (prepare forwardSource).graph
      ((Index.ofEnvironment forwardSource).node .execution 0) child ∧
      thirty.size = child.size * 5 ∧ thirty.align = child.align ∧ 5 ≤ word64Max := by
  trustIrCompilerProof {
    have history : Session.Reachable forwardSource afterForward :=
      .queried (mode := .execution) (ty := .Array ⟨0⟩ 5) (value := thirty) .prepared (by rfl)
    exact history.query_array_prepared_child .execution ⟨0⟩ 5 thirty (by rfl)
  } {
    have history : Session.Reachable forwardSource afterForward :=
      .queried (mode := .execution) (ty := .Array ⟨0⟩ 5) (value := thirty) .prepared (by trustIrReduce)
    exact history.query_array_prepared_child .execution ⟨0⟩ 5 thirty (by trustIrReduce)
  }

theorem missing_zero_array_refuses : query {} .execution (.Array ⟨99⟩ 0) = .error (.missingType 99) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem empty_source_row_zero_array_refuses :
    query { types := [none] } .execution (.Array ⟨0⟩ 0) = .error (.missingType 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem cyclic_zero_array_refuses : query cycleSource .execution (.Array ⟨0⟩ 0) = .error (.cycle 1) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem excessive_count_refuses_before_zero_stride :
    query { types := [some (.Tuple [])] } .execution (.Array ⟨0⟩ (word64Max + 1)) = .error .sizeOverflow := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem zero_stride_array_succeeds :
    query { types := [some (.Tuple [])] } .execution (.Array ⟨0⟩ 7) = .ok { size := 0, align := some 1 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem scalar_target_refusal_precedes_array_source :
    query { canonicalScalars := false } .execution (.Array ⟨99⟩ 0) = .error .scalarTarget := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end PreparedReferenceControls
end TrustIr.SourceLayout
