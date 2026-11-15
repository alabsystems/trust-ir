-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutDeterminism

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

/-- A successful derivation at an actually compiled array root executes the
exact source-indexed scaling equation. Checked failure roots cannot provide it. -/
theorem RootCompilation.array_scaled_execution {index : Index} {mode : Mode} {id : TyId} {count : Nat}
    {before after : Graph} {root : Nat} {value : Summary}
    (compiled : RootCompilation index mode (.Array id count) before root after)
    (derived : NodeDerivation after root value) :
    (scaled mode count (index.node mode id.index)).Executes after value := by
  obtain ⟨equation,found,kind⟩ := compiled.array_equation
  rcases kind with rfl | ⟨error,rfl⟩
  · exact derived.execution found
  · have impossible := derived.done_result found
    cases impossible

/-- Cached roots retain the original source index and original array equation
through all later graph extensions. -/
theorem Session.CompiledRoot.array_scaled_execution {source : Environment} {mode : Mode}
    {id : TyId} {count root : Nat} {graph : Graph} {value : Summary}
    (origin : Session.CompiledRoot source mode (.Array id count) root graph)
    (derived : NodeDerivation graph root value) :
    (scaled mode count ((Index.ofEnvironment source).node mode id.index)).Executes graph value := by
  obtain ⟨before,history,compiledGraph,compiled,growth⟩ := origin
  rw [history.index_eq] at compiled
  obtain ⟨equation,found,kind⟩ := compiled.array_equation
  have retained := growth root equation found
  rcases kind with rfl | ⟨error,rfl⟩
  · exact derived.execution retained
  · have impossible := derived.done_result retained
    cases impossible

/-- Every actual successful array query, including root/memo hits, supplies its
original source child-node derivation and exact size/alignment product. -/
theorem Session.Reachable.query_array_child {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : TyId) (count : Nat)
    (value : Summary) (run : session.query mode (.Array id count) = .ok (value,next)) :
    ∃ root child, Session.CompiledRoot source mode (.Array id count) root next.graph ∧
      NodeDerivation next.graph ((Index.ofEnvironment source).node mode id.index) child ∧
      value.size = child.size * count ∧ value.align = child.align := by
  obtain ⟨root,origin,derived⟩ := history.query_compilation_origin mode (.Array id count) value run
  obtain ⟨child,childDerived,size,align⟩ := (origin.array_scaled_execution derived).scaled_extent mode count _
  exact ⟨root,child,origin,childDerived,size,align⟩

/-- Source array geometry supplies every logical slot bound from the actual
child derivation. No physical parent bound is assumed. Zero count/stride remain
ordinary cases of the same law. -/
theorem Session.Reachable.query_array_geometry {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : TyId) (count : Nat)
    (value : Summary) (run : session.query mode (.Array id count) = .ok (value,next)) :
    ∃ child, NodeDerivation next.graph ((Index.ofEnvironment source).node mode id.index) child ∧
      value.size = child.size * count ∧ value.align = child.align ∧
      ∀ slot, slot < count → ∀ offset width, offset + width ≤ child.size →
        slot * child.size + offset + width ≤ value.size := by
  obtain ⟨_,child,_,derived,size,align⟩ := history.query_array_child mode id count value run
  refine ⟨child,derived,size,align,?_⟩
  intro slot inside offset width within
  rw [size]
  calc
    slot * child.size + offset + width ≤ (slot + 1) * child.size := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    _ ≤ count * child.size := Nat.mul_le_mul_right _ (by omega)
    _ = child.size * count := Nat.mul_comm _ _

/-- A source array query agrees with any valid earlier memo observation of its
original child node, rather than another node with an equal byte extent. -/
theorem Session.Reachable.query_array_prior_child {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : TyId) (count : Nat)
    (input value : Summary)
    (cached : session.memo.find ((Index.ofEnvironment source).node mode id.index) = some input)
    (run : session.query mode (.Array id count) = .ok (value,next)) :
    value.size = input.size * count ∧ value.align = input.align := by
  obtain ⟨_,child,_,derived,size,align⟩ := history.query_array_child mode id count value run
  have growth := (Session.query_preserves_derivation _ _ _ _ _ history.invariant run).2.2.1.equations
  have same := (history.cached _ input cached).unique_after_growth growth derived
  cases same
  exact ⟨size,align⟩

/-- Queries of different array lengths over the same original child and mode
share the same child summary along an actual source query history. -/
theorem Session.QueryChain.array_count_scaling {source : Environment}
    {before first current last : Session} (history : Session.Reachable source before)
    (mode : Mode) (id : TyId) (firstCount lastCount : Nat) (firstValue lastValue : Summary)
    (firstRun : before.query mode (.Array id firstCount) = .ok (firstValue,first))
    (chain : Session.QueryChain first current)
    (lastRun : current.query mode (.Array id lastCount) = .ok (lastValue,last)) :
    ∃ child : Summary, firstValue.size = child.size * firstCount ∧ lastValue.size = child.size * lastCount ∧
      firstValue.align = child.align ∧ lastValue.align = child.align := by
  obtain ⟨_,child,_,derived,size,align⟩ := history.query_array_child mode id firstCount firstValue firstRun
  have firstHistory := Session.Reachable.queried history firstRun
  obtain ⟨_,laterChild,_,laterDerived,laterSize,laterAlign⟩ :=
    (chain.reachable firstHistory).query_array_child mode id lastCount lastValue lastRun
  have growth := (Session.QueryChain.queried chain mode (.Array id lastCount) lastValue lastRun).graph_extends firstHistory
  have same := derived.unique_after_growth growth laterDerived
  cases same
  exact ⟨child,size,laterSize,align,laterAlign⟩

end TrustIr.SourceLayout

namespace TrustIr.SourceLayout.ArrayOriginControls

private def source : Environment := { types := [some .U16] }
private def child : Summary := { size := 2, align := some 2 }
private def three : Summary := { size := 6, align := some 2 }
private def five : Summary := { size := 10, align := some 2 }
private def afterThree : Session :=
  (((prepare source).query .execution (.Array ⟨0⟩ 3)).toOption.getD (three,prepare source)).2
private def afterOther : Session :=
  ((afterThree.query .shape .U8).toOption.getD ({ size := 1, align := some 1 },afterThree)).2
private def afterFive : Session :=
  ((afterOther.query .execution (.Array ⟨0⟩ 5)).toOption.getD (five,afterOther)).2

/-- Cold source query with a concrete original type-row reference. -/
theorem actual_array_query : query source .execution (.Array ⟨0⟩ 3) = .ok three := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_shape_query : query source .shape (.Array ⟨0⟩ 3) = .ok three := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_cached_array_query : (afterThree.query .execution (.Array ⟨0⟩ 3)).map (fun pair => pair.1) =
    .ok three := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_child_memo : afterThree.memo.find ((Index.ofEnvironment source).node .execution 0) =
    some child := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- An actual nonempty memo yields a product law for every successful later
array count, without supplying the desired parent extent as a premise. -/
theorem actual_prior_child_any_count (count : Nat) (value : Summary) (next : Session)
    (run : afterThree.query .execution (.Array ⟨0⟩ count) = .ok (value,next)) :
    value.size = 2 * count ∧ value.align = some 2 := by
  trustIrCompilerProof {
    have history : Session.Reachable source afterThree :=
      .queried (mode := .execution) (ty := .Array ⟨0⟩ 3) (value := three) .prepared (by rfl)
    exact history.query_array_prior_child .execution ⟨0⟩ count child value actual_child_memo run
  } {
    have history : Session.Reachable source afterThree :=
      .queried (mode := .execution) (ty := .Array ⟨0⟩ 3) (value := three) .prepared (by trustIrReduce)
    exact history.query_array_prior_child .execution ⟨0⟩ count child value actual_child_memo run
  }

/-- Interleaving another mode/type does not change the source element used for
arrays of three and five elements. -/
theorem actual_interleaved_scaling :
    ∃ input : Summary, three.size = input.size * 3 ∧ five.size = input.size * 5 ∧
      three.align = input.align ∧ five.align = input.align := by
  trustIrCompilerProof {
    have chain : Session.QueryChain afterThree afterOther :=
      .queried (.refl _) .shape .U8 { size := 1, align := some 1 } (by rfl)
    exact chain.array_count_scaling (source := source) (last := afterFive) .prepared .execution ⟨0⟩ 3 5 three five (by rfl) (by rfl)
  } {
    have chain : Session.QueryChain afterThree afterOther :=
      .queried (.refl _) .shape .U8 { size := 1, align := some 1 } (by trustIrReduce)
    exact chain.array_count_scaling (source := source) (last := afterFive) .prepared .execution ⟨0⟩ 3 5 three five (by trustIrReduce) (by trustIrReduce)
  }

/-- Zero logical length still retains the actual child alignment. -/
theorem actual_zero_count : query source .execution (.Array ⟨0⟩ 0) =
    .ok { size := 0, align := some 2 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- A positive-length array of zero-byte elements has zero physical extent. -/
theorem actual_zero_stride : query { types := [some .Unit] } .execution (.Array ⟨0⟩ 3) =
    .ok { size := 0, align := some 1 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_missing_type_refuses : query source .execution (.Array ⟨7⟩ 3) =
    .error (.missingType 7) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_overflow_count_refuses : query source .execution (.Array ⟨0⟩ (word64Max + 1)) =
    .error .sizeOverflow := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_noncanonical_target_refuses :
    query { types := [some .U16], canonicalScalars := false } .execution (.Array ⟨0⟩ 3) =
      .error .scalarTarget := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end TrustIr.SourceLayout.ArrayOriginControls
