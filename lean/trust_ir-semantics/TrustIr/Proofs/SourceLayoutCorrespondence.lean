-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourcePreparedReferences

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

/-- Transport the actual finite derivation along corresponding ordered
equations. No acyclicity, successful evaluation or node-number equality is assumed. -/
theorem NodeDerivation.transport_nodes {left right : Graph} {relation : Nat → Nat → Prop}
    (paired : left.Correspondence right relation) {node : Nat} {value : Summary}
    (derived : NodeDerivation left node value) :
    ∀ other, relation node other → NodeDerivation right other value := by
  induction derived using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ => ∀ otherSteps, StepsCorrespond relation steps otherSteps →
      StepsDerivation right otherSteps first last) with
  | equation found initial steps finished transferred =>
    intro other related
    obtain ⟨leftEquation,rightEquation,leftFound,rightFound,equations⟩ := paired _ other related
    have same := Option.some.inj (found.symm.trans leftFound)
    cases same
    cases equations with
    | mk kind start finish matched =>
      exact .equation rightFound initial (transferred _ matched) finished
  | nil state =>
    rename_i other matched
    cases matched
    exact .nil state
  | check updated later transferred =>
    rename_i other matched
    cases matched with
    | check update tail => exact .check updated (transferred _ tail)
  | child solved updated later childTransferred restTransferred =>
    rename_i other matched
    cases matched with
    | child update related tail => exact .child (childTransferred _ related) updated (restTransferred _ tail)

theorem NodeDerivation.corresponding_unique {left right : Graph} {relation : Nat → Nat → Prop}
    (paired : left.Correspondence right relation) {first second : Nat} (related : relation first second)
    {value other : Summary} (derived : NodeDerivation left first value) (another : NodeDerivation right second other) :
    value = other := (derived.transport_nodes paired second related).functional _ another

theorem NodeDerivation.below_frontier {graph : Graph} (bounded : graph.Bounded)
    {node : Nat} {value : Summary} (derived : NodeDerivation graph node value) : node < graph.count := by
  cases derived with
  | equation found initial steps finished =>
    by_cases inside : node < graph.count
    · exact inside
    · rw [bounded node (Nat.le_of_not_lt inside)] at found
      cases found

/-- Independent actual compilations of the same type/mode have corresponding
roots. Original references use the closed prepared component; new nodes are
paired by the compiler proof, including cache hits and recursive children. -/
theorem Session.CompiledRoot.corresponds {source : Environment} {mode : Mode} {ty : Ty}
    {left right : Graph} {first second : Nat}
    (leftOrigin : Session.CompiledRoot source mode ty first left)
    (rightOrigin : Session.CompiledRoot source mode ty second right) :
    ∃ relation, left.Correspondence right relation ∧ relation first second := by
  obtain ⟨leftBefore,leftHistory,leftCompiled,leftRun,leftGrowth⟩ := leftOrigin
  obtain ⟨rightBefore,rightHistory,rightCompiled,rightRun,rightGrowth⟩ := rightOrigin
  have leftFrontier := leftHistory.invariant.1.2
  have rightFrontier := rightHistory.invariant.1.2
  have leftScalars := leftHistory.scalar_invariant
  have rightScalars := rightHistory.scalar_invariant
  rw [leftHistory.index_eq] at leftRun leftFrontier leftScalars
  rw [rightHistory.index_eq] at rightRun rightFrontier rightScalars
  have originalGraphs := Graph.Correspondence.closed_region (prepared_closed source)
    leftHistory.extends_prepared rightHistory.extends_prepared
  have originalPairs : ∀ node, node < 2 * (Index.ofEnvironment source).count + 2 →
      node = node ∧ node < (prepare source).graph.count := by
    intro node inside
    exact ⟨rfl,Nat.lt_of_lt_of_le inside (prepare_derivation source).1.2⟩
  obtain ⟨relation,included,compiledGraphs,roots⟩ := leftRun.corresponds rightRun
    leftHistory.invariant.1.1 leftFrontier leftScalars rightHistory.invariant.1.1 rightFrontier rightScalars
    originalGraphs originalPairs
  exact ⟨relation,compiledGraphs.grow leftGrowth rightGrowth,roots⟩

/-- Every successful query of one type/mode in independently reached sessions
of the same source returns the entire same Summary. No source validity,
acyclicity, graph equality or caller correspondence premise is required. -/
theorem Session.Reachable.forked_typed_summary {source : Environment}
    {left leftNext right rightNext : Session} (leftHistory : Session.Reachable source left)
    (rightHistory : Session.Reachable source right) (mode : Mode) (ty : Ty) (first second : Summary)
    (leftRun : left.query mode ty = .ok (first,leftNext))
    (rightRun : right.query mode ty = .ok (second,rightNext)) : first = second := by
  obtain ⟨_,leftOrigin,leftDerived⟩ := leftHistory.query_compilation_origin mode ty first leftRun
  obtain ⟨_,rightOrigin,rightDerived⟩ := rightHistory.query_compilation_origin mode ty second rightRun
  obtain ⟨relation,paired,roots⟩ := leftOrigin.corresponds rightOrigin
  exact leftDerived.corresponding_unique paired roots rightDerived

/-- A successful prepared source row agrees with an independently queried
instance of its actual source type. Copied bodies and forward aliases are both
justified by preparation's retained compilation witness. -/
theorem Session.Reachable.prepared_type_summary {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (position : Nat) (ty : Ty)
    (first second : Summary) (found : (trustIrListGet? source.types position) = some (some ty))
    (derived : NodeDerivation (prepare source).graph ((Index.ofEnvironment source).node mode position) first)
    (run : session.query mode ty = .ok (second,next)) : first = second := by
  obtain ⟨leftBefore,leftCompiled,leftRoot,leftBounded,leftFrontier,leftScalars,leftRun,leftRetained,installed⟩ :=
    prepare_type_compilation source mode position ty found
  have leftDerived : NodeDerivation (prepare source).graph leftRoot first := by
    cases original : leftCompiled.nodes.find leftRoot with
    | none =>
      rw [original] at installed
      exact (derived.execution installed).alias_child
    | some equation =>
      rw [original] at installed
      exact (derived.execution installed).to_node (leftRetained _ _ original)
  obtain ⟨rightRoot,rightOrigin,rightDerived⟩ := history.query_compilation_origin mode ty second run
  obtain ⟨rightBefore,rightHistory,rightCompiled,rightRun,rightRetained⟩ := rightOrigin
  have rightFrontier := rightHistory.invariant.1.2
  have rightScalars := rightHistory.scalar_invariant
  rw [rightHistory.index_eq] at rightRun rightFrontier rightScalars
  have paired := Graph.Correspondence.closed_region (prepared_closed source)
    (Graph.Extends.refl (prepare source).graph) (Session.Reachable.queried history run).extends_prepared
  have originalPairs : ∀ node, node < 2 * (Index.ofEnvironment source).count + 2 →
      node = node ∧ node < (prepare source).graph.count := by
    intro node inside
    exact ⟨rfl,Nat.lt_of_lt_of_le inside (prepare_derivation source).1.2⟩
  obtain ⟨relation,_,graphs,roots⟩ := leftRun.corresponds_in_extensions rightRun
    leftBounded leftFrontier leftScalars rightHistory.invariant.1.1 rightFrontier rightScalars
    leftRetained rightRetained paired originalPairs
  exact leftDerived.corresponding_unique graphs roots rightDerived

/-- Successful actual array roots retain their exact compiled equation,
including roots obtained from caches after further graph growth. -/
theorem Session.CompiledRoot.array_success_equation {source : Environment} {mode : Mode}
    {id : TyId} {count root : Nat} {graph : Graph} {value : Summary}
    (origin : Session.CompiledRoot source mode (.Array id count) root graph)
    (derived : NodeDerivation graph root value) :
    graph.nodes.find root = some (scaled mode count ((Index.ofEnvironment source).node mode id.index)) := by
  obtain ⟨before,history,compiledGraph,compiled,growth⟩ := origin
  rw [history.index_eq] at compiled
  obtain ⟨equation,found,kind⟩ := compiled.array_equation
  have retained := growth root equation found
  rcases kind with rfl | ⟨error,rfl⟩
  · exact retained
  · have impossible := derived.done_result retained
    cases impossible

/-- Independently grown actual array-query graphs correspond at their roots
and original source component, without equating their other fresh nodes. -/
theorem Session.Reachable.forked_array_summary {source : Environment}
    {left leftNext right rightNext : Session} (leftHistory : Session.Reachable source left)
    (rightHistory : Session.Reachable source right) (mode : Mode) (id : TyId) (count : Nat)
    (leftValue rightValue : Summary)
    (leftRun : left.query mode (.Array id count) = .ok (leftValue,leftNext))
    (rightRun : right.query mode (.Array id count) = .ok (rightValue,rightNext)) : leftValue = rightValue := by
  obtain ⟨first,leftOrigin,leftDerived⟩ := leftHistory.query_compilation_origin mode (.Array id count) leftValue leftRun
  obtain ⟨second,rightOrigin,rightDerived⟩ := rightHistory.query_compilation_origin mode (.Array id count) rightValue rightRun
  obtain ⟨_,childDerived,_,_,_⟩ := leftHistory.query_array_prepared_child mode id count leftValue leftRun
  have inside := childDerived.below_frontier (prepare_derivation source).1.1
  have paired := Graph.Correspondence.scaled_roots (prepared_closed source)
    (Session.Reachable.queried leftHistory leftRun).extends_prepared
    (Session.Reachable.queried rightHistory rightRun).extends_prepared mode count inside
    (leftOrigin.array_success_equation leftDerived) (rightOrigin.array_success_equation rightDerived)
  exact leftDerived.corresponding_unique paired (Or.inr ⟨rfl,rfl⟩) rightDerived

namespace CorrespondenceControls

private def value : Summary :=
  { size := 2, align := some 2, fields := [{ ty := .U16, offset := 0, size := 2, align := 2 }] }
private def other : Summary :=
  { size := 2, align := some 2, fields := [{ ty := .Bool, offset := 0, size := 2, align := 2 }] }
private def pair (a b : Nat) : Prop := (a = 0 ∧ b = 10) ∨ (a = 7 ∧ b = 0)
private def left : Graph :=
  { nodes := (NatIndexTree.empty.insert 0 (.done (.ok value))).insert 7 (.alias 0), count := 8 }
private def right : Graph :=
  { nodes := (NatIndexTree.empty.insert 10 (.done (.ok value))).insert 0 (.alias 10), count := 11 }

/-- The right root reuses the left child's numeric ID, while its own child
has another ID. Neither numeric identity nor disjoint graph domains is required. -/
theorem aliases_with_colliding_numbers : left.Correspondence right pair := by
  intro a b related
  rcases related with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done pair (.ok value)⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.alias (Or.inl ⟨rfl,rfl⟩)⟩

private theorem leftLeaf : NodeDerivation left 0 value :=
  .equation (equation := .done (.ok value)) rfl rfl (.nil value) rfl

private theorem leftRoot : NodeDerivation left 7 value :=
  .equation (equation := .alias 0) rfl rfl (.child leftLeaf rfl (.nil value)) rfl

theorem complete_metadata_transports : NodeDerivation right 0 value :=
  leftRoot.transport_nodes aliases_with_colliding_numbers 0 (Or.inr ⟨rfl,rfl⟩)

theorem same_extent_different_metadata : value.size = other.size ∧ value.align = other.align ∧ value ≠ other := by
  refine ⟨rfl,rfl,?_⟩
  intro same
  have fields := congrArg (fun summary => summary.fields.map (·.ty)) same
  cases fields

private def wrong : Graph := { nodes := NatIndexTree.empty.insert 10 (.done (.ok other)), count := 11 }

theorem metadata_mismatch_rejects_correspondence :
    ¬ left.Correspondence wrong (fun a b => a = 0 ∧ b = 10) := by
  intro paired
  have wrongRun : NodeDerivation wrong 10 other :=
    .equation (equation := .done (.ok other)) rfl rfl (.nil other) rfl
  exact same_extent_different_metadata.2.2 (leftLeaf.corresponding_unique paired ⟨rfl,rfl⟩ wrongRun)

theorem reversed_children_reject_diagonal :
    ¬ StepsCorrespond (fun a b => a = b)
      ([.child 1 (fun _ (state : Unit) => .ok state),.child 2 (fun _ state => .ok state)] : List (Step Unit))
      [.child 2 (fun _ state => .ok state),.child 1 (fun _ state => .ok state)] := by
  intro paired
  cases paired with
  | child update same later => cases same

theorem checks_cannot_be_replaced_by_children :
    ¬ StepsCorrespond (fun _ _ => True)
      ([.check (fun (_ : Unit) => .error .scalarTarget)] : List (Step Unit))
      [.child 0 (fun _ state => .ok state)] := by
  intro paired
  cases paired

private def cycleLeft : Graph := { nodes := NatIndexTree.empty.insert 0 (.alias 0), count := 1 }
private def cycleRight : Graph := { nodes := NatIndexTree.empty.insert 10 (.alias 10), count := 11 }

theorem cyclic_graphs_can_correspond : cycleLeft.Correspondence cycleRight (fun a b => a = 0 ∧ b = 10) := by
  intro a b related
  rcases related with ⟨rfl,rfl⟩
  exact ⟨_,_,rfl,rfl,Equation.Corresponds.alias ⟨rfl,rfl⟩⟩

/-- Correspondence transports finite success; cycle error payloads retain
their actual local node numbers rather than becoming globally equal errors. -/
theorem cycle_refusals_keep_local_ids :
    cycleLeft.query 0 = .error (.cycle 0) ∧ cycleRight.query 10 = .error (.cycle 10) := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

private def source : Environment := { types := [some .U16] }
private def leftBefore : Session :=
  (((prepare source).query .execution .U8).toOption.getD ({ size := 1, align := some 1 },prepare source)).2
private def rightBefore : Session :=
  (((prepare source).query .execution .U64).toOption.getD ({ size := 8, align := some 8 },prepare source)).2

theorem actual_forks_disagree_outside_source :
    leftBefore.graph.nodes.find 5 = some (.done (.ok { size := 1, align := some 1 })) ∧
    rightBefore.graph.nodes.find 5 = some (.done (.ok { size := 8, align := some 8 })) := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem actual_array_forks_succeed :
    (leftBefore.query .execution (.Array ⟨0⟩ 3)).map (fun pair => pair.1) = .ok { size := 6, align := some 2 } ∧
    (rightBefore.query .execution (.Array ⟨0⟩ 3)).map (fun pair => pair.1) = .ok { size := 6, align := some 2 } := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

/-- Arbitrary successful values in these genuinely disagreeing graphs must
agree in all Summary fields, without a global graph-equality hypothesis. -/
theorem actual_array_forks_unique (first second : Summary) (leftNext rightNext : Session)
    (leftRun : leftBefore.query .execution (.Array ⟨0⟩ 3) = .ok (first,leftNext))
    (rightRun : rightBefore.query .execution (.Array ⟨0⟩ 3) = .ok (second,rightNext)) : first = second := by
  trustIrCompilerProof {
    have lh : Session.Reachable source leftBefore :=
      .queried (mode := .execution) (ty := .U8) (value := { size := 1, align := some 1 }) .prepared (by rfl)
    have rh : Session.Reachable source rightBefore :=
      .queried (mode := .execution) (ty := .U64) (value := { size := 8, align := some 8 }) .prepared (by rfl)
    exact lh.forked_array_summary rh .execution ⟨0⟩ 3 first second leftRun rightRun
  } {
    have lh : Session.Reachable source leftBefore :=
      .queried (mode := .execution) (ty := .U8) (value := { size := 1, align := some 1 }) .prepared (by trustIrReduce)
    have rh : Session.Reachable source rightBefore :=
      .queried (mode := .execution) (ty := .U64) (value := { size := 8, align := some 8 }) .prepared (by trustIrReduce)
    exact lh.forked_array_summary rh .execution ⟨0⟩ 3 first second leftRun rightRun
  }

end CorrespondenceControls

namespace FieldCorrespondenceControls

private def scalar : Summary := { size := 1, align := some 1 }
private def pair (a b : Nat) : Prop := (a = 0 ∨ a = 1) ∧ b = 10
private def left : Graph :=
  { nodes := (NatIndexTree.empty.insert 0 (.done (.ok scalar))).insert 1 (.done (.ok scalar)), count := 2 }
private def right : Graph := { nodes := NatIndexTree.empty.insert 10 (.done (.ok scalar)), count := 11 }
private def leftFields : List (Ty × Nat) := [(.U8,0),(.Bool,1)]
private def rightFields : List (Ty × Nat) := [(.U8,10),(.Bool,10)]

theorem shared_scalar_rows :
    RowsCorrespond (fun a b => a.1 = b.1 ∧ pair a.2 b.2) leftFields rightFields :=
  .cons ⟨rfl,Or.inl rfl,rfl⟩ (.cons ⟨rfl,Or.inr rfl,rfl⟩ .nil)

theorem canonical_field_equations :
    (canonicalFields .execution "tuple" 0 leftFields).Corresponds pair
      (canonicalFields .execution "tuple" 0 rightFields) :=
  Equation.Corresponds.canonicalFields _ _ _ shared_scalar_rows

private theorem leaves : left.Correspondence right pair := by
  intro a b related
  rcases related with ⟨rfl | rfl,rfl⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done pair (.ok scalar)⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done pair (.ok scalar)⟩

private def leftParent : Graph :=
  { left with nodes := left.nodes.insert left.count (canonicalFields .execution "tuple" 0 leftFields), count := left.count + 1 }
private def rightParent : Graph :=
  { right with nodes := right.nodes.insert right.count (canonicalFields .execution "tuple" 0 rightFields), count := right.count + 1 }

/-- Two child occurrences on the left can correspond to one interned child
on the right; newly allocated parent roots also have different numeric IDs. -/
theorem allocated_canonical_parents :
    leftParent.Correspondence rightParent (fun a b => pair a b ∨ a = 2 ∧ b = 11) :=
  leaves.allocate_pair
    (((Graph.Bounded.empty 0).allocate (.done (.ok scalar))).allocate (.done (.ok scalar)))
    ((Graph.Bounded.empty 10).allocate (.done (.ok scalar))) canonical_field_equations

private def result : Summary :=
  { size := 2, align := some 1,
    fields := [{ ty := .U8, offset := 0, size := 1, align := 1 },{ ty := .Bool, offset := 1, size := 1, align := 1 }] }

theorem canonical_queries_keep_types_and_order :
    leftParent.query 2 = .ok result ∧ rightParent.query 11 = .ok result := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem canonical_metadata_transports : NodeDerivation rightParent 11 result :=
  (leftParent.query_derivation 2 result canonical_queries_keep_types_and_order.1).transport_nodes
    allocated_canonical_parents 11 (Or.inr ⟨rfl,rfl⟩)

private def wide : Summary := { size := 2, align := some 2 }
private def packedLeft : Equation := declaredFields .execution "struct" 7 2 1 1 false [(.U16,some 0,0)]
private def packedRight : Equation := declaredFields .execution "struct" 7 2 1 1 false [(.U16,some 0,10)]

theorem packed_field_equations : packedLeft.Corresponds (fun a b => a = 0 ∧ b = 10) packedRight :=
  Equation.Corresponds.declaredFields _ _ _ _ _ _ _ (.cons ⟨rfl,rfl,rfl,rfl⟩ .nil)

private def packedLeftGraph : Graph :=
  { nodes := (NatIndexTree.empty.insert 0 (.done (.ok wide))).insert 1 packedLeft, count := 2 }
private def packedRightGraph : Graph :=
  { nodes := (NatIndexTree.empty.insert 10 (.done (.ok wide))).insert 11 packedRight, count := 12 }
private def packedResult : Summary :=
  { size := 2, align := some 1, fields := [{ ty := .U16, offset := 0, size := 2, align := 1 }] }

theorem packed_queries_keep_effective_alignment :
    packedLeftGraph.query 1 = .ok packedResult ∧ packedRightGraph.query 11 = .ok packedResult := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem missing_nonzero_offset_refuses :
    ({ nodes := (NatIndexTree.empty.insert 0 (.done (.ok wide))).insert 1 (declaredFields .execution "struct" 7 2 1 1 false [(.U16,none,0)]), count := 2 } : Graph).query 1 =
      .error (.incoherent "struct" 7) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem omitted_zero_field_retains_metadata :
    ({ nodes := (NatIndexTree.empty.insert 0 (.done (.ok { size := 0, align := some 1 }))).insert 1 (declaredFields .execution "struct" 7 0 1 1 false [(.Tuple [],none,0)]), count := 2 } : Graph).query 1 =
      .ok { size := 0, align := some 1, fields := [{ ty := .Tuple [], offset := 0, size := 0, align := 1 }] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem transparent_multiple_carriers_refuse :
    ({ left with nodes := left.nodes.insert 2 (declaredFields .execution "struct" 7 2 1 1 true [(.U8,some 0,0),(.Bool,some 1,1)]), count := 3 } : Graph).query 2 =
      .error (.incoherent "struct" 7) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem prefix_sequences_correspond_before_initial_failure :
    (Equation.sequence [0] (.done (.error .sizeOverflow))).Corresponds (fun a b => a = 0 ∧ b = 10) (Equation.sequence [10] (.done (.error .sizeOverflow))) :=
  Equation.Corresponds.sequence (.cons ⟨rfl,rfl⟩ .nil) (Equation.Corresponds.done _ _)

theorem prefix_refusal_precedes_deferred_initial_failure :
    ({ nodes := (NatIndexTree.empty.insert 0 (.done (.error (.missingType 99)))).insert 1 (Equation.sequence [0] (.done (.error .sizeOverflow))), count := 2 } : Graph).query 1 =
      .error (.missingType 99) ∧
    ({ nodes := (NatIndexTree.empty.insert 10 (.done (.error (.missingType 99)))).insert 11 (Equation.sequence [10] (.done (.error .sizeOverflow))), count := 12 } : Graph).query 11 =
      .error (.missingType 99) := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem same_extent_field_types_cannot_be_substituted :
    ¬ RowsCorrespond (fun (a b : Ty × Nat) => a.1 = b.1 ∧ True) [(.U8,0)] [(.Bool,10)] := by
  intro paired
  cases paired with
  | cons pair later => cases pair.1

theorem declared_offsets_cannot_be_shifted :
    ¬ RowsCorrespond (fun (a b : Ty × Option Nat × Nat) => a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ True)
      [(.U8,some 0,0)] [(.U8,some 1,10)] := by
  intro paired
  cases paired with
  | cons pair later => cases pair.2.1

theorem truncated_child_rows_are_rejected : ¬ RowsCorrespond (fun (_ _ : Nat) => True) [0,1] [10] := by
  intro paired
  have different := paired.same_length
  cases different

end FieldCorrespondenceControls

namespace TypedCorrespondenceControls

private def source : Environment := { types := [some .U16] }
private def byte : Summary := { size := 1, align := some 1 }
private def wide : Summary := { size := 8, align := some 8 }
private def left : Session := (((prepare source).query .execution .U8).toOption.getD (byte,prepare source)).2
private def right : Session := (((prepare source).query .execution .U64).toOption.getD (wide,prepare source)).2
private def leftBool : Session := ((left.query .execution .Bool).toOption.getD (byte,left)).2
private def rightBool : Session := ((right.query .execution .Bool).toOption.getD (byte,right)).2

private theorem leftHistory : Session.Reachable source left := by
  trustIrCompilerProof {
    exact .queried (mode := .execution) (ty := .U8) (value := byte) .prepared (by rfl)
  } {
    exact .queried (mode := .execution) (ty := .U8) (value := byte) .prepared (by trustIrReduce)
  }

private theorem rightHistory : Session.Reachable source right := by
  trustIrCompilerProof {
    exact .queried (mode := .execution) (ty := .U64) (value := wide) .prepared (by rfl)
  } {
    exact .queried (mode := .execution) (ty := .U64) (value := wide) .prepared (by trustIrReduce)
  }

/-- Same typed scalar request, but one graph reuses an interned leaf and the
other allocates. Full type equality in the root cache remains separate. -/
theorem scalar_hit_and_miss_return_same_summary :
    (left.query .execution .Bool).map (fun pair => pair.1) = .ok byte ∧
    (right.query .execution .Bool).map (fun pair => pair.1) = .ok byte := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem scalar_hit_and_miss_have_different_frontiers : leftBool.graph.count = 6 ∧ rightBool.graph.count = 7 := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem cached_scalar_root_is_reused : leftBool.query .execution .Bool = .ok (byte,leftBool) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem cached_scalar_and_fresh_query_are_unique (first second : Summary) (leftNext rightNext : Session)
    (leftRun : leftBool.query .execution .Bool = .ok (first,leftNext))
    (rightRun : right.query .execution .Bool = .ok (second,rightNext)) : first = second := by
  trustIrCompilerProof {
    have history : Session.Reachable source leftBool :=
      .queried (mode := .execution) (ty := .Bool) (value := byte) leftHistory (by rfl)
    exact history.forked_typed_summary rightHistory .execution .Bool first second leftRun rightRun
  } {
    have history : Session.Reachable source leftBool :=
      .queried (mode := .execution) (ty := .Bool) (value := byte) leftHistory (by trustIrReduce)
    exact history.forked_typed_summary rightHistory .execution .Bool first second leftRun rightRun
  }

theorem scalar_hit_and_miss_are_unique (first second : Summary) (leftNext rightNext : Session)
    (leftRun : left.query .execution .Bool = .ok (first,leftNext))
    (rightRun : right.query .execution .Bool = .ok (second,rightNext)) : first = second :=
  leftHistory.forked_typed_summary rightHistory .execution .Bool first second leftRun rightRun

theorem nested_vectors_in_disagreeing_graphs :
    (left.query .execution (.Vector 3 (.Vector 2 .U16))).map (fun pair => pair.1) = .ok { size := 12, align := some 2 } ∧
    (right.query .execution (.Vector 3 (.Vector 2 .U16))).map (fun pair => pair.1) = .ok { size := 12, align := some 2 } := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

private def tupleTy : Ty := .Tuple [.U8,.Bool,.Vector 2 .U16]
private def tupleValue : Summary :=
  { size := 6, align := some 2,
    fields := [{ ty := .U8, offset := 0, size := 1, align := 1 },{ ty := .Bool, offset := 1, size := 1, align := 1 },
      { ty := .Vector 2 .U16, offset := 2, size := 4, align := 2 }] }

theorem canonical_tuple_keeps_all_child_metadata :
    (left.query .execution tupleTy).map (fun pair => pair.1) = .ok tupleValue ∧
    (right.query .execution tupleTy).map (fun pair => pair.1) = .ok tupleValue := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem canonical_tuple_full_summary_is_unique (first second : Summary) (leftNext rightNext : Session)
    (leftRun : left.query .execution tupleTy = .ok (first,leftNext))
    (rightRun : right.query .execution tupleTy = .ok (second,rightNext)) : first = second :=
  leftHistory.forked_typed_summary rightHistory .execution tupleTy first second leftRun rightRun

private def declaredSource : Environment :=
  { types := [some (.Tuple [.U16,.U8])], hasTargetInfo := true,
    tupleLayouts := [{ tupleType := ⟨0⟩, size := 4, align := 2, fieldOffsets := [0,2] }] }
private def declaredValue : Summary :=
  { size := 4, align := some 2,
    fields := [{ ty := .U16, offset := 0, size := 2, align := 2 },{ ty := .U8, offset := 2, size := 1, align := 1 }] }

theorem declared_tuple_uses_shape_children :
    query declaredSource .execution (.Tuple [.U16,.U8]) = .ok declaredValue ∧
    query declaredSource .shape (.Tuple [.U16,.U8]) = .ok declaredValue := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

private def nominalSource : Environment :=
  { structs := [{ id := ⟨1⟩, name := "first", fields := [{ name := "byte", ty := .U8, offset := some 0 }], size := some 1, align := some 1 },
    { id := ⟨1⟩, name := "matching", fields := [{ name := "word", ty := .U16, offset := some 0 }], size := some 2, align := some 2 }] }

/-- The theorem compares the same mode: duplicate nominal IDs still follow
the different first-definition and matching-position lookup policies. -/
theorem nominal_lookup_modes_are_not_conflated :
    (query nominalSource .shape (.Struct ⟨1⟩)).map Summary.size = .ok 1 ∧
    (query nominalSource .execution (.Struct ⟨1⟩)).map Summary.size = .ok 2 := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem refinement_shape_keeps_original_reference : query source .shape (.Refine ⟨0⟩ ⟨0⟩) = .ok { size := 2, align := some 2 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem refinement_execution_still_refuses :
    query source .execution (.Refine ⟨0⟩ ⟨0⟩) = .error (.unsupported (.Refine ⟨0⟩ ⟨0⟩)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def closureSource : Environment :=
  { closures := [{ ClosureTy.bare ⟨0⟩ with captures := [.U16] }], hasTargetInfo := true,
    closureLayouts := [{ closure := ⟨0⟩, size := 2, align := 2, captureOffsets := [0] }] }

theorem typed_closure_shape_retains_capture_metadata :
    query closureSource .shape (.Closure ⟨0⟩) = .ok
      { size := 2, align := some 2, fields := [{ ty := .U16, offset := 0, size := 2, align := 2 }] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem typed_closure_execution_still_refuses :
    query closureSource .execution (.Closure ⟨0⟩) = .error (.unsupported (.Closure ⟨0⟩)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem unsupported_shape_tuple_still_refuses :
    query source .shape (.Tuple [.U8]) = .error (.unsupported (.Tuple [.U8])) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem invalid_global_tuple_metadata_still_refuses :
    query { tupleLayouts := [{ tupleType := ⟨99⟩, size := 1, align := 1, fieldOffsets := [] }] }
      .execution (.Tuple [.Never]) = .error (.missingType 99) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem cyclic_nested_array_still_refuses :
    query { types := [some (.Array ⟨0⟩ 1)] } .execution (.Vector 3 (.Array ⟨0⟩ 2)) = .error (.cycle 1) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end TypedCorrespondenceControls
namespace PreparedRowControls

private def backward : Environment := { types := [some .U16,some (.Refine ⟨0⟩ ⟨0⟩)] }
private def forward : Environment := { types := [some (.Refine ⟨1⟩ ⟨0⟩),some .U16] }
private def cycleSource : Environment := { types := [some (.Refine ⟨0⟩ ⟨0⟩)] }
private def scalar : Summary := { size := 2, align := some 2 }

theorem backward_row_copies_installed_body :
    (prepare backward).graph.nodes.find ((Index.ofEnvironment backward).node .shape 1) =
      some (.done (.ok scalar)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem forward_row_installs_alias :
    (prepare forward).graph.nodes.find ((Index.ofEnvironment forward).node .shape 0) =
      some (.alias ((Index.ofEnvironment forward).node .shape 1)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem backwardDerived : NodeDerivation (prepare backward).graph
    ((Index.ofEnvironment backward).node .shape 1) scalar := by
  trustIrCompilerProof {
    exact (prepare backward).graph.query_derivation _ _ (by rfl)
  } {
    exact (prepare backward).graph.query_derivation _ _ (by trustIrReduce)
  }

private theorem forwardDerived : NodeDerivation (prepare forward).graph
    ((Index.ofEnvironment forward).node .shape 0) scalar := by
  trustIrCompilerProof {
    exact (prepare forward).graph.query_derivation _ _ (by rfl)
  } {
    exact (prepare forward).graph.query_derivation _ _ (by trustIrReduce)
  }

theorem copied_row_agrees_with_any_actual_query {session next : Session}
    (history : Session.Reachable backward session) (value : Summary)
    (run : session.query .shape (.Refine ⟨0⟩ ⟨0⟩) = .ok (value,next)) : scalar = value :=
  history.prepared_type_summary .shape 1 _ scalar value rfl backwardDerived run

theorem forward_alias_agrees_with_any_actual_query {session next : Session}
    (history : Session.Reachable forward session) (value : Summary)
    (run : session.query .shape (.Refine ⟨1⟩ ⟨0⟩) = .ok (value,next)) : scalar = value :=
  history.prepared_type_summary .shape 0 _ scalar value rfl forwardDerived run

theorem self_alias_still_refuses :
    (prepare cycleSource).query .shape (.Refine ⟨0⟩ ⟨0⟩) = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem cyclic_source_row_has_no_finite_success (value : Summary) :
    ¬ NodeDerivation (prepare cycleSource).graph 0 value := by
  intro derived
  have invariant : (prepare cycleSource).graph.IndexedInvariant (fun node _ => node ≠ 0) := by
    intro node equation found
    by_cases same : node = 0
    · subst node
      rw [show (prepare cycleSource).graph.nodes.find 0 = some (.alias 0) from rfl] at found
      cases found
      exact Equation.IndexedRule.alias 0 0 (fun _ good => good)
    · exact .guarded (fun _ _ _ => same)
  exact (derived.satisfies_at invariant) rfl

private def nominal : Environment :=
  { types := [some (.Struct ⟨7⟩)]
    structs := [{ id := ⟨7⟩, name := "Later", fields := [], size := none, align := none }] }
private def unitValue : Summary := { size := 0, align := some 1 }

theorem execution_row_aliases_later_nominal_definition :
    (prepare nominal).graph.nodes.find ((Index.ofEnvironment nominal).node .execution 0) =
      some (.alias ((Index.ofEnvironment nominal).node .execution 1)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem execution_nominal_row_agrees_with_any_actual_query {session next : Session}
    (history : Session.Reachable nominal session) (value : Summary)
    (run : session.query .execution (.Struct ⟨7⟩) = .ok (value,next)) : unitValue = value := by
  trustIrCompilerProof {
    exact history.prepared_type_summary .execution 0 _ unitValue value rfl
      ((prepare nominal).graph.query_derivation _ _ (by rfl)) run
  } {
    exact history.prepared_type_summary .execution 0 _ unitValue value rfl
      ((prepare nominal).graph.query_derivation _ _ (by trustIrReduce)) run
  }

end PreparedRowControls

namespace CompletionCorrespondenceControls

private def source : Environment := { types := [some .U16] }
private def index : Index := Index.ofEnvironment source
private def early : Graph := { count := 4 }
private def scalar : Summary := { size := 2, align := some 2 }
private def unitEquation : Equation :=
  { kind := .unit, initial := .ok (), steps := [], finish := fun _ => .ok { size := 0, align := some 1 } }
private def original (a b : Nat) : Prop := a = b ∧ a < 4
private def fill (graph : Graph) : Graph :=
  { graph with nodes := (((graph.nodes.insert 0 (.done (.ok scalar))).insert 1 (.done (.ok scalar))).insert 2 unitEquation).insert 3 unitEquation }
private def arrayEquation : Equation := scaled .execution 3 (index.node .execution 0)
private def leftAfter : Graph := { early with nodes := early.nodes.insert 4 arrayEquation, count := 5 }
private def leftAmbient : Graph := fill leftAfter
private def rightBefore : Graph := fill { count := 11 }
private def rightAfter : Graph := { rightBefore with nodes := rightBefore.nodes.insert 11 arrayEquation, count := 12 }

private theorem leftRun : RootCompilation index .execution (.Array ⟨0⟩ 3) early 4 leftAfter := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private theorem rightRun : RootCompilation index .execution (.Array ⟨0⟩ 3) rightBefore 11 rightAfter := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

/-- The ordinary input-correspondence premise is impossible: original slots
are genuinely absent when the first compilation runs. -/
theorem early_original_correspondence_is_unavailable : ¬ early.Correspondence rightBefore original := by
  intro paired
  obtain ⟨leftEquation,rightEquation,found,_,_⟩ := paired 0 0 ⟨rfl,by decide⟩
  cases found

theorem array_compilation_keeps_unfilled_reference : leftAfter.nodes.find 1 = none :=
  leftRun.preserves_reserved (lower := 4) (Graph.Bounded.empty 4) (by decide) 1 (by decide)

private theorem retained : leftAfter.Extends leftAmbient := by
  trustIrCompilerProof {
    let first : Graph := { leftAfter with nodes := leftAfter.nodes.insert 0 (.done (.ok scalar)) }
    let second : Graph := { first with nodes := first.nodes.insert 1 (.done (.ok scalar)) }
    let third : Graph := { second with nodes := second.nodes.insert 2 unitEquation }
    have one : leftAfter.Extends first := Graph.Extends.insert_fresh _ _ _ (by rfl)
    have two : first.Extends second := Graph.Extends.insert_fresh _ _ _ (by rfl)
    have three : second.Extends third := Graph.Extends.insert_fresh _ _ _ (by rfl)
    have four : third.Extends leftAmbient := Graph.Extends.insert_fresh _ _ _ (by rfl)
    exact one.trans (two.trans (three.trans four))
  } {
    let first : Graph := { leftAfter with nodes := leftAfter.nodes.insert 0 (.done (.ok scalar)) }
    let second : Graph := { first with nodes := first.nodes.insert 1 (.done (.ok scalar)) }
    let third : Graph := { second with nodes := second.nodes.insert 2 unitEquation }
    have one : leftAfter.Extends first := Graph.Extends.insert_fresh _ _ _ (by trustIrReduce)
    have two : first.Extends second := Graph.Extends.insert_fresh _ _ _ (by trustIrReduce)
    have three : second.Extends third := Graph.Extends.insert_fresh _ _ _ (by trustIrReduce)
    have four : third.Extends leftAmbient := Graph.Extends.insert_fresh _ _ _ (by trustIrReduce)
    exact one.trans (two.trans (three.trans four))
  }

private theorem rightBounded : rightBefore.Bounded :=
  ((((Graph.Bounded.empty 11).put 0 (by decide) (.done (.ok scalar))).put 1 (by decide) (.done (.ok scalar))).put
    2 (by decide) unitEquation).put 3 (by decide) unitEquation

theorem array_compilation_keeps_installed_originals :
    ∀ node, node < 4 → rightAfter.nodes.find node = rightBefore.nodes.find node :=
  rightRun.preserves_reserved (lower := 4) rightBounded (by decide)

private theorem seed : leftAmbient.Correspondence rightAfter original := by
  intro a b related
  rcases related with ⟨rfl,inside⟩
  have alternatives : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done original (.ok scalar)⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done original (.ok scalar)⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.mk .unit _ _ .nil⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.mk .unit _ _ .nil⟩

private theorem originals : ∀ node, node < 2 * index.count + 2 → original node node := by
  intro node inside
  exact ⟨rfl,inside⟩

/-- Late fills establish the original reference component. The early
compiler output and later compiler root then correspond without recompilation. -/
theorem array_outputs_correspond_after_filling :
    ∃ relation, leftAmbient.Correspondence rightAfter relation ∧ relation 4 11 := by
  obtain ⟨relation,_,paired,roots⟩ := leftRun.corresponds_in_extensions rightRun
    (Graph.Bounded.empty 4) (by decide) (by intro key node found; cases found)
    rightBounded (by decide) (by intro key node found; cases found)
    retained (Graph.Extends.refl rightAfter) seed originals
  exact ⟨relation,paired,roots⟩

private def result : Summary := { size := 6, align := some 2 }

theorem completed_array_queries_succeed : leftAmbient.query 4 = .ok result ∧ rightAfter.query 11 = .ok result := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem completed_array_derivation_transports : NodeDerivation rightAfter 11 result := by
  obtain ⟨relation,paired,roots⟩ := array_outputs_correspond_after_filling
  exact (leftAmbient.query_derivation 4 result completed_array_queries_succeed.1).transport_nodes paired 11 roots

private def clobbered : Graph := { leftAmbient with nodes := leftAmbient.nodes.insert 4 (.done (.error .scalarTarget)) }

theorem replacing_emitted_equation_is_not_an_extension : ¬ leftAfter.Extends clobbered := by
  trustIrCompilerProof {
    intro preserved
    have found := preserved 4 arrayEquation (by rfl)
    have lengths := congrArg (fun (lookup : Option Equation) => lookup.map (fun equation => equation.steps.length)) found
    cases lengths
  } {
    intro preserved
    have found := preserved 4 arrayEquation (by trustIrReduce)
    have lengths := congrArg (fun (lookup : Option Equation) => lookup.map (fun equation => equation.steps.length)) found
    cases lengths
  }

private def completedOriginal : Graph := fill { count := 4 }
private theorem emptyRetained : early.Extends completedOriginal := fun _ _ found => by cases found
private theorem completeBounded : completedOriginal.Bounded :=
  ((((Graph.Bounded.empty 4).put 0 (by decide) (.done (.ok scalar))).put 1 (by decide) (.done (.ok scalar))).put
    2 (by decide) unitEquation).put 3 (by decide) unitEquation
private theorem completedSeed : completedOriginal.Correspondence completedOriginal original := by
  intro a b related
  rcases related with ⟨rfl,inside⟩
  have alternatives : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases alternatives with rfl | rfl | rfl | rfl
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done original (.ok scalar)⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.done original (.ok scalar)⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.mk .unit _ _ .nil⟩
  · exact ⟨_,_,rfl,rfl,Equation.Corresponds.mk .unit _ _ .nil⟩

theorem missing_reference_compiles_before_installation :
    RootCompilation index .shape (.Refine ⟨0⟩ ⟨0⟩) early 0 early ∧ early.nodes.find 0 = none := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem reference_outputs_correspond_after_installation :
    ∃ relation, completedOriginal.Correspondence completedOriginal relation ∧ relation 0 0 := by
  trustIrCompilerProof {
    have later : RootCompilation index .shape (.Refine ⟨0⟩ ⟨0⟩) completedOriginal 0 completedOriginal := rfl
    obtain ⟨relation,_,paired,roots⟩ := missing_reference_compiles_before_installation.1.corresponds_in_extensions later
      (Graph.Bounded.empty 4) (by decide) (by intro key node found; cases found)
      completeBounded (by decide) (by intro key node found; cases found)
      emptyRetained (Graph.Extends.refl completedOriginal) completedSeed originals
    exact ⟨relation,paired,roots⟩
  } {
    have later : RootCompilation index .shape (.Refine ⟨0⟩ ⟨0⟩) completedOriginal 0 completedOriginal := by trustIrReduce
    obtain ⟨relation,_,paired,roots⟩ := missing_reference_compiles_before_installation.1.corresponds_in_extensions later
      (Graph.Bounded.empty 4) (by decide) (by intro key node found; cases found)
      completeBounded (by decide) (by intro key node found; cases found)
      emptyRetained (Graph.Extends.refl completedOriginal) completedSeed originals
    exact ⟨relation,paired,roots⟩
  }

theorem installed_reference_query_succeeds : completedOriginal.query 0 = .ok scalar := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem late_cyclic_reference_remains_a_refusal :
    ({ completedOriginal with nodes := completedOriginal.nodes.insert 0 (.alias 0) } : Graph).query 0 = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end CompletionCorrespondenceControls

end TrustIr.SourceLayout
