-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutArrayOrigin
import TrustIr.Layout.References

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

/-- Closure, unlike equation preservation alone, permits moving a successful
finite derivation back to the original graph. No acyclicity premise is needed. -/
theorem NodeDerivation.restrict_region {before after : Graph} {region : Nat → Prop}
    (growth : before.Extends after) (closed : before.ClosedRegion region)
    {node : Nat} {value : Summary} (derived : NodeDerivation after node value)
    (inside : region node) : NodeDerivation before node value := by
  revert inside
  induction derived using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ => StepsIn region steps → StepsDerivation before steps first last) with
  | equation found initial steps finished transferred =>
    intro member
    obtain ⟨original,lookup,dependencies⟩ := closed _ member
    have same := Option.some.inj ((growth _ _ lookup).symm.trans found)
    cases same
    exact .equation lookup initial (transferred dependencies) finished
  | nil state => exact .nil state
  | check updated later transferred =>
    rename_i dependencies
    exact .check updated (transferred dependencies)
  | child solved updated later childTransferred restTransferred =>
    rename_i dependencies
    exact .child (childTransferred dependencies.1) updated (restTransferred dependencies.2)

/-- Independently grown graphs agree on a closed original region even when
new allocations outside it collide and the extensions disagree elsewhere. -/
theorem NodeDerivation.closed_region_agrees {base left right : Graph} {region : Nat → Prop}
    (closed : base.ClosedRegion region) (leftGrowth : base.Extends left) (rightGrowth : base.Extends right)
    {node : Nat} (inside : region node) {first second : Summary}
    (leftRun : NodeDerivation left node first) (rightRun : NodeDerivation right node second) : first = second :=
  ((leftRun.restrict_region leftGrowth closed inside).weaken rightGrowth).functional _ rightRun

/-- A derivation in an actual source history can be retracted to preparation
when the original source dependency region is closed. -/
theorem Session.Reachable.prepared_region_derivation {source : Environment} {session : Session}
    (history : Session.Reachable source session) {region : Nat → Prop}
    (closed : (prepare source).graph.ClosedRegion region) {node : Nat} (inside : region node)
    {value : Summary} (derived : NodeDerivation session.graph node value) :
    NodeDerivation (prepare source).graph node value :=
  derived.restrict_region history.extends_prepared closed inside

/-- Valid memos from independently reached sessions agree on the original
closed region, without requiring global agreement of their fresh equations. -/
theorem Session.Reachable.forked_region_memo_agrees {source : Environment} {left right : Session}
    (leftHistory : Session.Reachable source left) (rightHistory : Session.Reachable source right)
    {region : Nat → Prop} (closed : (prepare source).graph.ClosedRegion region)
    {node : Nat} (inside : region node) {first second : Summary}
    (leftCached : left.memo.find node = some first) (rightCached : right.memo.find node = some second) :
    first = second :=
  (leftHistory.prepared_region_derivation closed inside (leftHistory.cached node first leftCached)).functional _
    (rightHistory.prepared_region_derivation closed inside (rightHistory.cached node second rightCached))

/-- Separate actual array-query histories share an original child summary
under source dependency closure. Neither history must continue the other. -/
theorem Session.Reachable.forked_array_scaling {source : Environment}
    {left leftNext right rightNext : Session} (leftHistory : Session.Reachable source left)
    (rightHistory : Session.Reachable source right) (mode : Mode) (id : TyId)
    (leftCount rightCount : Nat) (leftValue rightValue : Summary)
    (leftRun : left.query mode (.Array id leftCount) = .ok (leftValue,leftNext))
    (rightRun : right.query mode (.Array id rightCount) = .ok (rightValue,rightNext))
    {region : Nat → Prop} (closed : (prepare source).graph.ClosedRegion region)
    (inside : region ((Index.ofEnvironment source).node mode id.index)) :
    ∃ child : Summary, NodeDerivation (prepare source).graph
      ((Index.ofEnvironment source).node mode id.index) child ∧
      leftValue.size = child.size * leftCount ∧ rightValue.size = child.size * rightCount ∧
      leftValue.align = child.align ∧ rightValue.align = child.align := by
  obtain ⟨_,child,_,derived,size,align⟩ := leftHistory.query_array_child mode id leftCount leftValue leftRun
  obtain ⟨_,other,_,otherDerived,otherSize,otherAlign⟩ :=
    rightHistory.query_array_child mode id rightCount rightValue rightRun
  have first := (Session.Reachable.queried leftHistory leftRun).prepared_region_derivation closed inside derived
  have second := (Session.Reachable.queried rightHistory rightRun).prepared_region_derivation closed inside otherDerived
  have same := first.functional _ second
  cases same
  exact ⟨child,first,size,otherSize,align,otherAlign⟩

namespace ClosedRegionControls
private def value : Summary := { size := 2, align := some 2 }
private def source : Environment := { types := [some .U16] }
private def region (node : Nat) : Prop := node = 1

/-- The closure certificate is checked against the actual prepared source graph. -/
theorem actual_prepared_scalar_region : (prepare source).graph.ClosedRegion region := by
  trustIrCompilerProof {
    intro node inside
    change node = 1 at inside
    subst node
    exact ⟨.done (.ok value),rfl,True.intro⟩
  } {
    intro node inside
    change node = 1 at inside
    subst node
    exact ⟨.done (.ok value),(by trustIrReduce),True.intro⟩
  }

/-- The two successful queries branch directly from preparation. -/
theorem actual_forked_arrays :
    ∃ child : Summary, NodeDerivation (prepare source).graph 1 child ∧
      6 = child.size * 3 ∧ 10 = child.size * 5 ∧ some 2 = child.align ∧ some 2 = child.align := by
  trustIrCompilerProof {
    exact Session.Reachable.forked_array_scaling (source := source)
      (leftNext := (((prepare source).query .execution (.Array ⟨0⟩ 3)).toOption.getD (value,prepare source)).2)
      (rightNext := (((prepare source).query .execution (.Array ⟨0⟩ 5)).toOption.getD (value,prepare source)).2)
      .prepared .prepared .execution ⟨0⟩ 3 5 { size := 6, align := some 2 } { size := 10, align := some 2 }
      (by rfl) (by rfl) actual_prepared_scalar_region rfl
  } {
    exact Session.Reachable.forked_array_scaling (source := source)
      (leftNext := (((prepare source).query .execution (.Array ⟨0⟩ 3)).toOption.getD (value,prepare source)).2)
      (rightNext := (((prepare source).query .execution (.Array ⟨0⟩ 5)).toOption.getD (value,prepare source)).2)
      .prepared .prepared .execution ⟨0⟩ 3 5 { size := 6, align := some 2 } { size := 10, align := some 2 }
      (by trustIrReduce) (by trustIrReduce) actual_prepared_scalar_region rfl
  }

private def leftFork : Session :=
  (((prepare source).query .execution (.Array ⟨0⟩ 3)).toOption.getD (value,prepare source)).2
private def rightFork : Session :=
  (((prepare source).query .execution (.Array ⟨0⟩ 5)).toOption.getD (value,prepare source)).2

/-- Fresh root slots really collide with different results outside the closed
source region, so global graph equality/extension is unavailable. -/
theorem actual_forks_not_extensions : ¬ leftFork.graph.Extends rightFork.graph := by
  trustIrCompilerProof {
    intro growth
    have left : NodeDerivation leftFork.graph 5 { size := 6, align := some 2 } :=
      Graph.query_derivation _ _ _ (by rfl)
    have right : NodeDerivation rightFork.graph 5 { size := 10, align := some 2 } :=
      Graph.query_derivation _ _ _ (by rfl)
    have impossible := congrArg Summary.size (left.unique_after_growth growth right)
    cases impossible
  } {
    intro growth
    have left : NodeDerivation leftFork.graph 5 { size := 6, align := some 2 } :=
      Graph.query_derivation _ _ _ (by trustIrReduce)
    have right : NodeDerivation rightFork.graph 5 { size := 10, align := some 2 } :=
      Graph.query_derivation _ _ _ (by trustIrReduce)
    have impossible := congrArg Summary.size (left.unique_after_growth growth right)
    cases impossible
  }

private def nestedSource : Environment := { types := [some (.Array ⟨1⟩ 3),some .U16] }
private def nestedRegion (node : Nat) : Prop := node = 2 ∨ node = 3

theorem actual_prepared_array_region : (prepare nestedSource).graph.ClosedRegion nestedRegion := by
  trustIrCompilerProof {
    intro node inside
    rcases inside with rfl | rfl
    · exact ⟨scaled .execution 3 3,rfl,⟨Or.inr rfl,True.intro⟩⟩
    · exact ⟨.done (.ok value),rfl,True.intro⟩
  } {
    intro node inside
    rcases inside with rfl | rfl
    · exact ⟨scaled .execution 3 3,(by trustIrReduce),⟨Or.inr rfl,True.intro⟩⟩
    · exact ⟨.done (.ok value),(by trustIrReduce),True.intro⟩
  }

/-- The closed source component includes a real array dependency, not just a
leaf; independently compiled outer arrays retain its six-byte child. -/
theorem actual_forked_nested_arrays :
    ∃ child : Summary, NodeDerivation (prepare nestedSource).graph 2 child ∧
      12 = child.size * 2 ∧ 30 = child.size * 5 ∧ some 2 = child.align ∧ some 2 = child.align := by
  trustIrCompilerProof {
    exact Session.Reachable.forked_array_scaling (source := nestedSource)
      (leftNext := (((prepare nestedSource).query .execution (.Array ⟨0⟩ 2)).toOption.getD (value,prepare nestedSource)).2)
      (rightNext := (((prepare nestedSource).query .execution (.Array ⟨0⟩ 5)).toOption.getD (value,prepare nestedSource)).2)
      .prepared .prepared .execution ⟨0⟩ 2 5 { size := 12, align := some 2 } { size := 30, align := some 2 }
      (by rfl) (by rfl) actual_prepared_array_region (Or.inl rfl)
  } {
    exact Session.Reachable.forked_array_scaling (source := nestedSource)
      (leftNext := (((prepare nestedSource).query .execution (.Array ⟨0⟩ 2)).toOption.getD (value,prepare nestedSource)).2)
      (rightNext := (((prepare nestedSource).query .execution (.Array ⟨0⟩ 5)).toOption.getD (value,prepare nestedSource)).2)
      .prepared .prepared .execution ⟨0⟩ 2 5 { size := 12, align := some 2 } { size := 30, align := some 2 }
      (by trustIrReduce) (by trustIrReduce) actual_prepared_array_region (Or.inl rfl)
  }

private def openGraph : Graph := { nodes := NatIndexTree.empty.insert 0 (.alias 1), count := 1 }
private def filled : Graph := { openGraph with nodes := openGraph.nodes.insert 1 (.done (.ok value)), count := 2 }

theorem missing_dependency_can_be_added : openGraph.Extends filled :=
  Graph.Extends.allocate (by
    intro node outside
    change 1 ≤ node at outside
    change (NatIndexTree.empty.insert 0 (Equation.alias 1)).find node = none
    rw [NatIndexTree.find_insert,if_neg (by omega : node ≠ 0)]
    rfl) _

theorem original_missing_dependency_refuses : openGraph.query 0 = .error (.cycle 1) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem extension_fills_dependency : filled.query 0 = .ok value := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- Exact preservation alone cannot support backwards transport. -/
theorem original_has_no_derivation : ¬ NodeDerivation openGraph 0 value := by
  intro derived
  have run := derived.execution (by rfl : openGraph.nodes.find 0 = some (.alias 1))
  obtain ⟨first,last,initial,steps,finished⟩ := run
  cases steps with
  | child solved updated later =>
    have present := solved.present
    change false = true at present
    cases present

theorem open_region_is_not_closed : ¬ openGraph.ClosedRegion (fun node => node = 0 ∨ node = 1) := by
  intro closed
  obtain ⟨equation,found,_⟩ := closed 1 (Or.inr rfl)
  change none = some equation at found
  cases found

private def cyclic : Graph :=
  { nodes := (NatIndexTree.empty.insert 0 (.alias 1)).insert 1 (.alias 0), count := 2 }

/-- Closure admits cycles; it does not assert the existence of successful derivations. -/
theorem cycle_is_closed : cyclic.ClosedRegion (fun node => node = 0 ∨ node = 1) := by
  intro node inside
  rcases inside with rfl | rfl
  · exact ⟨.alias 1,by rfl,⟨Or.inr rfl,True.intro⟩⟩
  · exact ⟨.alias 0,by rfl,⟨Or.inl rfl,True.intro⟩⟩

theorem closed_cycle_refuses : cyclic.query 0 = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

end ClosedRegionControls
end TrustIr.SourceLayout
