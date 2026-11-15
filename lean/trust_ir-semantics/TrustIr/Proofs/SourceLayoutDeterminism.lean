-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutSession

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

/-- Finite successful derivations of one actual graph node are unique, even
when the graph contains forward references or cycles. No solver/cache oracle
or acyclicity assumption is used. -/
theorem NodeDerivation.functional {graph : Graph} {node : Nat} {value : Summary}
    (left : NodeDerivation graph node value) :
    ∀ other, NodeDerivation graph node other → value = other := by
  induction left using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ =>
      ∀ other, StepsDerivation graph steps first other → last = other) with
  | equation found initial steps finished unique =>
    intro other right
    cases right with
    | equation otherFound otherInitial otherSteps otherFinished =>
      have equationEq := Option.some.inj (found.symm.trans otherFound)
      cases equationEq
      have initialEq := Except.ok.inj (initial.symm.trans otherInitial)
      cases initialEq
      have finalEq := unique _ otherSteps
      cases finalEq
      exact Except.ok.inj (finished.symm.trans otherFinished)
  | nil state =>
    rename_i other right
    cases right
    rfl
  | check updated later unique =>
    rename_i other right
    cases right with
    | check otherUpdated otherLater =>
      have same := Except.ok.inj (updated.symm.trans otherUpdated)
      cases same
      exact unique _ otherLater
  | child solved updated later childUnique restUnique =>
    rename_i other right
    cases right with
    | child otherSolved otherUpdated otherLater =>
      have sameChild := childUnique _ otherSolved
      cases sameChild
      have same := Except.ok.inj (updated.symm.trans otherUpdated)
      cases same
      exact restUnique _ otherLater

/-- Ordered equation updates have a unique successful final state when child
requests use the same exact graph. -/
theorem StepsDerivation.functional {graph : Graph} {σ : Type} {steps : List (Step σ)}
    {first last other : σ} (left : StepsDerivation graph steps first last)
    (right : StepsDerivation graph steps first other) : last = other := by
  induction steps generalizing first last other with
  | nil => cases left; cases right; rfl
  | cons step rest ih =>
    cases step with
    | check update =>
      cases left with
      | check updated later =>
        cases right with
        | check otherUpdated otherLater =>
          have same := Except.ok.inj (updated.symm.trans otherUpdated)
          cases same
          exact ih later otherLater
    | child node update =>
      cases left with
      | child solved updated later =>
        cases right with
        | child otherSolved otherUpdated otherLater =>
          have sameChild := solved.functional _ otherSolved
          cases sameChild
          have same := Except.ok.inj (updated.symm.trans otherUpdated)
          cases same
          exact ih later otherLater

/-- An equation body has a unique successful result in a fixed graph. -/
theorem Equation.Executes.functional {graph : Graph} {equation : Equation}
    {left right : Summary} (first : equation.Executes graph left)
    (second : equation.Executes graph right) : left = right := by
  obtain ⟨initial,final,started,steps,finished⟩ := first
  obtain ⟨otherInitial,otherFinal,otherStarted,otherSteps,otherFinished⟩ := second
  have initialEq := Except.ok.inj (started.symm.trans otherStarted)
  cases initialEq
  have finalEq := steps.functional otherSteps
  cases finalEq
  exact Except.ok.inj (finished.symm.trans otherFinished)

/-- Exact preservation of equations preserves every old result: a newly
obtained derivation at an old node cannot silently change its summary. -/
theorem NodeDerivation.unique_after_growth {before after : Graph}
    (growth : before.Extends after) {node : Nat} {old current : Summary}
    (derived : NodeDerivation before node old) (later : NodeDerivation after node current) :
    old = current :=
  (derived.weaken growth).functional _ later

/-- The actual array/vector scaling equation retains its derived child's
size and alignment and multiplies size by the exact logical count. -/
theorem Equation.Executes.scaled_extent {graph : Graph} (mode : Mode) (count child : Nat)
    {value : Summary} (run : (scaled mode count child).Executes graph value) :
    ∃ input, NodeDerivation graph child input ∧ value.size = input.size * count ∧
      value.align = input.align := by
  obtain ⟨first,last,initial,steps,finished⟩ := run
  cases steps with
  | child solved updated later =>
    cases later
    cases finished
    dsimp only at updated
    unfold checked at updated
    split at updated
    · simp only [Bind.bind,Except.bind] at updated
      have result := (finish_ok_iff mode _ _).mp updated
      cases result.1
      exact ⟨_,solved,rfl,rfl⟩
    · cases updated

/-- A scaling equation cannot disagree with an earlier valid memo observation
of its child after exact graph growth. This is an equation-level product law,
not yet correspondence of independently compiled roots for a source type. -/
theorem Equation.Executes.scaled_prior_child {before after : Graph} {memo : Memo}
    (growth : before.Extends after) (valid : MemoDerivation before memo)
    (mode : Mode) (count child : Nat) (input output : Summary)
    (cached : memo.find child = some input)
    (run : (scaled mode count child).Executes after output) :
    output.size = input.size * count ∧ output.align = input.align := by
  obtain ⟨current,derived,size,align⟩ := run.scaled_extent mode count child
  have same := (valid child input cached).unique_after_growth growth derived
  cases same
  exact ⟨size,align⟩

/-- A finite actual sequence of successful layout queries, starting at an
existing session rather than silently resetting it to a fresh source. -/
inductive Session.QueryChain : Session → Session → Prop where
  | refl (session : Session) : QueryChain session session
  | queried {first current next : Session} (chain : QueryChain first current)
      (mode : Mode) (ty : Ty) (value : Summary)
      (run : current.query mode ty = .ok (value,next)) : QueryChain first next

/-- A real query chain retains its original source association. -/
theorem Session.QueryChain.reachable {source : Environment} {first last : Session}
    (chain : Session.QueryChain first last) (history : Session.Reachable source first) :
    Session.Reachable source last := by
  induction chain with
  | refl => exact history
  | queried chain mode ty value run ih => exact .queried ih run

/-- Existing node equations survive every query in an actual finite chain. -/
theorem Session.QueryChain.graph_extends {source : Environment} {first last : Session}
    (chain : Session.QueryChain first last) (history : Session.Reachable source first) :
    first.graph.Extends last.graph := by
  induction chain with
  | refl => exact Graph.Extends.refl _
  | queried chain mode ty value run ih =>
    exact ih.trans (Session.query_preserves_derivation _ _ _ _ _
      (chain.reachable history).invariant run).2.2.1.equations

/-- Two actual valid memo observations of an old node cannot disagree after
any sequence of successful queries, across modes, types and root buckets. -/
theorem Session.QueryChain.memo_agrees {source : Environment} {first last : Session}
    (chain : Session.QueryChain first last) (history : Session.Reachable source first)
    (node : Nat) (old current : Summary)
    (earlier : first.memo.find node = some old) (later : last.memo.find node = some current) :
    old = current :=
  (history.cached node old earlier).unique_after_growth (chain.graph_extends history)
    ((chain.reachable history).cached node current later)

/-- Actual query selection supplies the precise typed root and returned
summary. If that root already had a valid old memo entry, it must agree. -/
theorem Session.QueryChain.query_agrees_with_prior_memo {source : Environment}
    {first current next : Session} (chain : Session.QueryChain first current)
    (history : Session.Reachable source first) (mode : Mode) (ty : Ty) (value : Summary)
    (run : current.query mode ty = .ok (value,next)) :
    ∃ root, Session.CompiledRoot source mode ty root next.graph ∧
      ∀ old, first.memo.find root = some old → old = value := by
  obtain ⟨root,origin,derived⟩ := (chain.reachable history).query_compilation_origin mode ty value run
  refine ⟨root,origin,?_⟩
  intro old cached
  exact (history.cached root old cached).unique_after_growth
    ((Session.QueryChain.queried chain mode ty value run).graph_extends history) derived

end TrustIr.SourceLayout


namespace TrustIr.SourceLayout.DeterminismControls

private def one : Summary := { size := 1, align := some 1 }
private def five : Summary := { size := 5, align := some 1 }
private def nine : Summary := { size := 9, align := some 1 }
private def eleven : Summary := { size := 11, align := some 1 }
private def base : Graph := { count := 1, nodes := NatIndexTree.empty.insert 0 (.done (.ok one)) }
private def grown : Graph := { count := 2, nodes := base.nodes.insert 1 (.done (.ok nine)) }
private def rewritten : Graph := { count := 1, nodes := NatIndexTree.empty.insert 0 (.done (.ok nine)) }
private def forward : Graph := { count := 2, nodes :=
  (NatIndexTree.empty.insert 1 (.done (.ok five))).insert 0 (.alias 1) }
private def cycle : Graph := { count := 1, nodes := NatIndexTree.empty.insert 0 (.alias 0) }
private def forged : Memo := NatIndexTree.empty.insert 0 nine
private def orderedEquation : Equation :=
  { kind := .placements
    initial := .ok { cursor := 3 }
    steps := [.check (fun state => .ok { state with cursor := state.cursor * 2 }),
      .child 1 (fun summary state => .ok { state with cursor := state.cursor + summary.size })]
    finish := fun state => .ok { size := state.cursor, align := some 1 } }
private def ordered : Graph := { count := 2, nodes :=
  (NatIndexTree.empty.insert 1 (.done (.ok five))).insert 0 orderedEquation }

/-- A forward reference has a real finite result despite non-topological slots. -/
theorem actual_forward_query : forward.query 0 = .ok five := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- The actual solver rejects the cyclic request; determinism does not assert
existence or termination of a successful derivation for every graph. -/
theorem actual_cycle_refuses : cycle.query 0 = .error (.cycle 0) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- Ordered heterogeneous updates use a PlacementState and a Summary child. -/
theorem actual_ordered_query : ordered.query 0 = .ok eleven := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem ordered_result_unique (value : Summary) (derived : NodeDerivation ordered 0 value) :
    value = eleven :=
  (ordered.query_derivation 0 eleven actual_ordered_query).functional value derived |>.symm

theorem unrelated_graph_growth_preserves_query : base.query 0 = .ok one ∧ grown.query 0 = .ok one := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

/-- Replacing an old equation can change its result and is not graph growth. -/
theorem rewritten_equation_is_not_growth : ¬ base.Extends rewritten := by
  trustIrCompilerProof {
    intro growth
    have same := (base.query_derivation 0 one (by rfl)).unique_after_growth growth
      (rewritten.query_derivation 0 nine (by rfl))
    have sizes := congrArg Summary.size same
    cases sizes
  } {
    intro growth
    have same := (base.query_derivation 0 one (by trustIrReduce)).unique_after_growth growth
      (rewritten.query_derivation 0 nine (by trustIrReduce))
    have sizes := congrArg Summary.size same
    cases sizes
  }

/-- Arbitrary low-level memo injection is an actual counterexample without
memo validity; the real reachable-session invariant is substantive. -/
theorem forged_cache_returns_wrong_result : solve base .empty 0 forged = .ok (nine,forged) := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem forged_cache_is_invalid : ¬ MemoDerivation base forged := by
  trustIrCompilerProof {
    intro valid
    have same := (base.query_derivation 0 one (by rfl)).functional nine (valid 0 nine (by rfl))
    have sizes := congrArg Summary.size same
    cases sizes
  } {
    intro valid
    have same := (base.query_derivation 0 one (by trustIrReduce)).functional nine (valid 0 nine (by trustIrReduce))
    have sizes := congrArg Summary.size same
    cases sizes
  }

private def source : Environment := {}
private def first : Session := (((prepare source).query .execution .U8).toOption.getD (one,prepare source)).2
private def second : Session := ((first.query .shape .U16).toOption.getD (one,first)).2
private def third : Session := ((second.query .execution .U8).toOption.getD (one,second)).2

/-- A real query sequence crosses mode/type queries and returns to its old root. -/
theorem actual_source_query_chain : Session.QueryChain (prepare source) third := by
  trustIrCompilerProof {
    exact .queried (.queried (.queried (.refl _) .execution .U8 one (by rfl))
      .shape .U16 { size := 2, align := some 2 } (by rfl)) .execution .U8 one (by rfl)
  } {
    exact .queried (.queried (.queried (.refl _) .execution .U8 one (by trustIrReduce))
      .shape .U16 { size := 2, align := some 2 } (by trustIrReduce)) .execution .U8 one (by trustIrReduce)
  }

theorem actual_repeat_result : (second.query .execution .U8).map (fun pair => pair.1) = .ok one := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

private def scaledGraph (count : Nat) : Graph :=
  { count := 2, nodes := (NatIndexTree.empty.insert 1 (.done (.ok five))).insert 0 (scaled .execution count 1) }

theorem actual_scaled_product : (scaledGraph 3).query 0 = .ok { size := 15, align := some 1 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_zero_count_product : (scaledGraph 0).query 0 = .ok { size := 0, align := some 1 } := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

theorem actual_seed_memo : first.memo.find 2 = some one := by
  trustIrCompilerProof {
    exact rfl
  } {
    trustIrReduce
  }

/-- The source-owned chain, original nonempty memo and selected typed query
are used by the general result; the cache premise is not fabricated. -/
theorem actual_typed_query_prior_memo :
    ∃ root, Session.CompiledRoot source .execution .U8 root third.graph ∧
      ∀ old, first.memo.find root = some old → old = one := by
  trustIrCompilerProof {
    have firstHistory : Session.Reachable source first :=
      .queried (mode := .execution) (ty := .U8) (value := one) .prepared (by rfl)
    have suffix : Session.QueryChain first second :=
      .queried (.refl _) .shape .U16 { size := 2, align := some 2 } (by rfl)
    exact suffix.query_agrees_with_prior_memo firstHistory .execution .U8 one (by rfl)
  } {
    have firstHistory : Session.Reachable source first :=
      .queried (mode := .execution) (ty := .U8) (value := one) .prepared (by trustIrReduce)
    have suffix : Session.QueryChain first second :=
      .queried (.refl _) .shape .U16 { size := 2, align := some 2 } (by trustIrReduce)
    exact suffix.query_agrees_with_prior_memo firstHistory .execution .U8 one (by trustIrReduce)
  }

end TrustIr.SourceLayout.DeterminismControls
