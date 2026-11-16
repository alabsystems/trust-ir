-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Schema
import TrustIr.Layout.Available

namespace TrustIr.SourceLayout

structure PlacementState where
  cursor : Nat := 0
  align : Nat := 1
  fields : List Field := []

/-- Internal typed accumulators. This is an implementation language for
    source equations; it adds no TrustIr value or admissible IR type. -/
inductive Accumulator where
  | summary
  | placements
  | variants
  | unit
  | deferred (inner : Accumulator)

def Accumulator.State : Accumulator → Type
  | .summary => Summary
  | .placements => PlacementState
  | .variants => List Summary
  | .unit => Unit
  | .deferred inner => Except Error inner.State

inductive Step (σ : Type) where
  | check (update : σ → Except Error σ)
  | child (node : Nat) (update : Summary → σ → Except Error σ)

/-- Typed first-order source equations. Dependencies form an actual finite
    list; checks run in place before requesting later fields. State types are
    internal typed accumulators, not an untrusted value/type representation. -/
structure Equation where
  kind : Accumulator
  initial : Except Error kind.State
  steps : List (Step kind.State)
  finish : kind.State → Except Error Summary

abbrev Equation.State (equation : Equation) : Type := equation.kind.State

namespace Equation

def done (result : Except Error Summary) : Equation :=
  { kind := .summary, initial := result, steps := [], finish := Except.ok }

def alias (child : Nat) : Equation :=
  { kind := .summary, initial := .ok { size := 0, align := none },
    steps := [.child child fun value _ => .ok value], finish := Except.ok }

private def liftStep {σ : Type} : Step σ → Step (Except Error σ)
  | .check update => .check fun stored => do pure (.ok (← update (← stored)))
  | .child child update => .child child fun value stored => do pure (.ok (← update value (← stored)))

/-- Prefix requests precede even the next equation's initial refusal. -/
def sequence (children : List Nat) (next : Equation) : Equation :=
  { kind := .deferred next.kind, initial := .ok next.initial,
    steps := (children.map (fun child => .child child fun _ state => .ok state)) ++
      [.check fun state => do let _ ← state; pure state] ++ next.steps.map liftStep,
    finish := fun stored => do next.finish (← stored) }

end Equation

structure Graph where
  nodes : NatIndexTree Equation := .empty
  count : Nat := 0
  /-- Interned scalar byte summaries; never type or value identity. -/
  leaves : NatIndexTree Nat := .empty

abbrev Memo := NatIndexTree Summary

/- Finite logical execution of the actual equation graph. Cached values
must carry the same derivation as newly evaluated values. No execution fuel or
layout oracle is introduced. -/
mutual
  inductive NodeDerivation (graph : Graph) : Nat → Summary → Prop where
    | equation {node : Nat} {equation : Equation} {first last : equation.State}
        {value : Summary}
        (found : graph.nodes.find node = some equation)
        (initial : equation.initial = .ok first)
        (steps : StepsDerivation graph equation.steps first last)
        (finished : equation.finish last = .ok value) : NodeDerivation graph node value
  inductive StepsDerivation (graph : Graph) : {σ : Type} → List (Step σ) → σ → σ → Prop where
    | nil {σ : Type} (state : σ) : StepsDerivation graph [] state state
    | check {σ : Type} {update : σ → Except Error σ} {rest : List (Step σ)}
        {first next last : σ}
        (updated : update first = .ok next)
        (later : StepsDerivation graph rest next last) :
        StepsDerivation graph (.check update :: rest) first last
    | child {σ : Type} {node : Nat} {value : Summary}
        {update : Summary → σ → Except Error σ} {rest : List (Step σ)}
        {first next last : σ}
        (solved : NodeDerivation graph node value)
        (updated : update value first = .ok next)
        (later : StepsDerivation graph rest next last) :
        StepsDerivation graph (.child node update :: rest) first last
end

/-- Finite execution of one equation body, independently of its graph slot.
Child requests still require derivations in the exact graph. -/
def Equation.Executes (graph : Graph) (equation : Equation) (value : Summary) : Prop :=
  ∃ first last, equation.initial = .ok first ∧
    StepsDerivation graph equation.steps first last ∧ equation.finish last = .ok value

theorem NodeDerivation.execution {graph : Graph} {node : Nat} {value : Summary}
    {equation : Equation} (found : graph.nodes.find node = some equation)
    (derived : NodeDerivation graph node value) : equation.Executes graph value := by
  cases derived with
  | equation lookup initial steps finished =>
    rw [found] at lookup
    cases lookup
    exact ⟨_, _, initial, steps, finished⟩

theorem Equation.Executes.to_node {graph : Graph} {node : Nat} {value : Summary}
    {equation : Equation} (run : equation.Executes graph value)
    (found : graph.nodes.find node = some equation) : NodeDerivation graph node value := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact .equation found initial steps finished

private theorem StepsDerivation.ignore_prefix {graph : Graph} {σ : Type}
    (children : List Nat) (rest : List (Step σ)) (first last : σ)
    (run : StepsDerivation graph
      (children.map (fun child => .child child fun _ state => .ok state) ++ rest) first last) :
    StepsDerivation graph rest first last := by
  induction children with
  | nil => exact run
  | cons child children ih =>
    cases run with
    | child solved updated later =>
      cases updated
      exact ih later

private theorem StepsDerivation.unlift {graph : Graph} {σ : Type}
    (steps : List (Step σ)) (first : σ) (stored : Except Error σ)
    (run : StepsDerivation graph (steps.map Equation.liftStep) (.ok first) stored) :
    ∃ last, stored = .ok last ∧ StepsDerivation graph steps first last := by
  induction steps generalizing first stored with
  | nil =>
    cases run
    exact ⟨first, rfl, .nil first⟩
  | cons step rest ih =>
    cases step with
    | check update =>
      cases run with
      | check updated later =>
        dsimp only [Equation.liftStep] at updated
        cases hu : update first with
        | error error => simp [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
        | ok next =>
          simp only [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
          cases updated
          rcases ih next _ later with ⟨last, same, original⟩
          exact ⟨last, same, .check hu original⟩
    | child node update =>
      cases run with
      | child solved updated later =>
        dsimp only [Equation.liftStep] at updated
        rename_i value next
        cases hu : update value first with
        | error error => simp [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
        | ok next =>
          simp only [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
          cases updated
          rcases ih next _ later with ⟨last, same, original⟩
          exact ⟨last, same, .child solved hu original⟩

/-- Sequencing preserves the executed body's exact value and child derivations;
prefix dependencies cannot substitute a result for that body. -/
theorem Equation.Executes.sequence_body {graph : Graph} {children : List Nat}
    {next : Equation} {value : Summary}
    (run : (Equation.sequence children next).Executes graph value) :
    next.Executes graph value := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial
  simp only [Equation.sequence, Accumulator.State, List.append_assoc] at steps
  have body := StepsDerivation.ignore_prefix children _ _ _ steps
  cases body with
  | check updated later =>
    cases hi : next.initial with
    | error error => simp [hi, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
    | ok state =>
      simp only [hi, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
      cases updated
      rcases StepsDerivation.unlift next.steps state last later with ⟨final, same, original⟩
      subst last
      exact ⟨state, final, hi, original, finished⟩

/-- Aliases return precisely a derivation of their requested child. -/
theorem Equation.Executes.alias_child {graph : Graph} {child : Nat} {value : Summary}
    (run : (Equation.alias child).Executes graph value) : NodeDerivation graph child value := by
  rcases run with ⟨first, last, _initial, steps, finished⟩
  cases steps with
  | child solved updated later =>
    cases later
    cases updated
    cases finished
    exact solved

/-- Every cache hit has a finite derivation in this exact graph. -/
def MemoDerivation (graph : Graph) (memo : Memo) : Prop :=
  ∀ node value, memo.find node = some value → NodeDerivation graph node value

theorem MemoDerivation.empty (graph : Graph) : MemoDerivation graph .empty := by
  intro node value found
  cases found

theorem MemoDerivation.insert {graph : Graph} {memo : Memo}
    (valid : MemoDerivation graph memo) {node : Nat} {value : Summary}
    (derived : NodeDerivation graph node value) :
    MemoDerivation graph (memo.insert node value) := by
  intro query result found
  rw [NatIndexTree.find_insert] at found
  by_cases same : query = node
  · subst query
    simp only [ite_true, Option.some.injEq] at found
    subst result
    exact derived
  · rw [if_neg same] at found
    exact valid query result found

/-- List removal is used only by the separate uninhabitedness fixed point. -/
theorem erase_length_lt (xs : List Nat) (key : Nat) (present : key ∈ xs) :
    (xs.erase key).length < xs.length := by
  trustIrCompilerProof {
    induction xs with
    | nil => cases present
    | cons head tail ih =>
      by_cases equal : head = key
      · subst head; simp [List.erase]
      · have rest : key ∈ tail := by simpa [List.mem_cons, equal, Ne.symm equal] using present
        have distinct : (head == key) = false := by
          first | exact (beq_eq_false_iff_ne head key).mpr equal | exact beq_eq_false_iff_ne.mpr equal
        simp only [List.erase, distinct, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact Nat.succ_lt_succ (ih rest)
  } {
    induction xs with
    | nil => cases present
    | cons head tail ih =>
      cases Nat.decEq head key with
      | isTrue equal =>
        subst head
        have self : (key == key) = true := decide_eq_true rfl
        simp only [List.erase, self, ↓reduceIte, List.length_cons]
        exact Nat.lt_succ_self _
      | isFalse equal =>
        have rest : key ∈ tail := by
          cases present with
          | head => exact False.elim (equal rfl)
          | tail _ member => exact member
        have distinct : (head == key) = false := by
          change decide (head = key) = false
          exact Bool.eq_false_iff.mpr (fun same => equal (of_decide_eq_true same))
        simp only [List.erase, distinct, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact Nat.succ_lt_succ (ih rest)
  }

private structure Frame where
  owner : Nat
  equation : Equation
  update : Summary → equation.State → Except Error equation.State

private def savedSteps : List Frame → Nat
  | [] => 0
  | frame :: rest => frame.equation.steps.length + 1 + savedSteps rest

/-- A consumed prefix turns any derivation of the remaining equation into
    a derivation of its original graph node. -/
private def EquationReady (graph : Graph) (owner : Nat) (equation : Equation) : Prop :=
  ∀ first last value, equation.initial = .ok first →
    StepsDerivation graph equation.steps first last →
    equation.finish last = .ok value → NodeDerivation graph owner value

private theorem EquationReady.fresh {graph : Graph} {owner : Nat} {equation : Equation}
    (found : graph.nodes.find owner = some equation) : EquationReady graph owner equation := by
  intro first last value initial steps finished
  exact .equation found initial steps finished

private theorem EquationReady.check {graph : Graph} {owner : Nat} {equation : Equation}
    {state next : equation.State} {update : equation.State → Except Error equation.State}
    {rest : List (Step equation.State)}
    (ready : EquationReady graph owner equation) (initial : equation.initial = .ok state)
    (steps : equation.steps = .check update :: rest) (updated : update state = .ok next) :
    EquationReady graph owner { equation with initial := .ok next, steps := rest } := by
  intro first last value start later finished
  cases start
  apply ready state last value initial
  · rw [steps]
    exact .check updated later
  · exact finished

private theorem EquationReady.child {graph : Graph} {owner child : Nat} {equation : Equation}
    {state next : equation.State} {value : Summary}
    {update : Summary → equation.State → Except Error equation.State}
    {rest : List (Step equation.State)}
    (ready : EquationReady graph owner equation) (initial : equation.initial = .ok state)
    (steps : equation.steps = .child child update :: rest)
    (derived : NodeDerivation graph child value) (updated : update value state = .ok next) :
    EquationReady graph owner { equation with initial := .ok next, steps := rest } := by
  intro first last result start later finished
  cases start
  apply ready state last result initial
  · rw [steps]
    exact .child derived updated later
  · exact finished

private def rootOwner (owner : Nat) : List Frame → Nat
  | [] => owner
  | frame :: rest => rootOwner frame.owner rest

/-- Each saved continuation consumes a derivation of precisely the child
    whose result the machine will pass to its update. -/
private def StackReady (graph : Graph) (child : Nat) : List Frame → Prop
  | [] => True
  | frame :: rest =>
    (∀ value, NodeDerivation graph child value → ∀ old next,
      frame.equation.initial = .ok old → frame.update value old = .ok next →
      EquationReady graph frame.owner { frame.equation with initial := .ok next }) ∧
      StackReady graph frame.owner rest

/-- An explicit DFS frame machine. A fresh node strictly decreases the exact
    domain cardinality; a check, cached dependency or completed frame strictly
    decreases remaining source steps. The proof rank is erased from execution. -/
private def machine (graph : Graph) (available : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (stack : List Frame) (memo : Memo) :
    Except Error (Summary × Memo) :=
  match equation.initial with
  | .error error => .error error
  | .ok state =>
    match _steps : equation.steps with
    | [] =>
      match equation.finish state with
      | .error error => .error error
      | .ok value =>
        let memo := memo.insert owner value
        match stack with
        | [] => .ok (value, memo)
        | frame :: rest =>
          match frame.equation.initial with
          | .error error => .error error
          | .ok old =>
            match frame.update value old with
            | .error error => .error error
            | .ok next => machine graph available frame.owner
                { frame.equation with initial := .ok next } rest memo
    | step :: rest =>
      match step with
      | .check update =>
        match update state with
        | .error error => .error error
        | .ok next => machine graph available owner
            { equation with initial := .ok next, steps := rest } stack memo
      | .child child update =>
        match memo.find child with
        | some value =>
          match update value state with
          | .error error => .error error
          | .ok next => machine graph available owner
              { equation with initial := .ok next, steps := rest } stack memo
        | none =>
          match _present : available.find child with
          | none => .error (.cycle child)
          | some _ =>
            match graph.nodes.find child with
            | none => .error (.incoherent "equation" child)
            | some childEquation =>
              let parent : Equation := { equation with initial := .ok state, steps := rest }
              let frame : Frame := { owner, equation := parent, update }
              machine graph (Available.erase available child) child childEquation (frame :: stack) memo
termination_by (Available.size available, equation.steps.length + savedSteps stack)
decreasing_by
  all_goals simp_wf
  all_goals first
    | apply Prod.Lex.right; simp_all [savedSteps] <;> omega
    | apply Prod.Lex.left; apply Available.erase_size_lt; rw [_present]; rfl

private theorem machine_step (graph : Graph) (available : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (stack : List Frame) (memo : Memo) :
    machine graph available owner equation stack memo =
  match equation.initial with
  | .error error => .error error
  | .ok state =>
    match equation.steps with
    | [] =>
      match equation.finish state with
      | .error error => .error error
      | .ok value =>
        let memo := memo.insert owner value
        match stack with
        | [] => .ok (value, memo)
        | frame :: rest =>
          match frame.equation.initial with
          | .error error => .error error
          | .ok old =>
            match frame.update value old with
            | .error error => .error error
            | .ok next => machine graph available frame.owner
                { frame.equation with initial := .ok next } rest memo
    | step :: rest =>
      match step with
      | .check update =>
        match update state with
        | .error error => .error error
        | .ok next => machine graph available owner
            { equation with initial := .ok next, steps := rest } stack memo
      | .child child update =>
        match memo.find child with
        | some value =>
          match update value state with
          | .error error => .error error
          | .ok next => machine graph available owner
              { equation with initial := .ok next, steps := rest } stack memo
        | none =>
          match available.find child with
          | none => .error (.cycle child)
          | some _ =>
            match graph.nodes.find child with
            | none => .error (.incoherent "equation" child)
            | some childEquation =>
              let parent : Equation := { equation with initial := .ok state, steps := rest }
              let frame : Frame := { owner, equation := parent, update }
              machine graph (Available.erase available child) child childEquation (frame :: stack) memo := by
  cases equation with
  | mk kind initial steps finished =>
    cases steps with
    | nil => exact machine.eq_def graph available owner ⟨kind, initial, [], finished⟩ stack memo
    | cons step rest =>
      cases step with
      | check update =>
        exact machine.eq_def graph available owner ⟨kind, initial, .check update :: rest, finished⟩ stack memo
      | child child update =>
        cases initial with
        | error error =>
          exact machine.eq_def graph available owner ⟨kind, .error error, .child child update :: rest, finished⟩ stack memo
        | ok state =>
          cases hc : memo.find child with
          | some value =>
            simpa only [hc] using machine.eq_def graph available owner
              ⟨kind, .ok state, .child child update :: rest, finished⟩ stack memo
          | none =>
            rw [machine.eq_def]
            simp only [hc]
            split
            · rename_i present
              rw [present]
            · rename_i unit present
              rw [present]


private theorem machine_derivation (graph : Graph) (available : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (stack : List Frame) (memo : Memo)
    (output : Summary) (finalMemo : Memo)
    (ready : EquationReady graph owner equation) (frames : StackReady graph owner stack)
    (cached : MemoDerivation graph memo)
    (run : machine graph available owner equation stack memo = .ok (output, finalMemo)) :
    NodeDerivation graph (rootOwner owner stack) output ∧ MemoDerivation graph finalMemo := by
  rw [machine_step] at run
  cases hi : equation.initial with
  | error error => simp only [hi] at run <;> cases run
  | ok state =>
    simp only [hi] at run
    cases hs : equation.steps with
    | nil =>
      try simp only [hs] at run
      cases hf : equation.finish state with
      | error error => simp only [hf] at run <;> cases run
      | ok value =>
        simp only [hf] at run
        have derived : NodeDerivation graph owner value :=
          ready state state value hi (hs ▸ StepsDerivation.nil state) hf
        have inserted := cached.insert derived
        cases hstack : stack with
        | nil =>
          rw [hstack] at frames
          simp only [hstack] at run
          cases run
          exact ⟨derived, inserted⟩
        | cons frame rest =>
          rw [hstack] at frames
          simp only [hstack] at run
          cases hp : frame.equation.initial with
          | error error => simp only [hp] at run <;> cases run
          | ok old =>
            simp only [hp] at run
            cases hu : frame.update value old with
            | error error => simp only [hu] at run <;> cases run
            | ok next =>
              simp only [hu] at run
              exact machine_derivation graph available frame.owner
                { frame.equation with initial := .ok next } rest (memo.insert owner value)
                output finalMemo (frames.1 value derived old next hp hu) frames.2 inserted run
    | cons step rest =>
      try simp only [hs] at run
      cases step with
      | check update =>
        cases hu : update state with
        | error error => simp only [hu] at run <;> cases run
        | ok next =>
          simp only [hu] at run
          exact machine_derivation graph available owner
            { equation with initial := .ok next, steps := rest } stack memo output finalMemo
            (ready.check hi hs hu) frames cached run
      | child child update =>
        cases hc : memo.find child with
        | some value =>
          simp only [hc] at run
          cases hu : update value state with
          | error error => simp only [hu] at run <;> cases run
          | ok next =>
            simp only [hu] at run
            exact machine_derivation graph available owner
              { equation with initial := .ok next, steps := rest } stack memo output finalMemo
              (ready.child hi hs (cached child value hc) hu) frames cached run
        | none =>
          simp only [hc] at run
          cases ha : available.find child with
          | none => simp only [ha] at run <;> cases run
          | some unit =>
            simp only [ha] at run
            cases hg : graph.nodes.find child with
            | none => simp only [hg] at run <;> cases run
            | some childEquation =>
              simp only [hg] at run
              let parent : Equation := { equation with initial := .ok state, steps := rest }
              let frame : Frame := { owner, equation := parent, update }
              have pending : StackReady graph child (frame :: stack) := by
                constructor
                · intro value derived old next hp hu
                  have same : state = old := Except.ok.inj hp
                  cases same
                  exact ready.child hi hs derived hu
                · exact frames
              exact machine_derivation graph (Available.erase available child) child childEquation
                (frame :: stack) memo output finalMemo (EquationReady.fresh hg) pending cached run
termination_by (Available.size available, equation.steps.length + savedSteps stack)
decreasing_by
  all_goals simp_wf
  all_goals first
    | apply Prod.Lex.left; apply Available.erase_size_lt; rw [ha]; rfl
    | apply Prod.Lex.right
  all_goals first
    | simp only [hs, hstack, savedSteps, List.length_cons, List.length_nil]; omega
    | simp only [hs, savedSteps, List.length_cons, List.length_nil]; omega

/-- Prepared-source memo lookup is exact and independent of execution fuel. -/
def solve (graph : Graph) (available : NatIndexTree Unit) (node : Nat) :
    StateT Memo (Except Error) Summary := fun memo =>
  match memo.find node with
  | some value => .ok (value, memo)
  | none =>
    match available.find node with
    | none => .error (.cycle node)
    | some _ => match graph.nodes.find node with
      | none => .error (.incoherent "equation" node)
      | some equation => machine graph (Available.erase available node) node equation [] memo

def Graph.query (graph : Graph) (node : Nat) : Except Error Summary := do
  pure (← solve graph (Available.domain graph.nodes) node .empty).1

/-- Successful solving preserves a derivation-backed memo and returns a
    finite derivation of the requested node. Cached entries are an explicit
    premise rather than an unchecked source of layout facts. -/
theorem solve_derivation (graph : Graph) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (value : Summary) (finalMemo : Memo)
    (cached : MemoDerivation graph memo)
    (run : solve graph available node memo = .ok (value, finalMemo)) :
    NodeDerivation graph node value ∧ MemoDerivation graph finalMemo := by
  simp only [solve] at run
  cases hc : memo.find node with
  | some result =>
    simp only [hc] at run
    cases run
    exact ⟨cached node value hc, cached⟩
  | none =>
    simp only [hc] at run
    cases ha : available.find node with
    | none => simp only [ha] at run <;> cases run
    | some unit =>
      simp only [ha] at run
      cases hg : graph.nodes.find node with
      | none => simp only [hg] at run <;> cases run
      | some equation =>
        simp only [hg] at run
        exact machine_derivation graph (Available.erase available node) node equation [] memo
          value finalMemo (EquationReady.fresh hg) True.intro cached run

/-- Every successful fresh query is justified by finite execution of the
    actual graph. This theorem has no cache-validity or graph-shape premise. -/
theorem Graph.query_derivation (graph : Graph) (node : Nat) (value : Summary)
    (run : graph.query node = .ok value) : NodeDerivation graph node value := by
  cases solved : solve graph (Available.domain graph.nodes) node .empty with
  | error error =>
    simp [Graph.query, solved, Except.bind, Except.pure, Bind.bind, Pure.pure] at run
  | ok pair =>
    rcases pair with ⟨result, memo⟩
    have derived := solve_derivation graph (Available.domain graph.nodes) node .empty result memo
      (MemoDerivation.empty graph) solved
    have same : result = value := by simpa [Graph.query, solved, Except.bind, Except.pure, Bind.bind, Pure.pure] using run
    exact same ▸ derived.1

theorem solve_cached (graph : Graph) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (value : Summary) (cached : memo.find node = some value) :
    solve graph available node memo = .ok (value, memo) := by
  rw [solve, cached]

theorem solve_done (graph : Graph) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (value : Summary)
    (absent : memo.find node = none) (present : available.find node = some ())
    (equation : graph.nodes.find node = some (.done (.ok value))) :
    solve graph available node memo = .ok (value, memo.insert node value) := by
  simp only [solve, absent, present, equation]
  conv =>
    lhs
    delta machine machine._unary
    rw [WellFounded.fix_eq]
  rfl

end TrustIr.SourceLayout

namespace TrustIr.SourceLayout

/-- An equation's initial refusal is returned before its actual steps. -/
theorem solve_initial_error (graph : Graph) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (error : Error) (equation : Equation)
    (absent : memo.find node = none) (present : available.find node = some ())
    (found : graph.nodes.find node = some equation) (initial : equation.initial = .error error) :
    solve graph available node memo = .error error := by
  simp only [solve, absent, present, found]
  rw [machine_step, initial]


/-- A continuation-parametric computation of the unchanged equation machine.
The remaining exact domain and memo describe the actual successful traversal;
this proposition introduces no alternate evaluator or execution fuel. -/
def Equation.Computes (graph : Graph) (available : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (memo : Memo) (value : Summary) (finalMemo : Memo)
    (remaining : NatIndexTree Unit) : Prop :=
  ∀ stack, machine graph available owner equation stack memo =
    match stack with
    | [] => .ok (value, finalMemo)
    | frame :: rest =>
      match frame.equation.initial with
      | .error error => .error error
      | .ok old =>
        match frame.update value old with
        | .error error => .error error
        | .ok next => machine graph remaining frame.owner
            { frame.equation with initial := .ok next } rest finalMemo

theorem Equation.Computes.finish (graph : Graph) (available : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (memo : Memo) (first : equation.State) (value : Summary)
    (initial : equation.initial = .ok first) (steps : equation.steps = [])
    (finished : equation.finish first = .ok value) :
    equation.Computes graph available owner memo value (memo.insert owner value) available := by
  intro stack
  rw [machine_step]
  simp only [initial, steps, finished]

theorem Equation.Computes.check (graph : Graph) (available remaining : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (memo finalMemo : Memo) (first next : equation.State)
    (update : equation.State → Except Error equation.State) (rest : List (Step equation.State))
    (value : Summary) (initial : equation.initial = .ok first)
    (steps : equation.steps = .check update :: rest) (updated : update first = .ok next)
    (later : ({ equation with initial := .ok next, steps := rest } : Equation).Computes
      graph available owner memo value finalMemo remaining) :
    equation.Computes graph available owner memo value finalMemo remaining := by
  intro stack
  rw [machine_step]
  simp only [initial, steps, updated]
  exact later stack

theorem Equation.Computes.cached_child (graph : Graph) (available remaining : NatIndexTree Unit) (owner : Nat)
    (equation : Equation) (memo finalMemo : Memo) (first next : equation.State)
    (child : Nat) (update : Summary → equation.State → Except Error equation.State)
    (rest : List (Step equation.State)) (childValue value : Summary)
    (initial : equation.initial = .ok first) (steps : equation.steps = .child child update :: rest)
    (cached : memo.find child = some childValue) (updated : update childValue first = .ok next)
    (later : ({ equation with initial := .ok next, steps := rest } : Equation).Computes
      graph available owner memo value finalMemo remaining) :
    equation.Computes graph available owner memo value finalMemo remaining := by
  intro stack
  rw [machine_step]
  simp only [initial, steps, cached, updated]
  exact later stack

theorem Equation.Computes.fresh_child (graph : Graph) (available middle remaining : NatIndexTree Unit) (owner : Nat)
    (equation childEquation : Equation) (memo middleMemo finalMemo : Memo)
    (first next : equation.State) (child : Nat)
    (update : Summary → equation.State → Except Error equation.State)
    (rest : List (Step equation.State)) (childValue value : Summary)
    (initial : equation.initial = .ok first) (steps : equation.steps = .child child update :: rest)
    (absent : memo.find child = none) (present : available.find child = some ())
    (found : graph.nodes.find child = some childEquation)
    (computed : childEquation.Computes graph (Available.erase available child) child memo
      childValue middleMemo middle)
    (updated : update childValue first = .ok next)
    (later : ({ equation with initial := .ok next, steps := rest } : Equation).Computes
      graph middle owner middleMemo value finalMemo remaining) :
    equation.Computes graph available owner memo value finalMemo remaining := by
  intro stack
  rw [machine_step]
  simp only [initial, steps, absent, present, found]
  rw [computed ({ owner, equation := { equation with initial := .ok first, steps := rest }, update } :: stack)]
  dsimp only
  rw [updated]
  exact later stack

theorem solve_of_computes (graph : Graph) (available remaining : NatIndexTree Unit) (node : Nat)
    (equation : Equation) (memo finalMemo : Memo) (value : Summary)
    (absent : memo.find node = none) (present : available.find node = some ())
    (found : graph.nodes.find node = some equation)
    (computed : equation.Computes graph (Available.erase available node) node memo
      value finalMemo remaining) :
    solve graph available node memo = .ok (value, finalMemo) := by
  simp only [solve, absent, present, found]
  exact computed []



end TrustIr.SourceLayout

namespace TrustIr.SourceLayout

/-- Observe the precise initial error in the actual stored equation without
    reifying its dependent accumulator, step functions or finalizer at a caller.
    This is a proof about the unchanged solver and exact graph lookup. -/
theorem solve_initial_error_observed (graph : Graph) (node : Nat) (memo : Memo)
    (error : Error) (absent : memo.find node = none)
    (observed : (graph.nodes.find node).bind (fun equation =>
      match equation.initial with
      | .error failure => some failure
      | .ok _ => none) = some error) :
    solve graph (Available.domain graph.nodes) node memo = .error error := by
  cases found : graph.nodes.find node with
  | none =>
    simp only [found] at observed
    change none = some error at observed
    cases observed
  | some equation =>
    simp only [found] at observed
    change (match equation.initial with
      | .error failure => some failure
      | .ok _ => none) = some error at observed
    cases initialized : equation.initial with
    | ok first =>
      simp only [initialized] at observed
      all_goals cases observed
    | error failure =>
      simp only [initialized] at observed
      change some failure = some error at observed
      have same : failure = error := Option.some.inj observed
      cases same
      have present : (Available.domain graph.nodes).find node = some () := by
        rw [Available.find_domain, found]
        rfl
      exact solve_initial_error graph (Available.domain graph.nodes) node memo
        error equation absent present found initialized

end TrustIr.SourceLayout
