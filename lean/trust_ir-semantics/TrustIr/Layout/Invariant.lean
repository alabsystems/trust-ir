-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Graph

namespace TrustIr.SourceLayout

/-- Logical projection of ordered updates with the required child properties.
It carries no runtime state and checks only the executed finite prefix. -/
inductive StepsInvariant (property : Summary → Prop) :
    {σ : Type} → List (Step σ) → σ → σ → Prop where
  | nil {σ : Type} (state : σ) : StepsInvariant property [] state state
  | check {σ : Type} {update : σ → Except Error σ} {rest : List (Step σ)}
      {first next last : σ} (updated : update first = .ok next)
      (safe : StepsInvariant property rest next last) :
      StepsInvariant property (.check update :: rest) first last
  | child {σ : Type} {node : Nat} {value : Summary}
      {update : Summary → σ → Except Error σ} {rest : List (Step σ)}
      {first next last : σ} (valueSafe : property value)
      (updated : update value first = .ok next) (safe : StepsInvariant property rest next last) :
      StepsInvariant property (.child node update :: rest) first last

/-- The compiler may install a locally guarded equation or a true child alias.
The latter is justified by finite derivation induction, not a cache oracle. -/
inductive Equation.InvariantRule (property : Summary → Prop) : Equation → Prop where
  | guarded {equation : Equation}
      (safe : ∀ graph value, equation.Executes graph value → property value) :
      InvariantRule property equation
  | alias (child : Nat) : InvariantRule property (Equation.alias child)

/-- Every installed equation carries an invariant rule. It remains meaningful
for forward references and cycles: only finite successful derivations are used. -/
def Graph.SummaryInvariant (property : Summary → Prop) (graph : Graph) : Prop :=
  ∀ node equation, graph.nodes.find node = some equation → equation.InvariantRule property

theorem NodeDerivation.satisfies {property : Summary → Prop} {graph : Graph}
    (valid : graph.SummaryInvariant property) {node : Nat} {value : Summary}
    (derived : NodeDerivation graph node value) : property value := by
  induction derived using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ => StepsInvariant property steps first last) with
  | equation found initial steps finished evidence =>
    cases valid _ _ found with
    | guarded safe => exact safe graph _ ⟨_, _, initial, steps, finished⟩
    | alias child =>
      cases evidence with
      | child good updated later =>
        cases later
        cases updated
        cases finished
        exact good
  | nil state => exact .nil state
  | check updated later safe => exact .check updated safe
  | child solved updated later good safe => exact .child good updated safe

theorem Graph.SummaryInvariant.empty (property : Summary → Prop) (count : Nat) :
    ({ count := count } : Graph).SummaryInvariant property := by
  intro node equation impossible
  cases impossible

theorem Graph.SummaryInvariant.insert {property : Summary → Prop} {graph : Graph}
    (valid : graph.SummaryInvariant property) (node : Nat) (equation : Equation)
    (safe : equation.InvariantRule property) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).SummaryInvariant property := by
  intro query result found
  change (graph.nodes.insert node equation).find query = some result at found
  rw [NatIndexTree.find_insert] at found
  by_cases same : query = node
  · rw [if_pos same] at found
    cases found
    exact safe
  · rw [if_neg same] at found
    exact valid query result found

/-- A graph invariant plus a derivation-backed memo suffices for successful
solving, including cache hits. -/
theorem solve_satisfies {property : Summary → Prop} (graph : Graph)
    (valid : graph.SummaryInvariant property) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (value : Summary) (finalMemo : Memo) (cached : MemoDerivation graph memo)
    (run : solve graph available node memo = .ok (value, finalMemo)) : property value :=
  ((solve_derivation graph available node memo value finalMemo cached run).1).satisfies valid

theorem Graph.query_satisfies {property : Summary → Prop} (graph : Graph)
    (valid : graph.SummaryInvariant property) (node : Nat) (value : Summary)
    (run : graph.query node = .ok value) : property value :=
  (graph.query_derivation node value run).satisfies valid

/-- Node-indexed child obligations for an actual ordered equation execution.
Unlike a uniform summary predicate, this can distinguish execution and shape
nodes in their shared graph. No label or runtime field is added to the graph. -/
inductive StepsInvariantAt (property : Nat → Summary → Prop) :
    {σ : Type} → List (Step σ) → σ → σ → Prop where
  | nil {σ : Type} (state : σ) : StepsInvariantAt property [] state state
  | check {σ : Type} {update : σ → Except Error σ} {rest : List (Step σ)}
      {first next last : σ} (updated : update first = .ok next)
      (safe : StepsInvariantAt property rest next last) :
      StepsInvariantAt property (.check update :: rest) first last
  | child {σ : Type} {node : Nat} {value : Summary}
      {update : Summary → σ → Except Error σ} {rest : List (Step σ)}
      {first next last : σ} (valueSafe : property node value)
      (updated : update value first = .ok next)
      (safe : StepsInvariantAt property rest next last) :
      StepsInvariantAt property (.child node update :: rest) first last

/-- Either a local execution guard or a compositional rule consuming the exact
child obligations, in order. The owner node is part of the postcondition. -/
inductive Equation.IndexedRule (property : Nat → Summary → Prop) (owner : Nat) :
    Equation → Prop where
  | guarded {equation : Equation}
      (safe : ∀ graph value, equation.Executes graph value → property owner value) :
      IndexedRule property owner equation
  | checked {equation : Equation}
      (safe : ∀ first last value, equation.initial = .ok first →
        StepsInvariantAt property equation.steps first last →
        equation.finish last = .ok value → property owner value) :
      IndexedRule property owner equation

/-- Every installed equation establishes its own node's property. Alias rules
must transport the child's actual property; a different node's bound is not
silently substituted. Cycles still require finite successful derivations. -/
def Graph.IndexedInvariant (property : Nat → Summary → Prop) (graph : Graph) : Prop :=
  ∀ node equation, graph.nodes.find node = some equation →
    equation.IndexedRule property node

theorem NodeDerivation.satisfies_at {property : Nat → Summary → Prop} {graph : Graph}
    (valid : graph.IndexedInvariant property) {node : Nat} {value : Summary}
    (derived : NodeDerivation graph node value) : property node value := by
  induction derived using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ => StepsInvariantAt property steps first last) with
  | equation found initial steps finished evidence =>
    cases valid _ _ found with
    | guarded safe => exact safe graph _ ⟨_, _, initial, steps, finished⟩
    | checked safe => exact safe _ _ _ initial evidence finished
  | nil state => exact .nil state
  | check updated later safe => exact .check updated safe
  | child solved updated later good safe => exact .child good updated safe

theorem Equation.IndexedRule.alias {property : Nat → Summary → Prop} (owner child : Nat)
    (transport : ∀ value, property child value → property owner value) :
    (Equation.alias child).IndexedRule property owner := by
  apply IndexedRule.checked
  intro first last value initial steps finished
  cases steps with
  | child good updated later =>
    cases later
    cases updated
    cases finished
    exact transport _ good

/-- Copying an equation changes its owner, not its child obligations. The
new owner must accept every result licensed at the original owner. -/
theorem Equation.IndexedRule.reowner {property : Nat → Summary → Prop}
    {equation : Equation} {before after : Nat} (safe : equation.IndexedRule property before)
    (transport : ∀ value, property before value → property after value) :
    equation.IndexedRule property after := by
  cases safe with
  | guarded run => exact .guarded (fun graph value executed => transport value (run graph value executed))
  | checked run => exact .checked (fun first last value initial steps finished =>
      transport value (run first last value initial steps finished))

theorem Graph.IndexedInvariant.empty (property : Nat → Summary → Prop) (count : Nat) :
    ({ count := count } : Graph).IndexedInvariant property := by
  intro node equation impossible
  cases impossible

theorem Graph.IndexedInvariant.insert {property : Nat → Summary → Prop} {graph : Graph}
    (valid : graph.IndexedInvariant property) (node : Nat) (equation : Equation)
    (safe : equation.IndexedRule property node) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).IndexedInvariant property := by
  intro query result found
  change (graph.nodes.insert node equation).find query = some result at found
  rw [NatIndexTree.find_insert] at found
  by_cases same : query = node
  · rw [if_pos same] at found
    cases found
    exact same ▸ safe
  · rw [if_neg same] at found
    exact valid query result found

theorem MemoDerivation.satisfies_at {property : Nat → Summary → Prop} {graph : Graph}
    {memo : Memo} (cached : MemoDerivation graph memo)
    (valid : graph.IndexedInvariant property) {node : Nat} {value : Summary}
    (found : memo.find node = some value) : property node value :=
  (cached node value found).satisfies_at valid

/-- Cache hits and fresh solving obey the same node-indexed rule, because both
are justified by a derivation in the actual graph. -/
theorem solve_satisfies_at {property : Nat → Summary → Prop} (graph : Graph)
    (valid : graph.IndexedInvariant property) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (value : Summary) (finalMemo : Memo) (cached : MemoDerivation graph memo)
    (run : solve graph available node memo = .ok (value, finalMemo)) : property node value :=
  ((solve_derivation graph available node memo value finalMemo cached run).1).satisfies_at valid

theorem Graph.query_satisfies_at {property : Nat → Summary → Prop} (graph : Graph)
    (valid : graph.IndexedInvariant property) (node : Nat) (value : Summary)
    (run : graph.query node = .ok value) : property node value :=
  (graph.query_derivation node value run).satisfies_at valid

/-- Existing uniform invariants remain a special case of indexed rules. -/
theorem Graph.SummaryInvariant.indexed {property : Summary → Prop} {graph : Graph}
    (valid : graph.SummaryInvariant property) :
    graph.IndexedInvariant (fun _ value => property value) := by
  intro node equation found
  cases valid node equation found with
  | guarded safe => exact .guarded safe
  | alias child => exact Equation.IndexedRule.alias node child (fun _ safe => safe)

theorem Equation.IndexedRule.done {property : Nat → Summary → Prop} (owner : Nat)
    (result : Except Error Summary) (safe : ∀ value, result = .ok value → property owner value) :
    (Equation.done result).IndexedRule property owner := by
  apply IndexedRule.guarded
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

/-- Actual child derivations and their induction hypotheses share the same
 child value and update. Keeping these together avoids correlating unrelated
 logical and execution witnesses that happen to have the same final state. -/
inductive StepsCertified (graph : Graph) (property : Nat → Summary → Prop) :
    {σ : Type} → List (Step σ) → σ → σ → Prop where
  | nil {σ : Type} (state : σ) : StepsCertified graph property [] state state
  | check {σ : Type} {update : σ → Except Error σ} {rest : List (Step σ)}
      {first next last : σ} (updated : update first = .ok next)
      (safe : StepsCertified graph property rest next last) :
      StepsCertified graph property (.check update :: rest) first last
  | child {σ : Type} {node : Nat} {value : Summary}
      {update : Summary → σ → Except Error σ} {rest : List (Step σ)}
      {first next last : σ} (solved : NodeDerivation graph node value)
      (valueSafe : property node value) (updated : update value first = .ok next)
      (safe : StepsCertified graph property rest next last) :
      StepsCertified graph property (.child node update :: rest) first last

theorem StepsCertified.derivation {graph : Graph} {property : Nat → Summary → Prop}
    {σ : Type} {steps : List (Step σ)} {first last : σ}
    (safe : StepsCertified graph property steps first last) : StepsDerivation graph steps first last := by
  induction safe with
  | nil state => exact .nil state
  | check updated later ih => exact .check updated ih
  | child solved good updated later ih => exact .child solved updated ih

theorem StepsCertified.invariant {graph : Graph} {property : Nat → Summary → Prop}
    {σ : Type} {steps : List (Step σ)} {first last : σ}
    (safe : StepsCertified graph property steps first last) : StepsInvariantAt property steps first last := by
  induction safe with
  | nil state => exact .nil state
  | check updated later ih => exact .check updated ih
  | child solved good updated later ih => exact .child good updated ih

/-- A compositional rule may inspect actual child derivations in the same
 graph as its equation, as well as their induction hypotheses. This permits
 compiler certificates about exact child equations without assuming every
 arbitrary graph has those equations. -/
def Equation.ContextualRule (graph : Graph) (property : Nat → Summary → Prop)
    (owner : Nat) (equation : Equation) : Prop :=
  ∀ first last value, equation.initial = .ok first →
    StepsCertified graph property equation.steps first last →
    equation.finish last = .ok value → property owner value

/-- Every installed equation is justified in its actual graph. Finite
 derivation induction supplies child properties even in a cyclic graph. -/
def Graph.ContextualInvariant (property : Nat → Summary → Prop) (graph : Graph) : Prop :=
  ∀ node equation, graph.nodes.find node = some equation →
    equation.ContextualRule graph property node

theorem NodeDerivation.satisfies_contextual {property : Nat → Summary → Prop} {graph : Graph}
    (valid : graph.ContextualInvariant property) {node : Nat} {value : Summary}
    (derived : NodeDerivation graph node value) : property node value := by
  induction derived using NodeDerivation.rec
    (motive_2 := fun {_} steps first last _ => StepsCertified graph property steps first last) with
  | equation found initial steps finished evidence =>
    exact valid _ _ found _ _ _ initial evidence finished
  | nil state => exact .nil state
  | check updated later safe => exact .check updated safe
  | child solved updated later good safe => exact .child solved good updated safe

theorem Equation.IndexedRule.contextual {property : Nat → Summary → Prop}
    {equation : Equation} {owner : Nat} (safe : equation.IndexedRule property owner)
    (graph : Graph) : equation.ContextualRule graph property owner := by
  intro first last value initial children finished
  cases safe with
  | guarded run => exact run graph value ⟨first, last, initial, children.derivation, finished⟩
  | checked run => exact run first last value initial children.invariant finished

theorem Graph.IndexedInvariant.contextual {property : Nat → Summary → Prop} {graph : Graph}
    (valid : graph.IndexedInvariant property) : graph.ContextualInvariant property :=
  fun node equation found => (valid node equation found).contextual graph

theorem MemoDerivation.satisfies_contextual {property : Nat → Summary → Prop} {graph : Graph}
    {memo : Memo} (cached : MemoDerivation graph memo)
    (valid : graph.ContextualInvariant property) {node : Nat} {value : Summary}
    (found : memo.find node = some value) : property node value :=
  (cached node value found).satisfies_contextual valid

theorem solve_satisfies_contextual {property : Nat → Summary → Prop} (graph : Graph)
    (valid : graph.ContextualInvariant property) (available : NatIndexTree Unit) (node : Nat)
    (memo : Memo) (value : Summary) (finalMemo : Memo) (cached : MemoDerivation graph memo)
    (run : solve graph available node memo = .ok (value, finalMemo)) : property node value :=
  ((solve_derivation graph available node memo value finalMemo cached run).1).satisfies_contextual valid

theorem Graph.query_satisfies_contextual {property : Nat → Summary → Prop} (graph : Graph)
    (valid : graph.ContextualInvariant property) (node : Nat) (value : Summary)
    (run : graph.query node = .ok value) : property node value :=
  (graph.query_derivation node value run).satisfies_contextual valid

theorem Equation.ContextualRule.alias {property : Nat → Summary → Prop} (graph : Graph)
    (owner child : Nat) (transport : ∀ value, property child value → property owner value) :
    (Equation.alias child).ContextualRule graph property owner := by
  intro first last value initial steps finished
  cases steps with
  | child solved good updated later =>
    cases later
    cases updated
    cases finished
    exact transport _ good

theorem Equation.ContextualRule.reowner {property : Nat → Summary → Prop} {graph : Graph}
    {equation : Equation} {before after : Nat}
    (safe : equation.ContextualRule graph property before)
    (transport : ∀ value, property before value → property after value) :
    equation.ContextualRule graph property after :=
  fun first last value initial steps finished =>
    transport value (safe first last value initial steps finished)

private theorem StepsInvariantAt.ignore_prefix {property : Nat → Summary → Prop} {σ : Type}
    (children : List Nat) (rest : List (Step σ)) (first last : σ)
    (run : StepsInvariantAt property
      (children.map (fun child => .child child fun _ state => .ok state) ++ rest) first last) :
    StepsInvariantAt property rest first last := by
  induction children with
  | nil => exact run
  | cons child children ih =>
    cases run with
    | child good updated later =>
      cases updated
      exact ih later

private theorem StepsInvariantAt.unlift {property : Nat → Summary → Prop} {σ : Type}
    (steps : List (Step σ)) (first : σ) (stored : Except Error σ)
    (run : StepsInvariantAt property (steps.map (fun (step : Step σ) => (match step with
      | Step.check update => Step.check (fun stored => do pure (.ok (← update (← stored))))
      | Step.child node update => Step.child node (fun value stored => do pure (.ok (← update value (← stored)))) : Step (Except Error σ))))
      (.ok first) stored) :
    ∃ last, stored = .ok last ∧ StepsInvariantAt property steps first last := by
  induction steps generalizing first stored with
  | nil => cases run; exact ⟨first, rfl, .nil first⟩
  | cons step rest ih =>
    cases step with
    | check update =>
      cases run with
      | check updated later =>
        cases hu : update first with
        | error error => simp [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
        | ok next =>
          simp only [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
          cases updated
          rcases ih next _ later with ⟨last, same, original⟩
          exact ⟨last, same, .check hu original⟩
    | child node update =>
      cases run with
      | child good updated later =>
        rename_i value next
        cases hu : update value first with
        | error error => simp [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
        | ok next =>
          simp only [hu, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
          cases updated
          rcases ih next _ later with ⟨last, same, original⟩
          exact ⟨last, same, .child good hu original⟩

/-- Prefix dependencies keep their actual order and cannot supply the body's
result. Checked rules retain the body's child induction hypotheses. -/
theorem Equation.IndexedRule.sequence {property : Nat → Summary → Prop} {owner : Nat}
    (children : List Nat) {next : Equation} (safe : next.IndexedRule property owner) :
    (Equation.sequence children next).IndexedRule property owner := by
  cases safe with
  | guarded body => exact .guarded (fun graph value run => body graph value run.sequence_body)
  | checked body =>
    apply Equation.IndexedRule.checked
    intro first last value initial steps finished
    cases initial
    simp only [Equation.sequence, Accumulator.State, List.append_assoc] at steps
    have suffix := StepsInvariantAt.ignore_prefix children _ _ _ steps
    cases suffix with
    | check updated later =>
      cases hi : next.initial with
      | error error => simp [hi, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
      | ok state =>
        simp only [hi, Except.bind, Except.pure, Bind.bind, Pure.pure] at updated
        cases updated
        rcases StepsInvariantAt.unlift next.steps state last later with ⟨final, same, original⟩
        subst last
        exact body state final value hi original finished

end TrustIr.SourceLayout
