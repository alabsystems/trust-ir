-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Invariant
import TrustIr.Layout.Enums

namespace TrustIr.SourceLayout

/-- Source geometry fits the word-sized carrier after conversion by `scale`.
Absent alignment remains absent; this predicate does not invent alignment or
constrain field metadata that `finish` does not inspect. -/
def WordBounds (scale : Nat) (value : Summary) : Prop :=
  scale * value.size ≤ word64Max ∧
    match value.align with
    | none => True
    | some align => scale * align ≤ word64Max

instance (scale : Nat) (value : Summary) : Decidable (WordBounds scale value) := by
  unfold WordBounds
  cases value.align <;> infer_instance

/-- Both modes require byte geometry to fit. Shape mode additionally requires
its conversion to bits to fit, for size and any authored alignment. -/
def FinishBounds (mode : Mode) (value : Summary) : Prop :=
  WordBounds 1 value ∧ (mode = .shape → WordBounds 8 value)

instance (mode : Mode) (value : Summary) : Decidable (FinishBounds mode value) := by
  unfold FinishBounds
  infer_instance

/-- Complete outcome of the production guard, including its precise refusal.
Successful checks return the entire original summary without rebuilding or
reordering its fields, variants or other source-owned metadata. -/
theorem finish_result (mode : Mode) (value : Summary) :
    finish mode value =
      if FinishBounds mode value then .ok value else .error .sizeOverflow := by
  have shape_eq : (Mode.shape == Mode.shape) = true := rfl
  have execution_ne : (Mode.execution == Mode.shape) = false := rfl
  cases mode <;> cases h : value.align with
  | none =>
    by_cases hs : value.size ≤ word64Max <;>
      by_cases hb : 8 * value.size ≤ word64Max <;>
      simp [finish, checked, FinishBounds, WordBounds, h, hs, hb,
        Except.bind, Except.pure, Bind.bind, Pure.pure, shape_eq, execution_ne]
  | some align =>
    by_cases hs : value.size ≤ word64Max <;>
      by_cases ha : align ≤ word64Max <;>
      by_cases hb : 8 * value.size ≤ word64Max <;>
      by_cases hab : 8 * align ≤ word64Max <;>
      simp [finish, checked, FinishBounds, WordBounds, h, hs, ha, hb, hab,
        Except.bind, Except.pure, Bind.bind, Pure.pure, shape_eq, execution_ne]

/-- Admission is equivalent to bounded geometry and exact metadata preservation. -/
theorem finish_ok_iff (mode : Mode) (input output : Summary) :
    finish mode input = .ok output ↔ output = input ∧ FinishBounds mode input := by
  rw [finish_result]
  by_cases h : FinishBounds mode input <;> simp [h, eq_comm]

/-- Every out-of-range size or authored alignment is refused as overflow. -/
theorem finish_overflow_iff (mode : Mode) (value : Summary) :
    finish mode value = .error .sizeOverflow ↔ ¬ FinishBounds mode value := by
  rw [finish_result]
  by_cases h : FinishBounds mode value <;> simp [h]

/-- Every successful finalizer result satisfies the stated predicate. This
checks the actual equation; it does not assume anything about child caches. -/
def Equation.Finalizes (equation : Equation) (property : Summary → Prop) : Prop :=
  ∀ state value, equation.finish state = .ok value → property value

theorem NodeDerivation.finalizes {graph : Graph} {node : Nat} {value : Summary}
    {equation : Equation} {property : Summary → Prop}
    (found : graph.nodes.find node = some equation)
    (safe : equation.Finalizes property) (derived : NodeDerivation graph node value) :
    property value := by
  cases derived with
  | equation lookup initial steps finished =>
    rw [found] at lookup
    cases lookup
    exact safe _ _ finished

/-- Canonical aggregate finalization enforces geometry bounds independently
of how its field dependencies were solved. -/
theorem canonicalFields_finalizes (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) :
    (canonicalFields mode kind id fields).Finalizes (FinishBounds mode) := by
  intro state value success
  change (do
    let size ← alignUp state.cursor state.align
    finish mode { size, align := some state.align, fields := state.fields.reverse }) = .ok value at success
  cases hs : alignUp state.cursor state.align with
  | error error => simp [hs, Except.bind, Bind.bind] at success
  | ok size =>
    simp only [hs, Except.bind, Bind.bind] at success
    have result := (finish_ok_iff mode _ value).mp success
    exact result.1 ▸ result.2

/-- Producer-authored aggregate metadata passes the same final guard, after
all overlap and transparent-representation checks. -/
theorem declaredFields_finalizes (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).Finalizes
      (FinishBounds mode) := by
  intro state value success
  dsimp only [declaredFields] at success
  simp only [Except.bind, Except.pure, Bind.bind, Pure.pure,
    MonadExceptOf.throw] at success
  split at success
  · cases success
  · split at success
    · split at success
      · split at success
        · cases success
        · exact ((finish_ok_iff mode _ value).mp success).1 ▸
            ((finish_ok_iff mode _ value).mp success).2
      · split at success
        · cases success
        · exact ((finish_ok_iff mode _ value).mp success).1 ▸
            ((finish_ok_iff mode _ value).mp success).2
      · cases success
    · exact ((finish_ok_iff mode _ value).mp success).1 ▸
        ((finish_ok_iff mode _ value).mp success).2

/-- Arrays and vectors enforce bounds in the child update rather than in
an identity finalizer. The proof follows that actual update. -/
theorem Equation.Executes.scaled_bounds {graph : Graph} {value : Summary}
    (mode : Mode) (count child : Nat)
    (run : (scaled mode count child).Executes graph value) : FinishBounds mode value := by
  rcases run with ⟨first, last, _initial, steps, finished⟩
  cases steps with
  | child solved updated later =>
    cases later
    cases finished
    dsimp only [scaled] at updated
    simp only [Except.bind, Bind.bind] at updated
    split at updated
    · cases updated
    · have result := (finish_ok_iff mode _ value).mp updated
      exact result.1 ▸ result.2

theorem NodeDerivation.scaled_bounds {graph : Graph} {node : Nat} {value : Summary}
    (mode : Mode) (count child : Nat)
    (found : graph.nodes.find node = some (scaled mode count child))
    (derived : NodeDerivation graph node value) : FinishBounds mode value :=
  (derived.execution found).scaled_bounds mode count child

theorem Graph.query_canonicalFields_bounds (graph : Graph) (node : Nat)
    (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat))
    (value : Summary)
    (found : graph.nodes.find node = some (canonicalFields mode kind id fields))
    (run : graph.query node = .ok value) : FinishBounds mode value :=
  (graph.query_derivation node value run).finalizes found
    (canonicalFields_finalizes mode kind id fields)

theorem Graph.query_declaredFields_bounds (graph : Graph) (node : Nat)
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat)) (value : Summary)
    (found : graph.nodes.find node =
      some (declaredFields mode kind id size align clamp transparent fields))
    (run : graph.query node = .ok value) : FinishBounds mode value :=
  (graph.query_derivation node value run).finalizes found
    (declaredFields_finalizes mode kind id size align clamp transparent fields)

theorem Graph.query_scaled_bounds (graph : Graph) (node : Nat)
    (mode : Mode) (count child : Nat) (value : Summary)
    (found : graph.nodes.find node = some (scaled mode count child))
    (run : graph.query node = .ok value) : FinishBounds mode value :=
  (graph.query_derivation node value run).scaled_bounds mode count child found

/-- A local guard bounds every successful finite execution of this equation. -/
def Equation.WordGuarded (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → WordBounds 1 value

abbrev Graph.WordInvariant (graph : Graph) := graph.SummaryInvariant (WordBounds 1)

theorem Equation.WordGuarded.rule {equation : Equation} (safe : equation.WordGuarded) :
    equation.InvariantRule (WordBounds 1) := .guarded safe

theorem finish_word_bounds (mode : Mode) (input value : Summary)
    (success : finish mode input = .ok value) : WordBounds 1 value := by
  have result := (finish_ok_iff mode input value).mp success
  exact result.1 ▸ result.2.1

theorem WordBounds.unit : WordBounds 1 { size := 0, align := some 1 } := by decide

theorem WordBounds.never : WordBounds 1 { size := 0, align := none } := by
  simp [WordBounds]

theorem Equation.WordGuarded.done (result : Result Summary)
    (safe : ∀ value, result = .ok value → WordBounds 1 value) :
    (Equation.done result).WordGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.WordGuarded.failed (error : Error) :
    (Equation.done (.error error)).WordGuarded :=
  Equation.WordGuarded.done _ (by intro value impossible; cases impossible)

theorem Equation.WordGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).WordGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact ((canonicalFields_finalizes mode kind id fields) last value finished).1

theorem Equation.WordGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).WordGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact ((declaredFields_finalizes mode kind id size align clamp transparent fields) last value finished).1

theorem Equation.WordGuarded.scaled (mode : Mode) (count child : Nat) :
    (scaled mode count child).WordGuarded :=
  fun _ _ run => (run.scaled_bounds mode count child).1

theorem Equation.WordGuarded.enumeration (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (enumEquation mode definition uninhabited variants).WordGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact enumEquation_finish_property mode definition uninhabited variants (WordBounds 1)
    (finish_word_bounds mode) last value finished ⟨first, initial⟩

theorem Equation.WordGuarded.sequence (children : List Nat) {next : Equation}
    (safe : next.WordGuarded) : (Equation.sequence children next).WordGuarded :=
  fun _ _ run => safe _ _ run.sequence_body

theorem Equation.WordGuarded.unit (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps := steps,
       finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).WordGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, executed, finished⟩
  cases finished
  exact WordBounds.unit

/-- A graph can carry different byte/bit obligations at different nodes.
The mode assignment is logical evidence, not additional runtime state. -/
abbrev Graph.ModeInvariant (modeAt : Nat → Mode) (graph : Graph) :=
  graph.IndexedInvariant (fun node value => FinishBounds (modeAt node) value)

/-- A finalization guard is an indexed rule independently of child bounds. -/
theorem Equation.Finalizes.indexed {property : Nat → Summary → Prop}
    (owner : Nat) {equation : Equation} (safe : equation.Finalizes (property owner)) :
    equation.IndexedRule property owner := by
  apply Equation.IndexedRule.guarded
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact safe last value finished

theorem FinishBounds.unit (mode : Mode) :
    FinishBounds mode { size := 0, align := some 1 } := by
  cases mode <;> decide

theorem FinishBounds.never (mode : Mode) :
    FinishBounds mode { size := 0, align := none } := by
  cases mode <;> decide

/-- Every mode's successful result may be used at an execution-mode alias.
This admits sharing a shape-safe scalar with execution, without asserting the
invalid converse that byte bounds imply shape-bit bounds. -/
theorem FinishBounds.execution {mode : Mode} {value : Summary}
    (safe : FinishBounds mode value) : FinishBounds .execution value := by
  refine ⟨safe.1, ?_⟩
  intro impossible
  cases impossible

theorem Equation.mode_alias (modeAt : Nat → Mode) (owner child : Nat)
    (same : modeAt owner = modeAt child) :
    (Equation.alias child).IndexedRule (fun node value => FinishBounds (modeAt node) value) owner :=
  Equation.IndexedRule.alias owner child (by intro value safe; simpa [same] using safe)

theorem Equation.execution_alias (modeAt : Nat → Mode) (owner child : Nat)
    (execution : modeAt owner = .execution) :
    (Equation.alias child).IndexedRule (fun node value => FinishBounds (modeAt node) value) owner :=
  Equation.IndexedRule.alias owner child (by
    intro value safe
    rw [execution]
    exact safe.execution)

theorem canonicalFields_mode_rule (modeAt : Nat → Mode) (owner : Nat) (kind : String)
    (id : Nat) (fields : List (Ty × Nat)) :
    (canonicalFields (modeAt owner) kind id fields).IndexedRule
      (fun node value => FinishBounds (modeAt node) value) owner :=
  (canonicalFields_finalizes (modeAt owner) kind id fields).indexed owner

theorem declaredFields_mode_rule (modeAt : Nat → Mode) (owner : Nat) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields (modeAt owner) kind id size align clamp transparent fields).IndexedRule
      (fun node value => FinishBounds (modeAt node) value) owner :=
  (declaredFields_finalizes (modeAt owner) kind id size align clamp transparent fields).indexed owner

theorem scaled_mode_rule (modeAt : Nat → Mode) (owner count child : Nat) :
    (scaled (modeAt owner) count child).IndexedRule
      (fun node value => FinishBounds (modeAt node) value) owner :=
  .guarded (fun _ _ run => run.scaled_bounds (modeAt owner) count child)

theorem enum_mode_rule (modeAt : Nat → Mode) (owner : Nat) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (enumEquation (modeAt owner) definition uninhabited variants).IndexedRule
      (fun node value => FinishBounds (modeAt node) value) owner := by
  apply Equation.IndexedRule.guarded
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact enumEquation_finish_property (modeAt owner) definition uninhabited variants
    (FinishBounds (modeAt owner))
    (fun input output success => by
      have result := (finish_ok_iff (modeAt owner) input output).mp success
      exact result.1 ▸ result.2) last value finished ⟨first, initial⟩

/-- Actual graph queries get the bound assigned to their precise root. -/
theorem Graph.query_mode_bounds (modeAt : Nat → Mode) (graph : Graph)
    (valid : graph.ModeInvariant modeAt) (node : Nat) (value : Summary)
    (run : graph.query node = .ok value) : FinishBounds (modeAt node) value :=
  graph.query_satisfies_at valid node value run

theorem MemoDerivation.mode_bounds (modeAt : Nat → Mode) {graph : Graph} {memo : Memo}
    (valid : graph.ModeInvariant modeAt) (cached : MemoDerivation graph memo)
    {node : Nat} {value : Summary} (found : memo.find node = some value) :
    FinishBounds (modeAt node) value := cached.satisfies_at valid found

/-- A successful execution satisfies the precise byte/bit guard for this
mode, independently of any assumptions about child derivations. -/
def Equation.ModeGuarded (mode : Mode) (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → FinishBounds mode value

theorem Equation.ModeGuarded.indexed {mode : Mode} {equation : Equation}
    (safe : equation.ModeGuarded mode) (modeAt : Nat → Mode) (owner : Nat)
    (assigned : modeAt owner = mode) :
    equation.IndexedRule (fun node value => FinishBounds (modeAt node) value) owner :=
  .guarded (by intro graph value run; rw [assigned]; exact safe graph value run)

theorem Equation.ModeGuarded.execution {mode : Mode} {equation : Equation}
    (safe : equation.ModeGuarded mode) : equation.ModeGuarded .execution :=
  fun graph value run => (safe graph value run).execution

theorem Equation.ModeGuarded.done (mode : Mode) (result : Result Summary)
    (safe : ∀ value, result = .ok value → FinishBounds mode value) :
    (Equation.done result).ModeGuarded mode := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.ModeGuarded.failed (mode : Mode) (error : Error) :
    (Equation.done (.error error)).ModeGuarded mode :=
  Equation.ModeGuarded.done mode _ (by intro value impossible; cases impossible)

theorem Equation.Finalizes.mode_guarded {mode : Mode} {equation : Equation}
    (safe : equation.Finalizes (FinishBounds mode)) : equation.ModeGuarded mode := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact safe last value finished

theorem Equation.ModeGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).ModeGuarded mode :=
  (canonicalFields_finalizes mode kind id fields).mode_guarded

theorem Equation.ModeGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).ModeGuarded mode :=
  (declaredFields_finalizes mode kind id size align clamp transparent fields).mode_guarded

theorem Equation.ModeGuarded.scaled (mode : Mode) (count child : Nat) :
    (scaled mode count child).ModeGuarded mode :=
  fun _ _ run => run.scaled_bounds mode count child

theorem Equation.ModeGuarded.enumeration (mode : Mode) (definition : EnumDef)
    (uninhabited : List Bool) (variants : List Nat) :
    (enumEquation mode definition uninhabited variants).ModeGuarded mode := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  exact enumEquation_finish_property mode definition uninhabited variants (FinishBounds mode)
    (fun input output success => by
      have result := (finish_ok_iff mode input output).mp success
      exact result.1 ▸ result.2) last value finished ⟨first, initial⟩

theorem Equation.ModeGuarded.sequence (mode : Mode) (children : List Nat) {next : Equation}
    (safe : next.ModeGuarded mode) : (Equation.sequence children next).ModeGuarded mode :=
  fun _ _ run => safe _ _ run.sequence_body

theorem Equation.ModeGuarded.unit (mode : Mode) (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps := steps,
       finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).ModeGuarded mode := by
  intro graph value run
  rcases run with ⟨first, last, initial, executed, finished⟩
  cases finished
  exact FinishBounds.unit mode

theorem NodeDerivation.mode_guarded {mode : Mode} {graph : Graph} {node : Nat} {value : Summary}
    {equation : Equation} (found : graph.nodes.find node = some equation)
    (safe : equation.ModeGuarded mode) (derived : NodeDerivation graph node value) :
    FinishBounds mode value := safe graph value (NodeDerivation.execution found derived)

/-- A copied equation preserves a mode obligation when both owners agree. -/
theorem Equation.IndexedRule.copy_mode {modeAt : Nat → Mode} {equation : Equation}
    {before after : Nat}
    (safe : equation.IndexedRule (fun node value => FinishBounds (modeAt node) value) before)
    (same : modeAt after = modeAt before) :
    equation.IndexedRule (fun node value => FinishBounds (modeAt node) value) after :=
  safe.reowner (fun value bounds => by simpa only [same] using bounds)

/-- Execution copies may consume either mode's result; the converse would
incorrectly admit byte-only geometry as a shape. -/
theorem Equation.IndexedRule.copy_execution {modeAt : Nat → Mode} {equation : Equation}
    {before after : Nat}
    (safe : equation.IndexedRule (fun node value => FinishBounds (modeAt node) value) before)
    (execution : modeAt after = .execution) :
    equation.IndexedRule (fun node value => FinishBounds (modeAt node) value) after :=
  safe.reowner (fun value bounds => by rw [execution]; exact bounds.execution)

/-- The actual copy-or-alias operation used by preparation is valid when
both reserved owners require the same mode. Missing forward roots stay aliases. -/
theorem Graph.ModeInvariant.copy_same {modeAt : Nat → Mode} {graph : Graph}
    (valid : graph.ModeInvariant modeAt) (child owner : Nat)
    (same : modeAt owner = modeAt child) :
    ((graph.nodes.find child).getD (Equation.alias child)).IndexedRule
      (fun node value => FinishBounds (modeAt node) value) owner := by
  cases found : graph.nodes.find child with
  | none => exact Equation.mode_alias modeAt owner child same
  | some equation => exact (valid child equation found).copy_mode same

theorem Graph.ModeInvariant.copy_execution {modeAt : Nat → Mode} {graph : Graph}
    (valid : graph.ModeInvariant modeAt) (child owner : Nat)
    (execution : modeAt owner = .execution) :
    ((graph.nodes.find child).getD (Equation.alias child)).IndexedRule
      (fun node value => FinishBounds (modeAt node) value) owner := by
  cases found : graph.nodes.find child with
  | none => exact Equation.execution_alias modeAt owner child execution
  | some equation => exact (valid child equation found).copy_execution execution

end TrustIr.SourceLayout
