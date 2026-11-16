-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameLifetimeProps

namespace TrustIr.FrameLifetime

/-- A frame identity at any finite depth of a runtime value. Compact arrays
are observed by logical lookup, so periodic/uniform storage is not expanded.
Every value-bearing constructor is included, including pointer metadata. -/
inductive FrameOccurs (lineage : Nat) : Value → Prop where
  | root (slots : List Value) : FrameOccurs lineage (.frame lineage slots)
  | frame {outer : Nat} {slots : List Value} {value : Value} :
      value ∈ slots → FrameOccurs lineage value → FrameOccurs lineage (.frame outer slots)
  | sourceRoot (function : FuncId) (declaration : BindingFrameDef) (slots : List Value) :
      FrameOccurs lineage (.sourceFrame lineage function declaration slots)
  | sourceFrame {outer : Nat} {function : FuncId} {declaration : BindingFrameDef}
      {slots : List Value} {value : Value} :
      value ∈ slots → FrameOccurs lineage value →
        FrameOccurs lineage (.sourceFrame outer function declaration slots)
  | aggregate {values : List Value} {value : Value} :
      value ∈ values → FrameOccurs lineage value → FrameOccurs lineage (.aggregate values)
  | vector {values : List Value} {value : Value} :
      value ∈ values → FrameOccurs lineage value → FrameOccurs lineage (.vector values)
  | set {values : List Value} {value : Value} :
      value ∈ values → FrameOccurs lineage value → FrameOccurs lineage (.set values)
  | sequence {values : List Value} {value : Value} :
      value ∈ values → FrameOccurs lineage value → FrameOccurs lineage (.sequence values)
  | closure {fn : FuncId} {values : List Value} {value : Value} :
      value ∈ values → FrameOccurs lineage value → FrameOccurs lineage (.closure fn values)
  | typedClosure {ty : ClosureTyId} {fn : FuncId} {values : List Value} {value : Value} :
      value ∈ values → FrameOccurs lineage value → FrameOccurs lineage (.typedClosure ty fn values)
  | record {fields : List (String × Value)} {name : String} {value : Value} :
      (name, value) ∈ fields → FrameOccurs lineage value → FrameOccurs lineage (.record fields)
  | array {values : CompactArray.Packed Value} {index : Nat} {value : Value} :
      values.get? index = some value → FrameOccurs lineage value → FrameOccurs lineage (.array values)
  | fatPtr {data : Nat} {provenance : Option AllocId} {value : Value} :
      FrameOccurs lineage value → FrameOccurs lineage (.fatPtr data provenance value)

/-- Recursive identity validity allows closed handles, but forbids unminted
identities in any nested payload. It imposes no type or liveness policy. -/
def MintedValue (bound : Nat) (value : Value) : Prop :=
  ∀ lineage, FrameOccurs lineage value → lineage < bound

theorem MintedValue.mono {before after : Nat} {value : Value}
    (valid : MintedValue before value) (monotone : before ≤ after) :
    MintedValue after value :=
  fun lineage occurrence => Nat.lt_of_lt_of_le (valid lineage occurrence) monotone

theorem mintedValue_undef (bound : Nat) (ty : Ty) : MintedValue bound (.undef ty) := by
  intro lineage occurrence
  cases occurrence

/-- A nominal function identity contains no runtime frame identity. This
does not establish that its source function declaration exists. -/
theorem mintedValue_fnItem (bound : Nat) (target : FuncId) :
    MintedValue bound (.fnItem target) := by
  intro lineage occurrence
  cases occurrence

theorem mintedValue_frame_iff (bound lineage : Nat) (slots : List Value) :
    MintedValue bound (.frame lineage slots) ↔
      lineage < bound ∧ ∀ value ∈ slots, MintedValue bound value := by
  constructor
  · intro valid
    exact ⟨valid lineage (.root slots), fun _ member other occurrence =>
      valid other (.frame member occurrence)⟩
  · rintro ⟨past, children⟩ other occurrence
    cases occurrence with
    | root => exact past
    | frame member child => exact children _ member _ child

theorem mintedValue_sourceFrame_iff (bound lineage : Nat) (function : FuncId)
    (declaration : BindingFrameDef) (slots : List Value) :
    MintedValue bound (.sourceFrame lineage function declaration slots) ↔
      lineage < bound ∧ ∀ value ∈ slots, MintedValue bound value := by
  constructor
  · intro valid
    exact ⟨valid lineage (.sourceRoot function declaration slots),
      fun _ member other occurrence => valid other (.sourceFrame member occurrence)⟩
  · rintro ⟨past, children⟩ other occurrence
    cases occurrence with
    | sourceRoot => exact past
    | sourceFrame member child => exact children _ member _ child

/-- Both frame carriers expose exactly the same recursive identity shape;
source metadata contributes no fabricated runtime lineage. -/
theorem mintedValue_frameValue_iff (bound : Nat) (origin : Option (FuncId × BindingFrameDef))
    (lineage : Nat) (slots : List Value) :
    MintedValue bound (frameValue origin lineage slots) ↔
      lineage < bound ∧ ∀ value ∈ slots, MintedValue bound value := by
  cases origin with
  | none => exact mintedValue_frame_iff bound lineage slots
  | some origin =>
    rcases origin with ⟨function, declaration⟩
    exact mintedValue_sourceFrame_iff bound lineage function declaration slots

/-- Exhaustive one-layer view of recursive validity. There is deliberately no
wildcard case: a new runtime constructor must declare its identity contents. -/
def ValueIdentityShape (bound : Nat) (value : Value) : Prop :=
  match value with
  | .frame lineage slots => lineage < bound ∧ ∀ child ∈ slots, MintedValue bound child
  | .sourceFrame lineage _ _ slots =>
      lineage < bound ∧ ∀ child ∈ slots, MintedValue bound child
  | .array values => ∀ index child, values.get? index = some child → MintedValue bound child
  | .aggregate values | .vector values | .set values | .sequence values =>
      ∀ child ∈ values, MintedValue bound child
  | .closure _ values | .typedClosure _ _ values => ∀ child ∈ values, MintedValue bound child
  | .record fields => ∀ name child, (name, child) ∈ fields → MintedValue bound child
  | .fatPtr _ _ metadata => MintedValue bound metadata
  | .int _ _ | .float _ | .bool _ | .ptr _ _ | .fnDef _ _ | .fnItem _ | .partial _
  | .undef _ | .nullPtr | .uninit => True

/-- Every runtime carrier agrees with the exhaustive shape description. -/
theorem mintedValue_iff_shape (bound : Nat) (value : Value) :
    MintedValue bound value ↔ ValueIdentityShape bound value := by
  cases value with
  | frame lineage slots => exact mintedValue_frame_iff bound lineage slots
  | sourceFrame lineage function declaration slots =>
    exact mintedValue_sourceFrame_iff bound lineage function declaration slots
  | aggregate values =>
    constructor
    · intro valid child member lineage occurrence
      exact valid lineage (.aggregate member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | aggregate member child => exact children _ member _ child
  | vector values =>
    constructor
    · intro valid child member lineage occurrence
      exact valid lineage (.vector member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | vector member child => exact children _ member _ child
  | set values =>
    constructor
    · intro valid child member lineage occurrence
      exact valid lineage (.set member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | set member child => exact children _ member _ child
  | sequence values =>
    constructor
    · intro valid child member lineage occurrence
      exact valid lineage (.sequence member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | sequence member child => exact children _ member _ child
  | closure fn values =>
    constructor
    · intro valid child member lineage occurrence
      exact valid lineage (.closure member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | closure member child => exact children _ member _ child
  | typedClosure ty fn values =>
    constructor
    · intro valid child member lineage occurrence
      exact valid lineage (.typedClosure member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | typedClosure member child => exact children _ member _ child
  | record fields =>
    constructor
    · intro valid name child member lineage occurrence
      exact valid lineage (.record member occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | record member child => exact children _ _ member _ child
  | array values =>
    constructor
    · intro valid index child found lineage occurrence
      exact valid lineage (.array found occurrence)
    · intro children lineage occurrence
      cases occurrence with
      | array found child => exact children _ _ found _ child
  | fatPtr data provenance metadata =>
    constructor
    · intro valid lineage occurrence
      exact valid lineage (.fatPtr occurrence)
    · intro child lineage occurrence
      cases occurrence with
      | fatPtr inner => exact child lineage inner
  | int width integer =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | float number =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | bool bit =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | ptr address provenance =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | fnDef ty fn =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | fnItem fn =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | «partial» bytes =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | undef ty =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | nullPtr  =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence
  | uninit  =>
    constructor
    · intro _; trivial
    · intro _ lineage occurrence; cases occurrence

/-- Recursive validity of the values in an SSA map. -/
def MintedValues (bound : Nat) (locals : ValueMap) : Prop :=
  ∀ id value, locals.get id = some value → MintedValue bound value

theorem values_empty (bound : Nat) : MintedValues bound ValueMap.empty := by
  intro id value lookup
  cases lookup

theorem values_mono {before after : Nat} {locals : ValueMap}
    (valid : MintedValues before locals) (monotone : before ≤ after) :
    MintedValues after locals :=
  fun id value lookup => (valid id value lookup).mono monotone

theorem values_set {bound : Nat} {locals : ValueMap}
    (valid : MintedValues bound locals) (dest : ValueId) (value : Value)
    (operand : MintedValue bound value) : MintedValues bound (locals.set dest value) := by
  intro id found lookup
  by_cases same : id = dest
  · subst id
    simp [ValueMap.get, ValueMap.set] at lookup
    cases lookup
    exact operand
  · simp [ValueMap.get, ValueMap.set, same] at lookup
    exact valid id found lookup

theorem values_handles {bound : Nat} {locals : ValueMap}
    (valid : MintedValues bound locals) : MintedHandles bound locals :=
  fun id lineage slots lookup => valid id (.frame lineage slots) lookup lineage (.root slots)

private theorem slot_member {values : List Value} {index : Nat} {value : Value}
    (found : trustIrListGet? values index = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero => simp at found; subst value; exact List.Mem.head _
    | succ index => exact List.Mem.tail _ (ih found)

private theorem set_valid (bound : Nat) (values : List Value) (index : Nat) (value : Value)
    (original : ∀ child ∈ values, MintedValue bound child)
    (inserted : MintedValue bound value) :
    ∀ child ∈ values.set index value, MintedValue bound child := by
  induction values generalizing index with
  | nil => intro child member; cases member
  | cons head tail ih =>
    cases index with
    | zero =>
      intro child member
      cases member with
      | head => exact inserted
      | tail _ member => exact original child (.tail head member)
    | succ index =>
      intro child member
      cases member with
      | head => exact original head (.head tail)
      | tail _ member =>
        exact ih index (fun child member => original child (.tail head member)) child member

/-- Updating one actual runtime frame slot preserves every recursively
minted child, including source-origin frames and nominal item leaves. -/
theorem frame_slots_set_valid (bound : Nat) (values : List Value) (index : Nat) (value : Value)
    (original : ∀ child ∈ values, MintedValue bound child)
    (inserted : MintedValue bound value) :
    ∀ child ∈ values.set index value, MintedValue bound child :=
  set_valid bound values index value original inserted

/-- Identity well-formedness of a runtime state. Other well-formedness
components (typing, memory, SSA freshness, LIFO) are deliberately separate. -/
structure WellMintedState (s : MachineState) : Prop where
  table : MintedLineages s
  values : MintedValues s.nextFrameLineage s.locals

theorem WellMintedState.empty : WellMintedState MachineState.empty :=
  ⟨minted_empty, values_empty 0⟩

theorem WellMintedState.open_success (s final : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semOpenFrame definition) s = .ok (id, final)) :
    WellMintedState final := by
  by_cases room : s.nextFrameLineage < 2^64-1
  · rw [open_run s definition room] at run
    cases run
    constructor
    · exact minted_open s definition valid.table
    · apply values_set (values_mono valid.values (Nat.le_succ _))
      apply (mintedValue_frame_iff _ _ _).2
      constructor
      · exact Nat.lt_succ_self _
      · intro value member
        rcases List.mem_map.mp member with ⟨slot, _, rfl⟩
        exact mintedValue_undef _ slot.ty
  · rw [open_overflow_run s definition room] at run
    contradiction

theorem WellMintedState.bind_success (s final : MachineState) (id rhs result : ValueId)
    (slot : Nat) (valid : WellMintedState s)
    (run : Sem.run (semBindSlot id slot rhs) s = .ok (result, final)) :
    WellMintedState final := by
  obtain ⟨origin, lineage, slots, value, lookup, operand, _, _, _, rfl⟩ :=
    bind_success_state s final id rhs result slot run
  have original := (mintedValue_frameValue_iff _ _ _ _).1 (valid.values id _ lookup)
  constructor
  · exact valid.table
  · apply values_set valid.values
    exact (mintedValue_frameValue_iff _ _ _ _).2
      ⟨original.1, set_valid _ slots slot value original.2 (valid.values rhs value operand)⟩

/-- Recursive validity derives the selected-slot premise from the original
frame value, eliminating the additional assumption needed by direct handles. -/
theorem WellMintedState.load_success (s final : MachineState) (id result : ValueId)
    (slot : Nat) (ty : Ty) (valid : WellMintedState s)
    (run : Sem.run (semLoadSlot id slot ty) s = .ok (result, final)) :
    WellMintedState final := by
  obtain ⟨origin, lineage, slots, value, lookup, _, found, _, rfl⟩ :=
    load_success_state s final id result slot ty run
  have original := (mintedValue_frameValue_iff _ _ _ _).1 (valid.values id _ lookup)
  exact ⟨valid.table, values_set valid.values _ value (original.2 value (slot_member found))⟩

theorem WellMintedState.close_success (s final : MachineState) (id : ValueId)
    (valid : WellMintedState s)
    (run : Sem.run (semCloseFrame id) s = .ok ((), final)) :
    WellMintedState final := by
  obtain ⟨_, lineage, _, _, _, rfl⟩ := close_success_state s final id run
  exact ⟨minted_close s lineage valid.table, valid.values⟩

/-- Caller restoration needs recursive validity of saved locals and returns
at the callee's current bound; validity of its own locals is insufficient. -/
theorem WellMintedState.restore (s : MachineState) (frame : StackFrame) (ret : List Value)
    (table : MintedLineages s) (saved : MintedValues s.nextFrameLineage frame.locals)
    (returned : ∀ value ∈ ret, MintedValue s.nextFrameLineage value) :
    WellMintedState (restoreFrame s frame ret) := by
  constructor
  · exact minted_restore s frame ret table
  · cases destEq : frame.returnDest with
    | none => simpa [restoreFrame, destEq] using saved
    | some dest =>
      cases ret with
      | nil => simpa [restoreFrame, destEq] using saved
      | cons value rest =>
        cases rest with
        | nil => simpa [restoreFrame, destEq] using values_set saved dest value (returned value (by simp))
        | cons next tail => simpa [restoreFrame, destEq] using saved

/-- Saved caller values remain recursively valid across a callee's monotone
identity history, including any closures of previously minted identities. -/
theorem saved_values_history (before after : MachineState) (frame : StackFrame)
    (saved : MintedValues before.nextFrameLineage frame.locals)
    (history : HistoryExtends before after) :
    MintedValues after.nextFrameLineage frame.locals := values_mono saved history.monotone

/-- The earlier nested-handle counterexample is rejected by recursive
validity, even though the outer direct handle has already been minted. -/
theorem nested_future_rejected : ¬ MintedValue 1 (.frame 0 [.frame 1 []]) := by
  intro valid
  exact Nat.lt_irrefl 1
    (valid 1 (.frame (List.Mem.head []) (.root [])))

end TrustIr.FrameLifetime
