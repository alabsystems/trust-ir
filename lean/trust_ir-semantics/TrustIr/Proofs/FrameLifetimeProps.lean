-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.BindingFrameProps

namespace TrustIr.FrameLifetime

/-! Universal runtime laws, beyond the closed traces in BindingFrameProps.
The states below are exact successful results of the real operations, not
alternate semantics. No well-formedness or freshness of a forged state is
silently assumed: allocation room and non-overwritten SSA ids are explicit.
-/

def afterClose (s : MachineState) (lineage : Nat) : MachineState :=
  { s with openFrameLineages := s.openFrameLineages.filter (fun id => id != lineage) }

def afterOpen (s : MachineState) (definition : BindingFrameDef) : MachineState :=
  { s with
    locals := s.locals.set ⟨s.nextValueId⟩ (initFrame s.nextFrameLineage definition.slots)
    nextValueId := s.nextValueId + 1
    openFrameLineages := s.nextFrameLineage :: s.openFrameLineages
    nextFrameLineage := s.nextFrameLineage + 1 }

def afterBind (s : MachineState) (lineage : Nat) (slots : List Value)
    (slot : Nat) (value : Value) : MachineState :=
  { s with
    locals := s.locals.set ⟨s.nextValueId⟩ (.frame lineage (slots.set slot value))
    nextValueId := s.nextValueId + 1 }

theorem close_run (s : MachineState) (id : ValueId) (lineage : Nat) (slots : List Value)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (live : s.openFrameLineages.contains lineage = true) :
    Sem.run (semCloseFrame id) s = .ok ((), afterClose s lineage) := by
  trustIrCompilerProof {
      simp [semCloseFrame, Sem.frameHandle, Sem.setFrameState, afterClose,
        Sem.run, Sem.lookupValue, Sem.rejectPartial, Sem.getState, Sem.setState,
        lookup, live, StateT.run, StateT.bind, StateT.get, StateT.set,
        StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
  } {
      simp only [ite_true, semCloseFrame, Sem.frameHandle, Sem.setFrameState, afterClose,
        Sem.run, Sem.lookupValue, Sem.rejectPartial, Sem.getState, Sem.setState,
        lookup, live, StateT.run, StateT.bind, StateT.get, StateT.set,
        StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
  }

theorem open_run (s : MachineState) (definition : BindingFrameDef)
    (room : s.nextFrameLineage < 2^64-1) :
    Sem.run (semOpenFrame definition) s = .ok (⟨s.nextValueId⟩, afterOpen s definition) := by
  simp [semOpenFrame, Sem.setFrameState, afterOpen, Sem.run, room,
    Sem.getState, Sem.setState, Sem.bindFresh, MachineState.bindValue,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
    StateT.lift, bind, pure, Except.bind, Except.pure]

theorem open_overflow_run (s : MachineState) (definition : BindingFrameDef)
    (full : ¬ s.nextFrameLineage < 2^64-1) :
    Sem.run (semOpenFrame definition) s = .error (.ub "OpenFrame: frame id overflow") := by
  simp [semOpenFrame, Sem.run, full, Sem.getState, Sem.throwUB,
    StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift,
    bind, pure, Except.bind, Except.pure]
  rfl

theorem bind_run (s : MachineState) (id rhs : ValueId) (lineage slot : Nat)
    (slots : List Value) (value : Value)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (operand : s.lookupValue rhs = some value)
    (live : s.openFrameLineages.contains lineage = true) (bound : slot < slots.length) :
    Sem.run (semBindSlot id slot rhs) s =
      .ok (⟨s.nextValueId⟩, afterBind s lineage slots slot value) := by
  trustIrCompilerProof {
    simp [semBindSlot, Sem.frameHandle, bindSlot, afterBind, Sem.run,
      Sem.lookupValue, Sem.rejectPartial, Sem.getState, Sem.setState, Sem.bindFresh,
      MachineState.bindValue, lookup, operand, live, bound,
      StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
      StateT.lift, bind, pure, Except.bind, Except.pure]
  } {
    dsimp only [semBindSlot, Sem.frameHandle, bindSlot, afterBind, Sem.run,
      Sem.lookupValue, Sem.rejectPartial, Sem.getState, Sem.setState, Sem.bindFresh,
      MachineState.bindValue, StateT.run, StateT.bind, StateT.get, StateT.set,
      StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
    rw [lookup]
    dsimp only [StateT.bind, StateT.get, StateT.set, StateT.pure, bind, pure,
      Except.bind, Except.pure]
    rw [if_pos live]
    dsimp only [StateT.bind, StateT.get, StateT.set, StateT.pure, bind, pure,
      Except.bind, Except.pure]
    rw [operand]
    dsimp only [StateT.bind, StateT.get, StateT.set, StateT.pure, bind, pure,
      Except.bind, Except.pure]
    rw [if_pos bound]
    dsimp only [StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
      bind, pure, Except.bind, Except.pure]
    rw [lookup]
    dsimp only [StateT.pure, Pure.pure, Except.pure, bindSlot]
    rw [if_pos bound] <;> rfl
  }

theorem removed_lineage_closed (lineages : List Nat) (lineage : Nat) :
    (lineages.filter (fun id => id != lineage)).contains lineage = false  := by
  cases found : (lineages.filter (fun id => id != lineage)).contains lineage with
  | false => rfl
  | true =>
    have kept := (List.mem_filter.mp (List.mem_of_elem_eq_true found)).2
    simpa using kept

private theorem run_bind {α β : Type} (m : Sem α) (k : α → Sem β) (s : MachineState) :
    Sem.run (m >>= k) s = (Sem.run m s >>= fun pair => Sem.run (k pair.1) pair.2) := rfl

/-- Closing any snapshot invalidates reads through every same-lineage snapshot,
including different SSA ids and different slot contents. No bounds premise. -/
theorem close_alias_load (s : MachineState) (id alias : ValueId)
    (lineage slot : Nat) (slots aliasSlots : List Value) (ty : Ty)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (other : s.lookupValue alias = some (.frame lineage aliasSlots))
    (live : s.openFrameLineages.contains lineage = true) :
    Sem.run (do semCloseFrame id; semLoadSlot alias slot ty) s =
      .error (.ub "LoadSlot: frame is not open") := by
  rw [run_bind, close_run s id lineage slots lookup live]
  exact closed_frame_load (afterClose s lineage) alias lineage slot aliasSlots ty other
    (removed_lineage_closed _ _)

/-- Closure takes priority over both bounds and lookup of the bind operand. -/
theorem close_alias_bind (s : MachineState) (id alias rhs : ValueId)
    (lineage slot : Nat) (slots aliasSlots : List Value)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (other : s.lookupValue alias = some (.frame lineage aliasSlots))
    (live : s.openFrameLineages.contains lineage = true) :
    Sem.run (do semCloseFrame id; semBindSlot alias slot rhs) s =
      .error (.ub "BindSlot: frame is not open") := by
  rw [run_bind, close_run s id lineage slots lookup live]
  exact closed_frame_bind (afterClose s lineage) alias rhs lineage slot aliasSlots other
    (removed_lineage_closed _ _)

theorem close_alias_double_close (s : MachineState) (id alias : ValueId)
    (lineage : Nat) (slots aliasSlots : List Value)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (other : s.lookupValue alias = some (.frame lineage aliasSlots))
    (live : s.openFrameLineages.contains lineage = true) :
    Sem.run (do semCloseFrame id; semCloseFrame alias) s =
      .error (.ub "CloseFrame: frame is not open (double close)") := by
  rw [run_bind, close_run s id lineage slots lookup live]
  exact closed_frame_close (afterClose s lineage) alias lineage aliasSlots other
    (removed_lineage_closed _ _)

/-- Closing one lineage leaves every distinct lineage's liveness unchanged. -/
theorem close_preserves_other (lineages : List Nat) (lineage other : Nat)
    (different : other ≠ lineage) :
    (lineages.filter (fun id => id != lineage)).contains other = lineages.contains other := by
  cases original : lineages.contains other with
  | false =>
    cases filtered : (lineages.filter (fun id => id != lineage)).contains other with
    | false => rfl
    | true =>
      have wasLive := List.elem_eq_true_of_mem
        (List.mem_filter.mp (List.mem_of_elem_eq_true filtered)).1
      change List.elem other lineages = false at original
      rw [original] at wasLive
      contradiction
  | true =>
    exact List.elem_eq_true_of_mem (List.mem_filter.mpr
      ⟨List.mem_of_elem_eq_true original, (by first | exact (bne_iff_ne _ _).2 different | exact bne_iff_ne.mpr different)⟩)

/-- Slot updates keep the lineage table and counter exactly, even if the
SSA counter is unrelated to runtime lineage identities. -/
theorem bind_preserves_lifetime (s : MachineState) (lineage : Nat)
    (slots : List Value) (slot : Nat) (value : Value) :
    (afterBind s lineage slots slot value).openFrameLineages = s.openFrameLineages ∧
    (afterBind s lineage slots slot value).nextFrameLineage = s.nextFrameLineage := ⟨rfl,rfl⟩

theorem open_counter_strict (s : MachineState) (definition : BindingFrameDef) :
    s.nextFrameLineage < (afterOpen s definition).nextFrameLineage := Nat.lt_succ_self _

/-- A previously minted closed identity is not revived by a later allocation.
The strict-past premise is essential: arbitrary forged states may put a frame
at their next unallocated identity, and are not silently treated as fresh. -/
theorem open_keeps_past_closed (s : MachineState) (definition : BindingFrameDef)
    (lineage : Nat) (past : lineage < s.nextFrameLineage)
    (closed : s.openFrameLineages.contains lineage = false) :
    (afterOpen s definition).openFrameLineages.contains lineage = false  := by
  cases found : (afterOpen s definition).openFrameLineages.contains lineage with
  | false => rfl
  | true =>
    have member := List.mem_of_elem_eq_true found
    change lineage ∈ s.nextFrameLineage :: s.openFrameLineages at member
    rcases List.mem_cons.mp member with same | old
    · exact False.elim ((Nat.ne_of_lt past) same)
    · have original := List.elem_eq_true_of_mem old
      change s.openFrameLineages.contains lineage = true at original
      rw [closed] at original
      cases original

theorem bind_retains_old_snapshot (s : MachineState) (id : ValueId)
    (lineage : Nat) (slots : List Value) (slot : Nat) (value : Value)
    (different : id ≠ ⟨s.nextValueId⟩) :
    (afterBind s lineage slots slot value).lookupValue id = s.lookupValue id := by
  simp [afterBind, MachineState.lookupValue, ValueMap.get, ValueMap.set, different]

theorem bind_new_snapshot (s : MachineState) (lineage : Nat)
    (slots : List Value) (slot : Nat) (value : Value) :
    (afterBind s lineage slots slot value).lookupValue ⟨s.nextValueId⟩ =
      some (.frame lineage (slots.set slot value)) := by
  simp [afterBind, MachineState.lookupValue, ValueMap.get, ValueMap.set]

/-- The complete dynamic bind/close/read chain: any successful functional
update is invalidated when its original snapshot is closed. The original
snapshot must occupy an already allocated SSA id, not the fresh destination. -/
theorem bind_close_load (s : MachineState) (id rhs : ValueId)
    (lineage slot readSlot : Nat) (slots : List Value) (value : Value) (ty : Ty)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (operand : s.lookupValue rhs = some value)
    (live : s.openFrameLineages.contains lineage = true) (bound : slot < slots.length)
    (different : id ≠ ⟨s.nextValueId⟩) :
    Sem.run (do
      let newer ← semBindSlot id slot rhs
      semCloseFrame id
      semLoadSlot newer readSlot ty) s = .error (.ub "LoadSlot: frame is not open") := by
  rw [run_bind, bind_run s id rhs lineage slot slots value lookup operand live bound]
  apply close_alias_load (afterBind s lineage slots slot value) id ⟨s.nextValueId⟩
    lineage readSlot slots (slots.set slot value) ty
  · rw [bind_retains_old_snapshot s id lineage slots slot value different]
    exact lookup
  · exact bind_new_snapshot s lineage slots slot value
  · exact live

theorem open_retains_other_lookup (s : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (different : id ≠ ⟨s.nextValueId⟩) :
    (afterOpen s definition).lookupValue id = s.lookupValue id := by
  simp [afterOpen, MachineState.lookupValue, ValueMap.get, ValueMap.set, different]

/-- Reopening a declaration cannot revive any earlier closed snapshot.
The strict-past counter and non-overwritten SSA premises expose exactly the
runtime freshness required; the declaration itself may be reused. -/
theorem open_does_not_revive_alias (s : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (lineage slot : Nat) (slots : List Value) (ty : Ty)
    (room : s.nextFrameLineage < 2^64-1) (past : lineage < s.nextFrameLineage)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (closed : s.openFrameLineages.contains lineage = false)
    (different : id ≠ ⟨s.nextValueId⟩) :
    Sem.run (do let _ ← semOpenFrame definition; semLoadSlot id slot ty) s =
      .error (.ub "LoadSlot: frame is not open") := by
  rw [run_bind, open_run s definition room]
  apply closed_frame_load (afterOpen s definition) id lineage slot slots ty
  · rw [open_retains_other_lookup s definition id different]
    exact lookup
  · exact open_keeps_past_closed s definition lineage past closed

/-- The compositional history invariant: counters never decrease, and a
closed identity older than the current counter stays closed. This is a
relation on runtime state, not a replacement instruction interpreter. -/
structure HistoryExtends (before after : MachineState) : Prop where
  monotone : before.nextFrameLineage ≤ after.nextFrameLineage
  closed : ∀ lineage, lineage < before.nextFrameLineage →
    before.openFrameLineages.contains lineage = false →
    after.openFrameLineages.contains lineage = false

theorem HistoryExtends.refl (s : MachineState) : HistoryExtends s s :=
  ⟨Nat.le_refl _, fun _ _ closed => closed⟩

/-- Any finite composition inherits the no-revival property. -/
theorem HistoryExtends.trans {s t u : MachineState}
    (first : HistoryExtends s t) (second : HistoryExtends t u) : HistoryExtends s u := by
  constructor
  · exact Nat.le_trans first.monotone second.monotone
  · intro lineage past closed
    exact second.closed lineage (Nat.lt_of_lt_of_le past first.monotone)
      (first.closed lineage past closed)

theorem history_open (s : MachineState) (definition : BindingFrameDef) :
    HistoryExtends s (afterOpen s definition) :=
  ⟨Nat.le_succ _, fun lineage past closed => open_keeps_past_closed s definition lineage past closed⟩

/-- Every successful actual OpenFrame extends the history and increments its
counter exactly once. No allocation-room premise is assumed from the caller. -/
theorem open_success_history (s final : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (run : Sem.run (semOpenFrame definition) s = .ok (id, final)) :
    HistoryExtends s final ∧ final.nextFrameLineage = s.nextFrameLineage + 1 := by
  by_cases room : s.nextFrameLineage < 2^64-1
  · rw [open_run s definition room] at run
    cases run
    exact ⟨history_open s definition, rfl⟩
  · rw [open_overflow_run s definition room] at run
    contradiction

theorem history_close (s : MachineState) (lineage : Nat) :
    HistoryExtends s (afterClose s lineage) := by
  constructor
  · exact Nat.le_refl _
  · intro other _ closed
    by_cases same : other = lineage
    · subst other
      exact removed_lineage_closed _ _
    · change (s.openFrameLineages.filter (fun id => id != lineage)).contains other = false
      rw [close_preserves_other _ _ _ same]
      exact closed

theorem history_bind (s : MachineState) (lineage : Nat)
    (slots : List Value) (slot : Nat) (value : Value) :
    HistoryExtends s (afterBind s lineage slots slot value) :=
  ⟨Nat.le_refl _, fun _ _ closed => closed⟩

/-- Restoring a caller retains the callee's complete runtime frame history,
including closures and fresh identities minted in the callee. -/
theorem history_restore (s : MachineState) (frame : StackFrame) (ret : List Value) :
    HistoryExtends s (restoreFrame s frame ret) := by
  have fields := restoreFrame_preserves_lineage s frame ret
  constructor
  · rw [fields.2]
    exact Nat.le_refl _
  · intro lineage _ closed
    rw [fields.1]
    exact closed

/-- Resetting SSA for a callee cannot rewind dynamic frame identity. -/
theorem history_clear_locals (s : MachineState) :
    HistoryExtends s { s with locals := ValueMap.empty, nextValueId := 0 } :=
  ⟨Nat.le_refl _, fun _ _ closed => closed⟩

/-- The successful-open state characterized by open_run, followed by any history extension, cannot
resurrect a previously closed minted lineage. -/
theorem closed_through_open_and_history (s final : MachineState) (definition : BindingFrameDef)
    (lineage : Nat) (past : lineage < s.nextFrameLineage)
    (closed : s.openFrameLineages.contains lineage = false)
    (tail : HistoryExtends (afterOpen s definition) final) :
    final.openFrameLineages.contains lineage = false :=
  ((history_open s definition).trans tail).closed lineage past closed

/-- Negative boundary: an externally forged handle at the NEXT identity can
be revived by open. This refutes dropping the strict-past premise; it is not
an executable history from empty. -/
theorem forged_future_identity_can_revive :
    let s := { MachineState.empty with
      locals := ValueMap.empty.set ⟨0⟩ (.frame 0 [.int 32 7])
      nextValueId := 1 }
    s.openFrameLineages.contains 0 = false ∧
    (Sem.run (do
      let _ ← semOpenFrame ⟨⟨0⟩, "forged", []⟩
      let value ← semLoadSlot ⟨0⟩ 0 .I32
      Sem.lookupValue value) s).map Prod.fst = .ok (.int 32 7) := ⟨rfl,rfl⟩

/-- Negative boundary: a forged non-fresh SSA counter permits overwriting the
old handle. Snapshot preservation explicitly excludes this case. -/
theorem nonfresh_ssa_can_overwrite_snapshot :
    let s := { MachineState.empty with
      locals := (ValueMap.empty.set ⟨0⟩ (.frame 1 [.int 32 7])).set ⟨1⟩ (.int 32 9)
      nextValueId := 0
      openFrameLineages := [1]
      nextFrameLineage := 2 }
    (Sem.run (do
      let _ ← semBindSlot ⟨0⟩ 0 ⟨1⟩
      Sem.lookupValue ⟨0⟩) s).map Prod.fst = .ok (.frame 1 [.int 32 9]) := rfl

/-- Allocation well-formedness: every live dynamic frame identity has already
been minted. This says nothing about slot types, SSA freshness or LIFO closure. -/
def MintedLineages (s : MachineState) : Prop :=
  ∀ lineage, lineage ∈ s.openFrameLineages → lineage < s.nextFrameLineage

theorem minted_empty : MintedLineages MachineState.empty := by
  intro lineage member
  cases member

theorem minted_open (s : MachineState) (definition : BindingFrameDef)
    (valid : MintedLineages s) : MintedLineages (afterOpen s definition) := by
  intro lineage member
  change lineage ∈ s.nextFrameLineage :: s.openFrameLineages at member
  cases member with
  | head => exact Nat.lt_succ_self _
  | tail _ member => exact Nat.lt_trans (valid lineage member) (Nat.lt_succ_self _)

theorem minted_close (s : MachineState) (lineage : Nat)
    (valid : MintedLineages s) : MintedLineages (afterClose s lineage) := by
  intro other member
  exact valid other (List.mem_filter.mp member).1

theorem minted_bind (s : MachineState) (lineage : Nat) (slots : List Value)
    (slot : Nat) (value : Value) (valid : MintedLineages s) :
    MintedLineages (afterBind s lineage slots slot value) := valid

theorem minted_restore (s : MachineState) (frame : StackFrame) (ret : List Value)
    (valid : MintedLineages s) : MintedLineages (restoreFrame s frame ret) := by
  have fields := restoreFrame_preserves_lineage s frame ret
  intro lineage member
  rw [fields.2]
  rw [fields.1] at member
  exact valid lineage member

/-- The real successful allocator preserves minted identities; allocation room
is derived from success rather than assumed by the client. -/
theorem minted_open_success (s final : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (valid : MintedLineages s)
    (run : Sem.run (semOpenFrame definition) s = .ok (id, final)) :
    MintedLineages final := by
  by_cases room : s.nextFrameLineage < 2^64-1
  · rw [open_run s definition room] at run
    cases run
    exact minted_open s definition valid
  · rw [open_overflow_run s definition room] at run
    contradiction

/-- Direct frame operands must name minted identities, even when already
closed. Nested values are outside this operand-level relation. -/
def MintedHandles (bound : Nat) (locals : ValueMap) : Prop :=
  ∀ id lineage slots, locals.get id = some (.frame lineage slots) → lineage < bound

theorem handles_empty (bound : Nat) : MintedHandles bound ValueMap.empty := by
  intro id lineage slots lookup
  cases lookup

theorem handles_mono {before after : Nat} {locals : ValueMap}
    (valid : MintedHandles before locals) (monotone : before ≤ after) :
    MintedHandles after locals := by
  intro id lineage slots lookup
  exact Nat.lt_of_lt_of_le (valid id lineage slots lookup) monotone

/-- Insertion requires the inserted operand itself to respect the bound.
No freshness assumption is needed: overwriting cannot forge a new lineage. -/
theorem handles_set {bound : Nat} {locals : ValueMap}
    (valid : MintedHandles bound locals) (dest : ValueId) (value : Value)
    (operand : ∀ lineage slots, value = .frame lineage slots → lineage < bound) :
    MintedHandles bound (locals.set dest value) := by
  intro id lineage slots lookup
  by_cases same : id = dest
  · subst id
    simp [ValueMap.get, ValueMap.set] at lookup
    exact operand lineage slots lookup
  · simp [ValueMap.get, ValueMap.set, same] at lookup
    exact valid id lineage slots lookup

theorem handles_open (s : MachineState) (definition : BindingFrameDef)
    (valid : MintedHandles s.nextFrameLineage s.locals) :
    MintedHandles (afterOpen s definition).nextFrameLineage
      (afterOpen s definition).locals := by
  apply handles_set (handles_mono valid (Nat.le_succ _))
  intro lineage slots equal
  simp [initFrame] at equal
  rw [← equal.1]
  exact Nat.lt_succ_self _

theorem handles_close (s : MachineState) (lineage : Nat)
    (valid : MintedHandles s.nextFrameLineage s.locals) :
    MintedHandles (afterClose s lineage).nextFrameLineage
      (afterClose s lineage).locals := valid

theorem handles_bind (s : MachineState) (id : ValueId) (lineage slot : Nat)
    (slots : List Value) (value : Value)
    (valid : MintedHandles s.nextFrameLineage s.locals)
    (lookup : s.lookupValue id = some (.frame lineage slots)) :
    MintedHandles (afterBind s lineage slots slot value).nextFrameLineage
      (afterBind s lineage slots slot value).locals := by
  apply handles_set valid
  intro other otherSlots equal
  cases equal
  exact valid id lineage slots lookup

/-- Caller locals and a returned operand must each be well formed at the
callee's current counter. They cannot be inferred from the callee's locals. -/
theorem handles_restore (s : MachineState) (frame : StackFrame) (ret : List Value)
    (saved : MintedHandles s.nextFrameLineage frame.locals)
    (returned : ∀ value ∈ ret, ∀ lineage slots,
      value = .frame lineage slots → lineage < s.nextFrameLineage) :
    MintedHandles (restoreFrame s frame ret).nextFrameLineage
      (restoreFrame s frame ret).locals := by
  cases destEq : frame.returnDest with
  | none => simpa [restoreFrame, destEq] using saved
  | some dest =>
    cases ret with
    | nil => simpa [restoreFrame, destEq] using saved
    | cons value rest =>
      cases rest with
      | nil =>
        simpa [restoreFrame, destEq] using
          handles_set saved dest value (returned value (by simp))
      | cons next tail => simpa [restoreFrame, destEq] using saved

/-- Previously minted saved locals remain admissible after a callee extends
frame history, including when it closes caller-owned identities. -/
theorem handles_saved_history (before after : MachineState) (frame : StackFrame)
    (saved : MintedHandles before.nextFrameLineage frame.locals)
    (history : HistoryExtends before after) :
    MintedHandles after.nextFrameLineage frame.locals :=
  handles_mono saved history.monotone

/-- Derive the strict-past premise of no revival from an operand lookup. -/
theorem handles_open_closed (s : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (lineage : Nat) (slots : List Value)
    (valid : MintedHandles s.nextFrameLineage s.locals)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (closed : s.openFrameLineages.contains lineage = false) :
    (afterOpen s definition).openFrameLineages.contains lineage = false :=
  open_keeps_past_closed s definition lineage (valid id lineage slots lookup) closed

/-- A valid callee state does not sanitize externally forged saved locals. -/
theorem restore_forged_saved_handle :
    ¬ MintedHandles 0
      (restoreFrame MachineState.empty
        ⟨ValueMap.empty.set ⟨0⟩ (.frame 0 []), none, 1⟩ []).locals := by
  intro valid
  exact Nat.not_lt_zero 0 (valid ⟨0⟩ 0 [] rfl)

/-- A singleton return can introduce a forged handle even with empty saved locals. -/
theorem restore_forged_return_handle :
    ¬ MintedHandles 0
      (restoreFrame MachineState.empty
        ⟨ValueMap.empty, some ⟨0⟩, 1⟩ [.frame 0 []]).locals := by
  intro valid
  exact Nat.not_lt_zero 0 (valid ⟨0⟩ 0 [] rfl)

/-- A snapshot's immutable declaration origin. `none` is the original
unqualified carrier; a source carrier retains the complete original row. -/
def frameValue (origin : Option (FuncId × BindingFrameDef)) (lineage : Nat)
    (slots : List Value) : Value :=
  match origin with
  | none => .frame lineage slots
  | some (function, declaration) => .sourceFrame lineage function declaration slots

/-- Successful inspection exposes the exact operand, including any immutable
source origin, and leaves state unchanged. No origin is synthesized from slots. -/
theorem frameHandle_success (s final : MachineState) (id : ValueId) (op : String)
    (lineage : Nat) (slots : List Value)
    (run : Sem.run (Sem.frameHandle id op) s = .ok ((lineage, slots), final)) :
    ∃ origin, s.lookupValue id = some (frameValue origin lineage slots) ∧ final = s := by
  cases lookup : s.lookupValue id with
  | none =>
    simp [Sem.frameHandle, Sem.lookupValue, Sem.run, Sem.getState,
      Sem.throwTypeError, lookup, StateT.run, StateT.bind, StateT.get,
      StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some value =>
    cases value <;>
      simp [Sem.frameHandle, Sem.lookupValue, Sem.rejectPartial, Sem.run,
        Sem.getState, Sem.throwTypeError, Sem.throwUB, lookup,
        StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift,
        bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
    case frame heldLineage heldSlots =>
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨none, rfl, rfl⟩
    case sourceFrame heldLineage function declaration heldSlots =>
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨some (function, declaration), rfl, rfl⟩

/-- Both allocation invariants follow from an actual successful OpenFrame. -/
theorem open_success_well_minted (s final : MachineState) (definition : BindingFrameDef)
    (id : ValueId) (table : MintedLineages s)
    (handles : MintedHandles s.nextFrameLineage s.locals)
    (run : Sem.run (semOpenFrame definition) s = .ok (id, final)) :
    MintedLineages final ∧ MintedHandles final.nextFrameLineage final.locals := by
  by_cases room : s.nextFrameLineage < 2^64-1
  · rw [open_run s definition room] at run
    cases run
    exact ⟨minted_open s definition table, handles_open s definition handles⟩
  · rw [open_overflow_run s definition room] at run
    contradiction

/-- Any successful continuation after inspection receives the exact frame
operand and source origin from the original state. -/
theorem frameHandle_bind_success {α : Type} (s final : MachineState)
    (id : ValueId) (op : String) (k : Nat × List Value → Sem α) (result : α)
    (run : Sem.run (Sem.frameHandle id op >>= k) s = .ok (result, final)) :
    ∃ origin lineage slots, s.lookupValue id = some (frameValue origin lineage slots) ∧
      Sem.run (k (lineage, slots)) s = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run (Sem.frameHandle id op) s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair =>
    rcases pair with ⟨⟨lineage, slots⟩, after⟩
    obtain ⟨origin, lookup, rfl⟩ := frameHandle_success s after id op lineage slots step
    exact ⟨origin, lineage, slots, lookup, by simpa [step] using run⟩

private theorem close_origin_run (s : MachineState) (id : ValueId)
    (origin : Option (FuncId × BindingFrameDef)) (lineage : Nat) (slots : List Value)
    (lookup : s.lookupValue id = some (frameValue origin lineage slots))
    (live : s.openFrameLineages.contains lineage = true) :
    Sem.run (semCloseFrame id) s = .ok ((), afterClose s lineage) := by
  trustIrCompilerProof {
    have isOpen := live
  } {
    have isOpen := List.mem_of_elem_eq_true live
  }
  cases origin with
  | none => exact close_run s id lineage slots lookup live
  | some origin =>
    rcases origin with ⟨function, declaration⟩
    simp [frameValue] at lookup
    simp [semCloseFrame, Sem.frameHandle, Sem.setFrameState, afterClose,
      Sem.run, Sem.lookupValue, Sem.rejectPartial, Sem.getState, Sem.setState,
      lookup, live, isOpen, StateT.run, StateT.bind, StateT.get, StateT.set,
      StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]

/-- Successful close identifies the actual origin, closed lineage and exact
resulting state. Both carriers share one runtime lifetime table. -/
theorem close_success_state (s final : MachineState) (id : ValueId)
    (run : Sem.run (semCloseFrame id) s = .ok ((), final)) :
    ∃ origin lineage slots, s.lookupValue id = some (frameValue origin lineage slots) ∧
      s.openFrameLineages.contains lineage = true ∧ final = afterClose s lineage := by
  obtain ⟨origin, lineage, slots, lookup, tail⟩ :=
    frameHandle_bind_success s final id "CloseFrame" _ () run
  cases live : s.openFrameLineages.contains lineage with
  | false =>
    trustIrCompilerProof {
      simp [Sem.run, Sem.getState, live, Sem.throwUB, StateT.run,
        StateT.bind, StateT.get, StateT.lift, bind, pure, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    } {
      have closed : lineage ∉ s.openFrameLineages := by
        intro present
        have on : s.openFrameLineages.contains lineage = true :=
          List.elem_eq_true_of_mem present
        rw [live] at on
        cases on
      simp [Sem.run, Sem.getState, live, closed, Sem.throwUB, StateT.run,
        StateT.bind, StateT.get, StateT.lift, bind, pure, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    }
  | true =>
    rw [close_origin_run s id origin lineage slots lookup live] at run
    cases run
    exact ⟨origin, lineage, slots, lookup, live, rfl⟩

theorem close_success_well_minted (s final : MachineState) (id : ValueId)
    (table : MintedLineages s) (handles : MintedHandles s.nextFrameLineage s.locals)
    (run : Sem.run (semCloseFrame id) s = .ok ((), final)) :
    MintedLineages final ∧ MintedHandles final.nextFrameLineage final.locals := by
  obtain ⟨_, lineage, _, _, _, rfl⟩ := close_success_state s final id run
  exact ⟨minted_close s lineage table, handles_close s lineage handles⟩

def afterBindOrigin (s : MachineState) (origin : Option (FuncId × BindingFrameDef))
    (lineage : Nat) (slots : List Value) (slot : Nat) (value : Value) : MachineState :=
  { s with
    locals := s.locals.set ⟨s.nextValueId⟩ (frameValue origin lineage (slots.set slot value))
    nextValueId := s.nextValueId + 1 }

private theorem bind_origin_run (s : MachineState) (id rhs : ValueId)
    (origin : Option (FuncId × BindingFrameDef)) (lineage slot : Nat)
    (slots : List Value) (value : Value)
    (lookup : s.lookupValue id = some (frameValue origin lineage slots))
    (operand : s.lookupValue rhs = some value)
    (live : s.openFrameLineages.contains lineage = true) (bound : slot < slots.length) :
    Sem.run (semBindSlot id slot rhs) s =
      .ok (⟨s.nextValueId⟩, afterBindOrigin s origin lineage slots slot value) := by
  trustIrCompilerProof {
    have isOpen := live
  } {
    have isOpen := List.mem_of_elem_eq_true live
  }
  cases origin with
  | none => exact bind_run s id rhs lineage slot slots value lookup operand live bound
  | some origin =>
    rcases origin with ⟨function, declaration⟩
    simp [frameValue] at lookup
    simp [semBindSlot, Sem.frameHandle, bindSlot, afterBindOrigin, frameValue, Sem.run,
      Sem.lookupValue, Sem.rejectPartial, Sem.getState, Sem.setState, Sem.bindFresh,
      MachineState.bindValue, lookup, operand, live, isOpen, bound,
      StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure,
      StateT.lift, bind, pure, Except.bind, Except.pure]

/-- A successful bind preserves the actual immutable origin and lineage,
recovers the real RHS and yields the exact functional snapshot state. -/
theorem bind_success_state (s final : MachineState) (id rhs result : ValueId) (slot : Nat)
    (run : Sem.run (semBindSlot id slot rhs) s = .ok (result, final)) :
    ∃ origin lineage slots value, s.lookupValue id = some (frameValue origin lineage slots) ∧
      s.lookupValue rhs = some value ∧ s.openFrameLineages.contains lineage = true ∧
      slot < slots.length ∧ result = ⟨s.nextValueId⟩ ∧
      final = afterBindOrigin s origin lineage slots slot value := by
  obtain ⟨origin, lineage, slots, lookup, tail⟩ :=
    frameHandle_bind_success s final id "BindSlot" _ result run
  cases live : s.openFrameLineages.contains lineage with
  | false =>
    trustIrCompilerProof {
      simp [Sem.run, Sem.getState, live, Sem.throwUB, StateT.run,
        StateT.bind, StateT.get, StateT.lift, bind, pure, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    } {
      have closed : lineage ∉ s.openFrameLineages := by
        intro present
        have on : s.openFrameLineages.contains lineage = true :=
          List.elem_eq_true_of_mem present
        rw [live] at on
        cases on
      simp [Sem.run, Sem.getState, live, closed, Sem.throwUB, StateT.run,
        StateT.bind, StateT.get, StateT.lift, bind, pure, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    }
  | true =>
    trustIrCompilerProof {
      have isOpen := live
    } {
      have isOpen := List.mem_of_elem_eq_true live
    }
    cases operand : s.lookupValue rhs with
    | none =>
      simp [Sem.run, Sem.lookupValue, Sem.getState, Sem.throwTypeError,
        live, isOpen, operand, StateT.run, StateT.bind, StateT.get,
        StateT.lift, bind, pure, Except.bind, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at tail
    | some value =>
      by_cases bound : slot < slots.length
      · rw [bind_origin_run s id rhs origin lineage slot slots value lookup operand live bound] at run
        cases run
        exact ⟨origin, lineage, slots, value, lookup, rfl, live, bound, rfl, rfl⟩
      · simp [Sem.run, Sem.lookupValue, Sem.getState, Sem.throwUB,
          live, isOpen, operand, bound, StateT.run, StateT.bind, StateT.get,
          StateT.lift, StateT.pure, bind, pure, Except.bind, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at tail

theorem bind_success_well_minted (s final : MachineState) (id rhs result : ValueId)
    (slot : Nat) (table : MintedLineages s)
    (handles : MintedHandles s.nextFrameLineage s.locals)
    (run : Sem.run (semBindSlot id slot rhs) s = .ok (result, final)) :
    MintedLineages final ∧ MintedHandles final.nextFrameLineage final.locals := by
  obtain ⟨origin, lineage, slots, value, lookup, _, _, _, _, rfl⟩ :=
    bind_success_state s final id rhs result slot run
  constructor
  · exact table
  · cases origin with
    | none => exact handles_bind s id lineage slot slots value handles lookup
    | some origin =>
      rcases origin with ⟨function, declaration⟩
      apply handles_set handles
      intro other otherSlots equal
      cases equal

def afterLoad (s : MachineState) (value : Value) : MachineState :=
  { s with locals := s.locals.set ⟨s.nextValueId⟩ value, nextValueId := s.nextValueId + 1 }

theorem load_run (s : MachineState) (id : ValueId) (lineage slot : Nat)
    (slots : List Value) (value : Value) (ty : Ty)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (live : s.openFrameLineages.contains lineage = true) (found : trustIrListGet? slots slot = some value) :
    Sem.run (semLoadSlot id slot ty) s = .ok (⟨s.nextValueId⟩, afterLoad s value) := by
  trustIrCompilerProof {
      simp [semLoadSlot, Sem.frameHandle, Sem.lookupValue, Sem.rejectPartial,
        Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, MachineState.bindValue, afterLoad,
        lookup, live, found, StateT.run, StateT.bind, StateT.get, StateT.set,
        StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
  } {
      have isOpen : lineage ∈ s.openFrameLineages := List.mem_of_elem_eq_true live
      simp [semLoadSlot, Sem.frameHandle, Sem.lookupValue, Sem.rejectPartial,
        Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, MachineState.bindValue, afterLoad,
        lookup, live, isOpen, found, StateT.run, StateT.bind, StateT.get, StateT.set,
        StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
  }

private theorem load_origin_run (s : MachineState) (id : ValueId)
    (origin : Option (FuncId × BindingFrameDef)) (lineage slot : Nat)
    (slots : List Value) (value : Value) (ty : Ty)
    (lookup : s.lookupValue id = some (frameValue origin lineage slots))
    (live : s.openFrameLineages.contains lineage = true)
    (found : trustIrListGet? slots slot = some value) :
    Sem.run (semLoadSlot id slot ty) s = .ok (⟨s.nextValueId⟩, afterLoad s value) := by
  trustIrCompilerProof {
    have isOpen := live
  } {
    have isOpen := List.mem_of_elem_eq_true live
  }
  cases origin with
  | none => exact load_run s id lineage slot slots value ty lookup live found
  | some origin =>
    rcases origin with ⟨function, declaration⟩
    simp [frameValue] at lookup
    simp [semLoadSlot, Sem.frameHandle, Sem.lookupValue, Sem.rejectPartial,
      Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, MachineState.bindValue, afterLoad,
      lookup, live, isOpen, found, StateT.run, StateT.bind, StateT.get, StateT.set,
      StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]

theorem load_success_state (s final : MachineState) (id result : ValueId)
    (slot : Nat) (ty : Ty)
    (run : Sem.run (semLoadSlot id slot ty) s = .ok (result, final)) :
    ∃ origin lineage slots value, s.lookupValue id = some (frameValue origin lineage slots) ∧
      s.openFrameLineages.contains lineage = true ∧ trustIrListGet? slots slot = some value ∧
      result = ⟨s.nextValueId⟩ ∧ final = afterLoad s value := by
  obtain ⟨origin, lineage, slots, lookup, tail⟩ :=
    frameHandle_bind_success s final id "LoadSlot" _ result run
  cases live : s.openFrameLineages.contains lineage with
  | false =>
    trustIrCompilerProof {
      simp [Sem.run, Sem.getState, live, Sem.throwUB, StateT.run,
        StateT.bind, StateT.get, StateT.lift, bind, pure, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    } {
      have closed : lineage ∉ s.openFrameLineages := by
        intro present
        have on : s.openFrameLineages.contains lineage = true :=
          List.elem_eq_true_of_mem present
        rw [live] at on
        cases on
      simp [Sem.run, Sem.getState, live, closed, Sem.throwUB, StateT.run,
        StateT.bind, StateT.get, StateT.lift, bind, pure, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    }
  | true =>
    trustIrCompilerProof {
      have isOpen := live
    } {
      have isOpen := List.mem_of_elem_eq_true live
    }
    cases found : trustIrListGet? slots slot with
    | none =>
      simp [Sem.run, Sem.getState, Sem.throwUB, live, isOpen, found,
        StateT.run, StateT.bind, StateT.get, StateT.lift, bind, pure,
        Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    | some value =>
      rw [load_origin_run s id origin lineage slot slots value ty lookup live found] at run
      cases run
      exact ⟨origin, lineage, slots, value, lookup, live, found, rfl, rfl⟩

/-- Load requires a bound for the selected slot's direct generic-frame handle,
if any, from either actual outer carrier. It cannot follow from the outer
identity alone; recursive validity supplies this premise in FrameValueValidity. -/
theorem load_success_well_minted (s final : MachineState) (id result : ValueId)
    (slot : Nat) (ty : Ty) (table : MintedLineages s)
    (handles : MintedHandles s.nextFrameLineage s.locals)
    (slotHandles : ∀ origin lineage slots value,
      s.lookupValue id = some (frameValue origin lineage slots) →
      trustIrListGet? slots slot = some value →
      ∀ other innerSlots, value = .frame other innerSlots → other < s.nextFrameLineage)
    (run : Sem.run (semLoadSlot id slot ty) s = .ok (result, final)) :
    MintedLineages final ∧ MintedHandles final.nextFrameLineage final.locals := by
  obtain ⟨origin, lineage, slots, value, lookup, _, found, _, rfl⟩ :=
    load_success_state s final id result slot ty run
  exact ⟨table, handles_set handles _ value (slotHandles origin lineage slots value lookup found)⟩

/-- A well-minted outer handle can contain a forged inner handle. The actual
load succeeds and exposes it, refuting unconditional direct-handle preservation. -/
theorem load_can_expose_future_handle :
    let s := { MachineState.empty with
      locals := ValueMap.empty.set ⟨0⟩ (.frame 0 [.frame 1 []])
      nextValueId := 1, openFrameLineages := [0], nextFrameLineage := 1 }
    MintedLineages s ∧ MintedHandles 1 s.locals ∧
      (Sem.run (semLoadSlot ⟨0⟩ 0 .Unit) s).map Prod.fst = .ok ⟨1⟩ ∧
      ¬ MintedHandles 1 (afterLoad s (.frame 1 [])).locals := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro lineage member
    simp at member
    subst lineage
    exact Nat.zero_lt_succ 0
  · intro id lineage slots lookup
    by_cases same : id = ⟨0⟩
    · subst id
      simp [ValueMap.get, ValueMap.set] at lookup
      rcases lookup with ⟨rfl, _⟩
      exact Nat.zero_lt_succ 0
    · simp [ValueMap.get, ValueMap.set, same, ValueMap.empty] at lookup
  · intro valid
    exact Nat.lt_irrefl 1 (valid ⟨1⟩ 1 [] rfl)

end TrustIr.FrameLifetime

#trustIrAxiomsExact TrustIr.FrameLifetime.close_run == [propext]
#trustIrAxiomsExact TrustIr.FrameLifetime.bind_run == [propext]
