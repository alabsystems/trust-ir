-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.FrameAliasValidity
import TrustIr.Proofs.FrameResultValidity

namespace TrustIr.FrameLifetime

private theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state =
      (Sem.run action state >>= fun pair => Sem.run (next pair.1) pair.2) := rfl

private theorem split_bind_success {α β : Type} (action : Sem α) (next : α → Sem β)
    (s final : MachineState) (result : β)
    (run : Sem.run (action >>= next) s = .ok (result, final)) :
    ∃ value middle, Sem.run action s = .ok (value, middle) ∧
      Sem.run (next value) middle = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run action s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa [step] using run⟩

private theorem lookup_success (s final : MachineState) (id : ValueId) (value : Value)
    (run : Sem.run (Sem.lookupValue id) s = .ok (value, final)) :
    s.lookupValue id = some value ∧ final = s := by
  cases lookup : s.lookupValue id with
  | none =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, Sem.throwTypeError, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, lookup, StateT.run,
      StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem contextual_fresh_success (value : Value) (state final : MachineState)
    (result : InstrResult) (valid : WellMintedState state)
    (held : MintedValue state.nextFrameLineage value)
    (run : Sem.run (Sem.bindFresh value >>= fun id => pure (.value (some id))) state =
      .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final ∧ HistoryExtends state final := by
  obtain ⟨id, middle, fresh, finished⟩ := split_bind_success _ _ state final result run
  have preserved := valid.fresh_success state middle value id held fresh
  have history : HistoryExtends state middle := by
    have exactRun : Sem.run (Sem.bindFresh value) state = .ok (state.bindValue value) := rfl
    rw [exactRun] at fresh
    cases fresh
    exact ⟨Nat.le_refl _, fun _ _ closed => closed⟩
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at finished
  cases finished
  exact ⟨id, rfl, preserved, history⟩

private theorem frame_update_minted (bound : Nat) (origin : Option (FuncId × BindingFrameDef))
    (lineage : Nat) (slots : List Value) (slot : Nat) (value : Value)
    (held : MintedValue bound (frameValue origin lineage slots))
    (inserted : MintedValue bound value) :
    MintedValue bound (frameValue origin lineage (slots.set slot value)) := by
  have original := (mintedValue_frameValue_iff bound origin lineage slots).1 held
  exact (mintedValue_frameValue_iff bound origin lineage (slots.set slot value)).2
    ⟨original.1, frame_slots_set_valid bound slots slot value original.2 inserted⟩

/-- The exact state published by an authenticated source-frame allocation. -/
def afterSourceOpen (state : MachineState) (origin : FuncId) (declaration : BindingFrameDef) :
    MachineState :=
  { state with
    locals := state.locals.set ⟨state.nextValueId⟩
      (.sourceFrame state.nextFrameLineage origin declaration (declaration.slots.map (fun _ => .uninit)))
    nextValueId := state.nextValueId + 1
    openFrameLineages := state.nextFrameLineage :: state.openFrameLineages
    nextFrameLineage := state.nextFrameLineage + 1 }

theorem WellMintedState.source_open (state : MachineState) (origin : FuncId)
    (declaration : BindingFrameDef) (valid : WellMintedState state) :
    WellMintedState (afterSourceOpen state origin declaration) := by
  constructor
  · exact minted_open state declaration valid.table
  · apply values_set (values_mono valid.values (Nat.le_succ _))
    apply (mintedValue_sourceFrame_iff _ _ _ _ _).2
    constructor
    · exact Nat.lt_succ_self _
    · intro value member
      rcases List.mem_map.mp member with ⟨slot, _, rfl⟩
      intro lineage occurrence
      cases occurrence

theorem source_open_history (state : MachineState) (origin : FuncId)
    (declaration : BindingFrameDef) : HistoryExtends state (afterSourceOpen state origin declaration) :=
  ⟨(history_open state declaration).monotone, (history_open state declaration).closed⟩

/-- Contextual allocation uses the real finite declaration and uninitialized
source snapshot; its successful run mints exactly the existing fresh lineage. -/
theorem contextual_open_success (ctx : EvalContext) (declaration : BindingFrameDef)
    (state final : MachineState) (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (stepInstWithContext ctx (.OpenFrame declaration)) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final ∧ HistoryExtends state final := by
  cases origin : ctx.currentFunction with
  | none =>
    simp only [stepInstWithContext, origin] at run
    obtain ⟨id, middle, executed, finished⟩ := split_bind_success _ _ state final result run
    have preserved := valid.open_success state middle declaration id executed
    have history := open_success_history state middle declaration id executed
    change Except.ok (.value (some id), middle) = Except.ok (result, final) at finished
    cases finished
    exact ⟨id, rfl, preserved, history.1⟩
  | some function =>
    cases found : ctx.valueSource.bindingFrame function declaration.id with
    | none =>
      simp [stepInstWithContext, origin, found, Sem.throwTypeError, Sem.run, StateT.run,
        StateT.bind, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at run
    | some original =>
      cases same : bindingFrameDeclarationEq original declaration with
      | false =>
        simp [stepInstWithContext, origin, found, same, Sem.throwTypeError, Sem.run, StateT.run,
          StateT.bind, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at run
      | true =>
        by_cases room : state.nextFrameLineage < 2 ^ 64 - 1
        · have executed : Sem.run (stepInstWithContext ctx (.OpenFrame declaration)) state =
              .ok (.value (some ⟨state.nextValueId⟩), afterSourceOpen state function original) := by
            simp [stepInstWithContext, origin, found, same, room, afterSourceOpen,
              Sem.run, Sem.getState, Sem.setState, Sem.setFrameState, Sem.bindFresh,
              MachineState.bindValue, StateT.run, StateT.bind, StateT.get, StateT.set,
              StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
          rw [executed] at run
          cases run
          exact ⟨_, rfl, valid.source_open state function original,
            source_open_history state function original⟩
        · simp [stepInstWithContext, origin, found, same, room, Sem.run, Sem.getState,
            Sem.throwUB, StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift,
            bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run

/-- Actual contextual binding preserves snapshots and identities on both
ordinary and authenticated source carriers. Every refusal remains in the run. -/
theorem contextual_bind_success (ctx : EvalContext) (frame rhs : ValueId) (slot : Nat)
    (state final : MachineState) (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (stepInstWithContext ctx (.BindSlot frame slot rhs)) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final ∧ HistoryExtends state final := by
  simp only [stepInstWithContext] at run
  obtain ⟨origin, lineage, slots, lookup, tail⟩ :=
    frameHandle_bind_success state final frame "BindSlot" _ result run
  have heldValid := valid.values frame (frameValue origin lineage slots) lookup
  obtain ⟨stored, middle, fetched, tail⟩ := split_bind_success _ _ state final result tail
  change Except.ok (state, state) = Except.ok (stored, middle) at fetched
  have pair := Except.ok.inj fetched
  have storedEq : stored = state := (congrArg Prod.fst pair).symm
  have middleEq : middle = state := (congrArg Prod.snd pair).symm
  subst stored
  subst middle
  cases live : state.openFrameLineages.contains lineage with
  | false =>
    trustIrCompilerProof {
      simp [live, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
        bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    } {
      have notLive : lineage ∉ state.openFrameLineages := by simpa using live
      simp [notLive, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
        bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    }
  | true =>
    simp only [live, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at tail
    obtain ⟨held, middle, looked, tail⟩ := split_bind_success _ _ state final result tail
    obtain ⟨found, same⟩ := lookup_success state middle frame held looked
    subst middle
    rw [lookup] at found
    cases found
    cases origin with
    | none =>
      simp only [frameValue] at tail
      obtain ⟨value, middle, operand, tail⟩ := split_bind_success _ _ state final result tail
      obtain ⟨valueLookup, same⟩ := lookup_success state middle rhs value operand
      subst middle
      by_cases bound : slot < slots.length
      · simp only [bound, ↓reduceIte] at tail
        obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ state final result tail
        have same := memory_check_success_state _ state middle unit checked
        subst middle
        cases unit
        simp only [bindSlot, bound, ↓reduceIte, pure_bind] at tail
        exact contextual_fresh_success _ state final result valid
          (frame_update_minted _ none lineage slots slot value heldValid
            (valid.values rhs value valueLookup)) tail
      · simp [bound, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    | some source =>
      rcases source with ⟨function, declaration⟩
      simp only [frameValue] at tail
      obtain ⟨types, middle, checkedTypes, tail⟩ := split_bind_success _ _ state final result tail
      have same := memory_check_success_state _ state middle types checkedTypes
      subst middle
      obtain ⟨value, middle, operand, tail⟩ := split_bind_success _ _ state final result tail
      obtain ⟨valueLookup, same⟩ := lookup_success state middle rhs value operand
      subst middle
      cases declared : trustIrListGet? types slot with
      | none =>
        simp [declared, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
      | some ty =>
        simp only [declared, pure_bind] at tail
        obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ state final result tail
        have same := memory_check_success_state _ state middle unit checked
        subst middle
        cases unit
        by_cases bound : slot < slots.length
        · simp only [bindSlot, bound, ↓reduceIte, pure_bind] at tail
          exact contextual_fresh_success _ state final result valid
            (frame_update_minted _ (some (function, declaration)) lineage slots slot value heldValid
              (valid.values rhs value valueLookup)) tail
        · simp [bindSlot, bound, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
            bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail

private theorem contextual_close_finish (frame : ValueId) (state final : MachineState)
    (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (do semCloseFrame frame; pure (.value none)) state = .ok (result, final)) :
    result = .value none ∧ WellMintedState final ∧ HistoryExtends state final := by
  obtain ⟨unit, middle, closed, finished⟩ := split_bind_success _ _ state final result run
  cases unit
  have preserved := valid.close_success state middle frame closed
  have history : HistoryExtends state middle := by
    obtain ⟨_, lineage, _, _, _, rfl⟩ := close_success_state state middle frame closed
    exact history_close state lineage
  change Except.ok (.value none, middle) = Except.ok (result, final) at finished
  cases finished
  exact ⟨rfl, preserved, history⟩

/-- Source handles authenticate first; ordinary and non-frame carriers retain
all original close behavior. Successful closes preserve alias history. -/
theorem contextual_close_success (ctx : EvalContext) (frame : ValueId)
    (state final : MachineState) (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (stepInstWithContext ctx (.CloseFrame frame)) state = .ok (result, final)) :
    result = .value none ∧ WellMintedState final ∧ HistoryExtends state final := by
  simp only [stepInstWithContext] at run
  obtain ⟨held, middle, looked, tail⟩ := split_bind_success _ _ state final result run
  obtain ⟨_, same⟩ := lookup_success state middle frame held looked
  subst middle
  cases held
  case sourceFrame lineage function declaration slots =>
    obtain ⟨types, middle, checked, tail⟩ := split_bind_success _ _ state final result tail
    have same := memory_check_success_state _ state middle types checked
    subst middle
    exact contextual_close_finish frame state final result valid tail
  all_goals exact contextual_close_finish frame state final result valid tail

private theorem slot_member {values : List Value} {index : Nat} {value : Value}
    (found : trustIrListGet? values index = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => cases found
  | cons head tail ih =>
    cases index with
    | zero => simp at found; subst value; exact List.Mem.head _
    | succ index => exact List.Mem.tail _ (ih found)

/-- Actual contextual loads either transport a recursively valid stored value
or publish the genuine typed undefined marker for an unwritten partial slot. -/
theorem contextual_load_success (ctx : EvalContext) (frame : ValueId) (slot : Nat) (requested : Ty)
    (state final : MachineState) (result : InstrResult) (valid : WellMintedState state)
    (run : Sem.run (stepInstWithContext ctx (.LoadSlot frame slot requested)) state = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final ∧ HistoryExtends state final := by
  simp only [stepInstWithContext] at run
  obtain ⟨origin, lineage, slots, lookup, tail⟩ :=
    frameHandle_bind_success state final frame "LoadSlot" _ result run
  have heldValid := (mintedValue_frameValue_iff _ _ _ _).1
    (valid.values frame (frameValue origin lineage slots) lookup)
  obtain ⟨stored, middle, fetched, tail⟩ := split_bind_success _ _ state final result tail
  change Except.ok (state, state) = Except.ok (stored, middle) at fetched
  have pair := Except.ok.inj fetched
  have storedEq : stored = state := (congrArg Prod.fst pair).symm
  have middleEq : middle = state := (congrArg Prod.snd pair).symm
  subst stored
  subst middle
  cases live : state.openFrameLineages.contains lineage with
  | false =>
    trustIrCompilerProof {
      simp [live, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
        bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    } {
      have notLive : lineage ∉ state.openFrameLineages := by simpa using live
      simp [notLive, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
        bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    }
  | true =>
    simp only [live, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at tail
    obtain ⟨held, middle, looked, tail⟩ := split_bind_success _ _ state final result tail
    obtain ⟨found, same⟩ := lookup_success state middle frame held looked
    subst middle
    rw [lookup] at found
    cases found
    cases origin with
    | none =>
      simp only [frameValue] at tail
      cases selected : trustIrListGet? slots slot with
      | none =>
        simp [selected, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
      | some value =>
        simp only [selected] at tail
        obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ state final result tail
        have same := memory_check_success_state _ state middle unit checked
        subst middle
        cases unit
        exact contextual_fresh_success value state final result valid
          (heldValid.2 value (slot_member selected)) tail
    | some source =>
      rcases source with ⟨function, declaration⟩
      simp only [frameValue] at tail
      obtain ⟨types, middle, checkedTypes, tail⟩ := split_bind_success _ _ state final result tail
      have same := memory_check_success_state _ state middle types checkedTypes
      subst middle
      cases declared : trustIrListGet? types slot with
      | none =>
        simp [declared, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
          bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
      | some declaredTy =>
        simp only [declared, pure_bind] at tail
        cases agrees : closureTyEq declaredTy requested with
        | false =>
          simp [agrees, Sem.throwTypeError, Sem.run, StateT.run, StateT.bind, StateT.lift,
            bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
        | true =>
          simp only [agrees, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind, loadSlot] at tail
          cases selected : trustIrListGet? slots slot with
          | none =>
            simp [selected, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
              bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
          | some value =>
            simp only [selected, pure_bind] at tail
            cases unwritten : value.isUninit with
            | false =>
              simp only [unwritten, Bool.false_eq_true, ↓reduceIte] at tail
              obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ state final result tail
              have same := memory_check_success_state _ state middle unit checked
              subst middle
              cases unit
              exact contextual_fresh_success value state final result valid
                (heldValid.2 value (slot_member selected)) tail
            | true =>
              simp only [unwritten, ↓reduceIte] at tail
              cases partialTy : isPartialLoadTy requested with
              | false =>
                simp [partialTy, Sem.throwUB, Sem.run, StateT.run, StateT.bind, StateT.lift,
                  bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
              | true =>
                simp only [partialTy, ↓reduceIte] at tail
                exact contextual_fresh_success (.undef requested) state final result valid
                  (mintedValue_undef _ requested) tail

end TrustIr.FrameLifetime
