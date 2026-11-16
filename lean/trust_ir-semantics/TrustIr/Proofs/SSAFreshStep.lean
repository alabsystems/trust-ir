-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshFrames
import TrustIr.Proofs.HeldMemoryFrames

namespace TrustIr.SSAFreshStep
open SSAFreshFrames

/-- Successful execution preserves the actual SSA high-water invariant.
    No condition is imposed on error paths. -/
def KeepsFresh {α : Type} (action : Sem α) : Prop :=
  ∀ state result, FreshState state → Sem.run action state = .ok result → FreshState result.snd

theorem pure_fresh {α : Type} (value : α) : KeepsFresh (pure value : Sem α) := by
  intro state result fresh run
  change Except.ok (value, state) = Except.ok result at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact fresh

theorem throw_fresh {α : Type} (error : SemError) : KeepsFresh (throw error : Sem α) := by
  intro state result fresh run
  change Except.error error = Except.ok result at run
  cases run

theorem bind_fresh {α β : Type} (first : Sem α) (next : α → Sem β)
    (firstFresh : KeepsFresh first) (nextFresh : ∀ value, KeepsFresh (next value)) :
    KeepsFresh (first >>= next) := by
  intro state result fresh run
  simp only [Sem.run, StateT.run, bind, StateT.bind, Except.bind] at run
  cases firstRun : first state with
  | error error => simp [firstRun] at run
  | ok pair =>
    simp only [firstRun] at run
    obtain ⟨value, middle⟩ := pair
    simp only [] at run
    have middleFresh := firstFresh state (value, middle) fresh
      (by simp [Sem.run, StateT.run, firstRun])
    exact nextFresh value middle result middleFresh (by simpa [Sem.run, StateT.run] using run)

theorem get_fresh : KeepsFresh Sem.getState := by
  intro state result fresh run
  change Except.ok (state, state) = Except.ok result at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact fresh

/-- A state update that retains its SSA projection retains freshness. -/
theorem sameSSA_fresh (before after : MachineState) (fresh : FreshState before)
    (locals : after.locals = before.locals) (next : after.nextValueId = before.nextValueId) :
    FreshState after := by
  intro id bound
  change after.locals id = none
  rw [locals]
  exact fresh id (by simpa only [next] using bound)

theorem bindFresh_fresh (value : Value) : KeepsFresh (Sem.bindFresh value) := by
  intro state result fresh run
  rw [Sem.run, sr_bindFresh] at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact set_fresh state ⟨state.nextValueId⟩ value (state.nextValueId + 1) fresh
    (Nat.le_succ _) (Nat.le_refl _)

theorem lookup_fresh (id : ValueId) : KeepsFresh (Sem.lookupValue id) := by
  unfold Sem.lookupValue
  apply bind_fresh _ _ get_fresh
  intro state
  cases state.lookupValue id with
  | none => exact throw_fresh _
  | some value => exact pure_fresh _

theorem mapM_fresh {α β : Type} (action : α → Sem β) (items : List α)
    (each : ∀ item, KeepsFresh (action item)) : KeepsFresh (items.mapM action) := by
  induction items with
  | nil => exact pure_fresh _
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply bind_fresh _ _ (each item)
    intro value
    exact bind_fresh _ _ ih (fun values => pure_fresh _)

private theorem dests_fold_fresh (dests : List ValueId) (values : List Value)
    (state : MachineState) (fresh : FreshState state) (arity : dests.length = values.length) :
    FreshState { state with
      locals := (dests.zip values).foldl (fun locals binding => locals.set binding.fst binding.snd) state.locals
      nextValueId := dests.foldl (fun next dest => max next (dest.index + 1)) state.nextValueId } := by
  induction dests generalizing values state with
  | nil => simpa only [List.zip_nil_left, List.foldl_nil] using fresh
  | cons dest dests ih =>
    cases values with
    | nil => simp at arity
    | cons value values =>
      let middle : MachineState := { state with
        locals := state.locals.set dest value
        nextValueId := max state.nextValueId (dest.index + 1) }
      have middleFresh : FreshState middle :=
        set_fresh state dest value _ fresh (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      simpa only [List.zip_cons_cons, List.foldl_cons] using
        ih values middle middleFresh (Nat.succ.inj arity)

theorem bindResultDests_fresh (dests : List ValueId) (values : List Value) :
    KeepsFresh (bindResultDests dests values) := by
  trustIrCompilerProof {
    intro state result fresh run
    by_cases arity : dests.length = values.length
    · simp only [bindResultDests, arity, bne_self_eq_false, if_false,
        Sem.run, sr_bind, sr_get, sr_set, Except.bind] at run
      have states := congrArg Prod.snd (Except.ok.inj run)
      rw [← states]
      exact dests_fold_fresh dests values state fresh arity
    · have mismatch : (dests.length != values.length) = true := by simpa using arity
      simp only [bindResultDests, mismatch, if_true, Sem.run, sr_throwTE] at run
  } {
    intro state result fresh run
    by_cases arity : dests.length = values.length
    · simp only [bindResultDests, arity, bne_self_eq_false, if_false,
        Sem.run, sr_bind, sr_get, sr_set, Except.bind] at run
      have states := congrArg Prod.snd (Except.ok.inj run)
      rw [← states]
      exact dests_fold_fresh dests values state fresh arity
    · have mismatch : (dests.length != values.length) = true := by simpa using arity
      simp only [bindResultDests, mismatch, if_true, Sem.run, sr_throwTE] at run
      cases run
  }

/-- Removing private aliases cannot create a binding above the high-water mark. -/
theorem erase_fresh (state : MachineState) (id : ValueId) (fresh : FreshState state) :
    FreshState { state with locals := fun key => if key == id then none else state.locals key } := by
  intro key bound
  change (if key == id then none else state.locals key) = none
  split
  · rfl
  · exact fresh key bound

theorem restore_empty_fresh (callee caller : MachineState) (destination : Option ValueId)
    (fresh : FreshState caller) :
    FreshState (restoreFrame callee (saveFrame caller destination) []) := by
  cases destination <;> exact sameSSA_fresh caller _ fresh rfl rfl


/-- Any held-value computation equivariant under complete SSA replacement
    preserves the actual SSA projection and therefore freshness. -/
theorem equivariant_fresh {α : Type} (action : Sem α)
    (equivariant : HeldMemoryFrames.Equivariant action) : KeepsFresh action := by
  intro state result fresh run
  have law := equivariant state state.locals state.nextValueId
  change Sem.run action state = (Sem.run action state).map
    (fun result => (result.1, HeldMemoryFrames.replaceSSA result.2 state.locals state.nextValueId)) at law
  rw [run] at law
  have states := congrArg Prod.snd (Except.ok.inj law)
  have locals := congrArg MachineState.locals states
  have next := congrArg MachineState.nextValueId states
  exact sameSSA_fresh state result.snd fresh locals next

theorem modify_fresh (update : MachineState → MachineState)
    (preserves : ∀ state, FreshState state → FreshState (update state)) :
    KeepsFresh (Sem.modifyState update) := by
  intro state result fresh run
  change Except.ok ((), update state) = Except.ok result at run
  have states := congrArg Prod.snd (Except.ok.inj run)
  rw [← states]
  exact preserves state fresh

private theorem retired_absent (results dests : List ValueId) (locals : ValueMap)
    (key : ValueId) (absent : locals key = none) :
    (results.foldl (fun locals tmp => if dests.contains tmp then locals
      else fun id => if id == tmp then none else locals id) locals) key = none := by
  trustIrCompilerProof {
    induction results generalizing locals with
    | nil => exact absent
    | cons tmp results ih =>
      by_cases keep : dests.contains tmp = true
      · simpa only [List.foldl_cons, keep, if_true] using ih locals absent
      · have nextAbsent : (fun id => if id == tmp then none else locals id) key = none := by
          change (if key == tmp then none else locals key) = none
          by_cases equal : (key == tmp) = true <;> simp only [equal, if_true, if_false, absent]
        simpa only [List.foldl_cons, keep, if_false] using ih _ nextAbsent
  } {
    induction results generalizing locals with
    | nil => exact absent
    | cons tmp results ih =>
      by_cases keep : dests.contains tmp = true
      · simpa only [List.foldl_cons, keep, if_true] using ih locals absent
      · have nextAbsent : (fun id => if id == tmp then none else locals id) key = none := by
          change (if key == tmp then none else locals key) = none
          by_cases equal : (key == tmp) = true <;> simp only [equal, Bool.false_eq_true, if_true, if_false, absent]
        simpa only [List.foldl_cons, keep, if_false] using ih _ nextAbsent
  }

theorem retire_many_fresh (state : MachineState) (results dests : List ValueId)
    (fresh : FreshState state) :
    FreshState { state with
      locals := results.foldl
        (fun locals tmp => if dests.contains tmp then locals
          else fun id => if id == tmp then none else locals id) state.locals } := by
  intro key bound
  exact retired_absent results dests state.locals key (fresh key bound)

theorem bindInstrResultDests_fresh (result : InstrResult) (dests : List ValueId) :
    KeepsFresh (bindInstrResultDests result dests) := by
  cases result with
  | value value =>
    cases value with
    | none =>
      cases dests with
      | nil => exact pure_fresh _
      | cons dest dests => exact throw_fresh _
    | some source =>
      cases dests with
      | nil => exact pure_fresh _
      | cons dest dests =>
        cases dests with
        | cons next rest => exact throw_fresh _
        | nil =>
          unfold bindInstrResultDests
          apply bind_fresh _ _ (lookup_fresh source)
          intro value
          apply bind_fresh _ _ (bindResultDests_fresh [dest] [value])
          intro unit
          split
          · change KeepsFresh (Sem.modifyState (fun state =>
              { state with locals := fun id => if id == source then none else state.locals id }))
            exact modify_fresh _ (fun state fresh => erase_fresh state source fresh)
          · exact pure_fresh _
  | values results =>
    simp only [bindInstrResultDests]
    split
    · exact throw_fresh _
    · apply bind_fresh _ _ (mapM_fresh Sem.lookupValue results lookup_fresh)
      intro values
      apply bind_fresh _ _ (bindResultDests_fresh dests values)
      intro unit
      change KeepsFresh (Sem.modifyState (fun state => { state with
        locals := results.foldl
          (fun locals tmp => if dests.contains tmp then locals
            else fun id => if id == tmp then none else locals id) state.locals }))
      exact modify_fresh _ (fun state fresh => retire_many_fresh state results dests fresh)
  | terminator step => exact throw_fresh _

theorem checkInstructionResults_fresh (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) :
    KeepsFresh (ctx.checkInstructionResults inst dests values) := by
  unfold EvalContext.checkInstructionResults
  cases typesResult : ctx.instructionResultTypes inst dests values.length with
  | error error =>
    simp only
    apply bind_fresh _ _ (throw_fresh error)
    intro types
    cases checkSSACharValues types values with
    | error error => exact throw_fresh _
    | ok unit => cases unit; exact pure_fresh _
  | ok types =>
    simp only [pure_bind]
    cases checkSSACharValues types values with
    | error error => exact throw_fresh _
    | ok unit => cases unit; exact pure_fresh _

theorem bindCallResults_fresh (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) :
    KeepsFresh (ctx.bindCallResults inst dests values) := by
  cases mismatch : (dests.length != values.length) with
  | true =>
    simp only [EvalContext.bindCallResults, mismatch, ↓reduceIte]
    exact bindResultDests_fresh dests values
  | false =>
    simp only [EvalContext.bindCallResults, mismatch, Bool.false_eq_true, ↓reduceIte]
    exact bind_fresh _ _ (checkInstructionResults_fresh ctx inst dests values)
      (fun _ => bindResultDests_fresh dests values)

private theorem checked_then_bind_fresh (ctx : EvalContext) (inst : Inst)
    (result : InstrResult) (dests : List ValueId) (values : List Value) :
    KeepsFresh (do ctx.checkInstructionResults inst dests values; bindInstrResultDests result dests) :=
  bind_fresh _ _ (checkInstructionResults_fresh ctx inst dests values)
    (fun _ => bindInstrResultDests_fresh result dests)

theorem bindInstructionResults_fresh (ctx : EvalContext) (inst : Inst)
    (result : InstrResult) (dests : List ValueId) :
    KeepsFresh (ctx.bindInstructionResults inst result dests) := by
  cases result with
  | value value =>
    cases value with
    | none =>
      cases dests with
      | nil => exact checked_then_bind_fresh ctx inst _ [] []
      | cons dest dests =>
        cases dests <;> simpa only [EvalContext.bindInstructionResults] using
          bindInstrResultDests_fresh (.value none) (dest :: _)
    | some source =>
      cases dests with
      | nil =>
        exact bind_fresh _ _ (lookup_fresh source)
          (fun value => checked_then_bind_fresh ctx inst _ [] [value])
      | cons dest dests =>
        cases dests with
        | nil =>
          simpa only [EvalContext.bindInstructionResults] using
            bind_fresh _ _ (lookup_fresh source)
              (fun value => checked_then_bind_fresh ctx inst (.value (some source)) [dest] [value])
        | cons next rest =>
          simpa only [EvalContext.bindInstructionResults] using
            bindInstrResultDests_fresh (.value (some source)) (dest :: next :: rest)
  | values results =>
    simp only [EvalContext.bindInstructionResults]
    split
    · exact bindInstrResultDests_fresh _ _
    · exact bind_fresh _ _ (mapM_fresh Sem.lookupValue results lookup_fresh)
        (fun values => checked_then_bind_fresh ctx inst _ dests values)
  | terminator step =>
    simpa only [EvalContext.bindInstructionResults] using bindInstrResultDests_fresh (.terminator step) dests

end TrustIr.SSAFreshStep

-- Exact dependency guards for the public freshness support closure.
#trustIrAxiomsPinned TrustIr.SSAFreshStep.pure_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.throw_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.bind_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.get_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.sameSSA_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.bindFresh_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.lookup_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.mapM_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.bindResultDests_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.erase_fresh == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.restore_empty_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.equivariant_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.modify_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshStep.retire_many_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.bindInstrResultDests_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.checkInstructionResults_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.bindCallResults_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshStep.bindInstructionResults_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

