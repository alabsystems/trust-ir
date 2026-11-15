-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksContext

namespace TrustIr.GenericCoro.AllBlocksEntryEffects
open Prefix GenericCoroAllBlocksPlanner AllBlocksContext

/-- Raw evaluator effects at every actual table lookup, before the framed
    return-arity and poison checks. Both executions use the SAME cleared
    input world. Undefined keys are retained by the header agreement. -/
structure EntryEffects (source target : EvalContext) : Prop where
  headers : HeaderAgreement source.functions target.functions
  maxDepth : source.maxCallDepth = target.maxCallDepth
  effects : ∀ requested sourceFunction targetFunction,
    source.functions requested = some sourceFunction →
    target.functions requested = some targetFunction →
    ∀ fuel depth args strategy world,
      EffectRelation
        (Sem.run (stepNWithContext (source.forFunction sourceFunction) fuel depth
          sourceFunction.cfg sourceFunction.entryBlock args strategy) (callerWorld world))
        (Sem.run (stepNWithContext (target.forFunction targetFunction) fuel depth
          targetFunction.cfg targetFunction.entryBlock args strategy) (callerWorld world))

theorem effectRelation_trans
    {source middle target : Except SemError (List Value × MachineState)}
    (first : EffectRelation source middle) (second : EffectRelation middle target) :
    EffectRelation source target := by
  cases first with
  | error error => exact second
  | returned values source middle world =>
    cases second with
    | returned _ _ target after => exact .returned values source target (world.trans after)

theorem headerRelated_trans {source middle target : Option EvalFunction}
    (first : HeaderRelated source middle) (second : HeaderRelated middle target) :
    HeaderRelated source target := by
  cases first with
  | absent => exact second
  | present source middle body convention =>
    cases second with
    | present _ target nextBody nextConvention =>
      exact .present source target (body.trans nextBody) (convention.trans nextConvention)

theorem EntryEffects.refl (context : EvalContext) : EntryEffects context context := by
  refine ⟨headerAgreement_refl _, rfl, ?_⟩
  intro requested source target sourceFound targetFound fuel depth args strategy world
  have same : source = target := Option.some.inj (sourceFound.symm.trans targetFound)
  subst target
  exact effectRelation_refl _

theorem EntryEffects.trans {source middle target : EvalContext}
    (first : EntryEffects source middle) (second : EntryEffects middle target) :
    EntryEffects source target := by
  refine ⟨fun id => headerRelated_trans (first.headers id) (second.headers id),
    first.maxDepth.trans second.maxDepth, ?_⟩
  intro requested sourceFunction targetFunction sourceFound targetFound fuel depth args strategy world
  cases middleFound : middle.functions requested with
  | none =>
    have impossible := first.headers requested
    rw [sourceFound, middleFound] at impossible
    cases impossible
  | some middleFunction =>
    exact effectRelation_trans
      (first.effects requested sourceFunction middleFunction sourceFound middleFound
        fuel depth args strategy world)
      (second.effects requested middleFunction targetFunction middleFound targetFound
        fuel depth args strategy world)

/-- The actual simultaneous resource induction supplies effects for EVERY
    requested key, including unchanged recursive or mutually recursive
    functions. No successful-return or callee-freshness premise is used. -/
theorem lowerRows_entryEffects (base : EvalContext) (selected : FuncId)
    (header : EvalFunction) (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (sourceTypes targetTypes : LocalTypeTable)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id)
    (typed : AllBlocksInference.TraceTyped targetTypes (planAllBlocks blocks).trace) :
    EntryEffects
      (withFunction base selected {header with cfg := cfgOf blocks, localTypes := some sourceTypes})
      (withFunction base selected
        {header with cfg := cfgOf (planAllBlocks blocks).rows, localTypes := some targetTypes}) := by
  let sourceFunction : EvalFunction := {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
  let targetFunction : EvalFunction :=
    {header with cfg := cfgOf (planAllBlocks blocks).rows, localTypes := some targetTypes}
  refine ⟨headerAgreement_withFunction base selected sourceFunction targetFunction rfl rfl, rfl, ?_⟩
  intro requested sourceCallee targetCallee sourceFound targetFound fuel depth args strategy world
  have simulated := AllBlocksInduction.evaluator_simulation base selected sourceFunction targetFunction
    rfl rfl rfl ?_ fuel
  · have selectedEffects := AllBlocksInduction.selected_of_paired (evaluatorAt fuel) (evaluatorAt fuel)
      base _ _ sourceFunction targetFunction rfl simulated.2
    have effects := calleeEffects_of_update (evaluatorAt fuel) (evaluatorAt fuel) base selected
      sourceFunction targetFunction simulated.1 selectedEffects
    exact effects requested sourceCallee targetCallee sourceFound targetFound depth args strategy world
  · intro sourceRecurse targetRecurse effects paired callDepth pc values panic state fresh
    exact AllBlocksSimulation.lowerRows_layer_effect sourceRecurse targetRecurse base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions
      (headerAgreement_withFunction base selected sourceFunction targetFunction rfl rfl) effects
      blocks ready sourceTypes targetTypes preserved typed paired callDepth pc values panic state fresh

/-- Consume the actual expanded factory result. Inference success and all
    trace declarations are derived from that result, not assumed by callers. -/
theorem functions_expanded_entryEffects
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows) (source target : EvalFunction)
    (actual : AllBlocks.functions direct indirect header blocks = .ok (.expanded source target))
    (base : EvalContext) (selected : FuncId) :
    EntryEffects (withFunction base selected source) (withFunction base selected target) := by
  have correct := AllBlocks.functions_correct direct indirect header blocks
  rw [actual] at correct
  obtain ⟨sourceInferred, targetInferred, _sourceRun, _targetRun, sourceEq, targetEq,
    ready, _noSuspends, preserved, typed, _calls, _entryCalls⟩ := correct
  rw [sourceEq, targetEq, AllBlocks.withInferredGraph_eq, AllBlocks.withInferredGraph_eq]
  exact lowerRows_entryEffects base selected header blocks ready sourceInferred.table
    targetInferred.table preserved typed

theorem factoryReplacement_entryEffects {source target : EvalFunction}
    (prepared : FactoryReplacement source target) (base : EvalContext) (selected : FuncId) :
    EntryEffects (withFunction base selected source) (withFunction base selected target) := by
  rcases prepared with same | ⟨direct, indirect, header, blocks, actual⟩
  · rw [same]
    exact EntryEffects.refl _
  · exact functions_expanded_entryEffects direct indirect header blocks source target actual base selected

private theorem withFunction_shadow (base : EvalContext) (key : FuncId)
    (first second : EvalFunction) :
    withFunction (withFunction base key first) key second = withFunction base key second := by
  change { base with functions := fun query => if query == key then some second
      else if query == key then some first else base.functions query } =
    { base with functions := fun query => if query == key then some second else base.functions query }
  have same : (fun query => if query == key then some second
      else if query == key then some first else base.functions query) =
      (fun query => if query == key then some second else base.functions query) := by
    funext query
    cases here : query == key <;> simp only [here, Bool.false_eq_true, if_false, if_true]
  rw [same]

private theorem withFunction_commute (base : EvalContext) (firstKey secondKey : FuncId)
    (first second : EvalFunction) (different : firstKey ≠ secondKey) :
    withFunction (withFunction base firstKey first) secondKey second =
      withFunction (withFunction base secondKey second) firstKey first := by
  change { base with functions := fun query => if query == secondKey then some second
      else if query == firstKey then some first else base.functions query } =
    { base with functions := fun query => if query == firstKey then some first
      else if query == secondKey then some second else base.functions query }
  have same : (fun query => if query == secondKey then some second
      else if query == firstKey then some first else base.functions query) =
      (fun query => if query == firstKey then some first
        else if query == secondKey then some second else base.functions query) := by
    funext query
    cases one : query == firstKey <;> cases two : query == secondKey <;>
      simp only [one, two, Bool.false_eq_true, if_false, if_true]
    exact False.elim (different ((of_decide_eq_true one).symm.trans (of_decide_eq_true two)))
  rw [same]

private def withoutKey (key : FuncId) (updates : List FunctionUpdate) : List FunctionUpdate :=
  updates.filter (fun update => !(update.id == key))

private theorem withoutKey_member (key : FuncId) (updates : List FunctionUpdate)
    (update : FunctionUpdate) (member : update ∈ withoutKey key updates) : update ∈ updates :=
  (List.mem_filter.mp member).1

private theorem withoutKey_different (key : FuncId) (updates : List FunctionUpdate)
    (update : FunctionUpdate) (member : update ∈ withoutKey key updates) : update.id ≠ key := by
  have guard := (List.mem_filter.mp member).2
  intro same
  have here : (update.id == key) = true := decide_eq_true same
  simp only [here, Bool.not_true, Bool.false_eq_true] at guard

private theorem withoutKey_length (key : FuncId) (updates : List FunctionUpdate) :
    (withoutKey key updates).length ≤ updates.length := by
  induction updates with
  | nil => exact Nat.le_refl _
  | cons update rest ih =>
    cases here : update.id == key <;>
      simp only [withoutKey, List.filter, here, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, if_false, if_true, List.length_cons] at ih ⊢ <;> omega

private theorem installFirst_commute (choose : FunctionUpdate → EvalFunction) (base : EvalContext)
    (updates : List FunctionUpdate) (key : FuncId) (function : EvalFunction)
    (different : ∀ update ∈ updates, update.id ≠ key) :
    withFunction (installFirst choose base updates) key function =
      installFirst choose (withFunction base key function) updates := by
  induction updates with
  | nil => rfl
  | cons update rest ih =>
    change withFunction (withFunction (installFirst choose base rest) update.id (choose update)) key function =
      withFunction (installFirst choose (withFunction base key function) rest) update.id (choose update)
    rw [withFunction_commute _ _ _ _ _ (different update ((trustIrListMemConsSelf _ _)))]
    rw [ih (fun later member => different later (List.mem_cons_of_mem update member))]

private theorem installFirst_mask (choose : FunctionUpdate → EvalFunction) (base : EvalContext)
    (updates : List FunctionUpdate) (key : FuncId) (function : EvalFunction) :
    withFunction (installFirst choose base updates) key function =
      withFunction (installFirst choose base (withoutKey key updates)) key function := by
  induction updates with
  | nil => rfl
  | cons update rest ih =>
    cases here : update.id == key with
    | true =>
      have same : update.id = key := of_decide_eq_true here
      simp only [withoutKey, List.filter, here, Bool.not_true, Bool.false_eq_true, if_false]
      change withFunction (withFunction (installFirst choose base rest) update.id (choose update)) key function = _
      rw [same, withFunction_shadow]
      exact ih
    | false =>
      have different : update.id ≠ key := by
        intro same
        have yes : (update.id == key) = true := decide_eq_true same
        rw [here] at yes
        cases yes
      simp only [withoutKey, List.filter, here, Bool.not_false, if_true]
      change withFunction (withFunction (installFirst choose base rest) update.id (choose update)) key function =
        withFunction (withFunction (installFirst choose base (withoutKey key rest)) update.id (choose update)) key function
      rw [withFunction_commute _ _ _ _ _ different,
        withFunction_commute _ _ _ _ _ different, ih]

/-- Finite source-order table composition for raw entry effects. The first
    executable duplicate wins; masked later replacements never become visible.
    Each actual one-key simulation is instantiated in its full surrounding
    table, including mutually recursive entries. -/
theorem installFirst_entryEffects (updates : List FunctionUpdate)
    (prepared : ∀ update ∈ updates, FactoryReplacement update.source update.target)
    (base : EvalContext) :
    EntryEffects (installFirst FunctionUpdate.source base updates)
      (installFirst FunctionUpdate.target base updates) := by
  suffices all : ∀ count (rows : List FunctionUpdate), rows.length = count →
      ∀ ctx, (∀ update ∈ rows, FactoryReplacement update.source update.target) →
        EntryEffects (installFirst FunctionUpdate.source ctx rows)
          (installFirst FunctionUpdate.target ctx rows) from
    all updates.length updates rfl base prepared
  intro count
  induction count using trustIrNatStrongInduction with
  | ind count ih =>
    intro rows census ctx produced
    cases rows with
    | nil => exact EntryEffects.refl _
    | cons update rest =>
      let retained := withoutKey update.id rest
      have shorter : retained.length < count := by
        change (withoutKey update.id rest).length < count
        have bound := withoutKey_length update.id rest
        simp only [List.length_cons] at census
        omega
      have retainedProduced : ∀ row ∈ retained, FactoryReplacement row.source row.target :=
        fun row member => produced row (List.mem_cons_of_mem update (withoutKey_member _ _ _ member))
      have retainedDifferent : ∀ row ∈ retained, row.id ≠ update.id :=
        withoutKey_different update.id rest
      have first := factoryReplacement_entryEffects
        (produced update ((trustIrListMemConsSelf _ _)))
        (installFirst FunctionUpdate.source ctx retained) update.id
      have second := ih retained.length shorter retained rfl
        (withFunction ctx update.id update.target) retainedProduced
      have after : EntryEffects
          (withFunction (installFirst FunctionUpdate.source ctx retained) update.id update.target)
          (withFunction (installFirst FunctionUpdate.target ctx retained) update.id update.target) := by
        rw [installFirst_commute _ _ _ _ _ retainedDifferent,
          installFirst_commute _ _ _ _ _ retainedDifferent]
        exact second
      change EntryEffects
        (withFunction (installFirst FunctionUpdate.source ctx rest) update.id update.source)
        (withFunction (installFirst FunctionUpdate.target ctx rest) update.id update.target)
      rw [installFirst_mask FunctionUpdate.source ctx rest update.id update.source,
        installFirst_mask FunctionUpdate.target ctx rest update.id update.target]
      exact EntryEffects.trans first after

end TrustIr.GenericCoro.AllBlocksEntryEffects

namespace TrustIr.GenericCoro.AllBlocksEntryEffects.Controls
open Prefix GenericCoroAllBlocksPlanner AllBlocksContext

/-- An inhabited pair of actual expanded, mutually recursive factories,
    composed in a raw table with a shadowed duplicate. The old framed-call
    conclusion is discarded: raw effects are rederived from the two actual
    factory equations and the first-wins composition theorem above. -/
theorem mutual_factories_and_duplicate_have_raw_entry_effects :
    ∃ leftSource leftTarget rightSource rightTarget,
      AllBlocks.functions AllBlocksContext.Controls.direct (fun _ => none)
        AllBlocksContext.Controls.header (AllBlocksContext.Controls.graph ⟨1⟩) =
          .ok (.expanded leftSource leftTarget) ∧
      AllBlocks.functions AllBlocksContext.Controls.direct (fun _ => none)
        AllBlocksContext.Controls.header (AllBlocksContext.Controls.graph ⟨0⟩) =
          .ok (.expanded rightSource rightTarget) ∧
      ∀ base,
        let updates : List FunctionUpdate :=
          [⟨⟨0⟩, leftSource, leftTarget⟩, ⟨⟨1⟩, rightSource, rightTarget⟩,
            ⟨⟨0⟩, rightSource, rightTarget⟩]
        (installFirst FunctionUpdate.source base updates).functions ⟨0⟩ = some leftSource ∧
        (installFirst FunctionUpdate.target base updates).functions ⟨0⟩ = some leftTarget ∧
        EntryEffects (installFirst FunctionUpdate.source base updates)
          (installFirst FunctionUpdate.target base updates) := by
  obtain ⟨leftSource, leftTarget, rightSource, rightTarget, leftRun, rightRun, _framed⟩ :=
    AllBlocksContext.Controls.two_updated_mutual_entries_preserve_every_framed_call
  refine ⟨leftSource, leftTarget, rightSource, rightTarget, leftRun, rightRun, ?_⟩
  intro base
  refine ⟨rfl, rfl, ?_⟩
  apply installFirst_entryEffects
  intro update member
  have left : FactoryReplacement leftSource leftTarget :=
    Or.inr ⟨_, _, _, _, leftRun⟩
  have right : FactoryReplacement rightSource rightTarget :=
    Or.inr ⟨_, _, _, _, rightRun⟩
  rcases List.mem_cons.mp member with same | later
  · cases same; exact left
  · rcases List.mem_cons.mp later with same | later
    · cases same; exact right
    · rcases List.mem_cons.mp later with same | impossible
      · cases same; exact right
      · cases impossible

end TrustIr.GenericCoro.AllBlocksEntryEffects.Controls
