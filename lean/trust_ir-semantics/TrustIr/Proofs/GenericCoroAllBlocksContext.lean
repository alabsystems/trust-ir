-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksCorrect

namespace TrustIr.GenericCoro.AllBlocksContext
open Prefix GenericCoroAllBlocksPlanner

/-- Equality of the real framed Call helper at every requested entry. Equality
    of Sem computations includes arbitrary caller states and complete errors. -/
def FramedCallsEquivalent (source target : EvalContext) : Prop :=
  ∀ requested fuel depth args strategy,
    runCallReq source fuel depth requested args strategy =
      runCallReq target fuel depth requested args strategy

theorem FramedCallsEquivalent.refl (ctx : EvalContext) : FramedCallsEquivalent ctx ctx :=
  fun _ _ _ _ _ => rfl

theorem FramedCallsEquivalent.symm {source target : EvalContext}
    (related : FramedCallsEquivalent source target) : FramedCallsEquivalent target source :=
  fun requested fuel depth args strategy => (related requested fuel depth args strategy).symm

theorem FramedCallsEquivalent.trans {source middle target : EvalContext}
    (first : FramedCallsEquivalent source middle) (second : FramedCallsEquivalent middle target) :
    FramedCallsEquivalent source target :=
  fun requested fuel depth args strategy =>
    (first requested fuel depth args strategy).trans (second requested fuel depth args strategy)

theorem FramedCallsEquivalent.run {source target : EvalContext}
    (related : FramedCallsEquivalent source target) (requested : FuncId) (fuel depth : Nat)
    (args : List Value) (strategy : PanicStrategy) (caller : MachineState) :
    Sem.run (runCallReq source fuel depth requested args strategy) caller =
      Sem.run (runCallReq target fuel depth requested args strategy) caller :=
  congrArg (fun action => Sem.run action caller) (related requested fuel depth args strategy)

/-- A one-key expansion preserves calls to ALL entries, including unchanged
    mutually recursive callees and undefined/bodyless other entries. The
    actual paired resource induction supplies both selected and same-graph
    effects; no user callback, caller-freshness or success premise is needed. -/
theorem lowerRows_framedCallsEquivalent (base : EvalContext) (selected : FuncId)
    (header : EvalFunction) (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (sourceTypes targetTypes : LocalTypeTable)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id)
    (typed : AllBlocksInference.TraceTyped targetTypes (planAllBlocks blocks).trace) :
    FramedCallsEquivalent
      (withFunction base selected {header with cfg := cfgOf blocks, localTypes := some sourceTypes})
      (withFunction base selected
        {header with cfg := cfgOf (planAllBlocks blocks).rows, localTypes := some targetTypes}) := by
  let sourceFunction : EvalFunction := {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
  let targetFunction : EvalFunction :=
    {header with cfg := cfgOf (planAllBlocks blocks).rows, localTypes := some targetTypes}
  let sourceCtx := withFunction base selected sourceFunction
  let targetCtx := withFunction base selected targetFunction
  intro requested fuel depth args strategy
  have simulated := AllBlocksInduction.evaluator_simulation base selected sourceFunction targetFunction
    rfl rfl rfl ?_ fuel
  · have selectedEffects := AllBlocksInduction.selected_of_paired (evaluatorAt fuel) (evaluatorAt fuel)
      base _ _ sourceFunction targetFunction rfl simulated.2
    have effects := calleeEffects_of_update (evaluatorAt fuel) (evaluatorAt fuel) base selected
      sourceFunction targetFunction simulated.1 selectedEffects
    have headers := headerAgreement_withFunction base selected sourceFunction targetFunction rfl rfl
    have related := headers requested
    change runCallReq sourceCtx fuel depth requested args strategy =
      runCallReq targetCtx fuel depth requested args strategy
    cases sourceFound : sourceCtx.functions requested with
    | none =>
      cases targetFound : targetCtx.functions requested with
      | none =>
        cases declared : base.declared requested <;>
          simp only [runCallReq, sourceFound, targetFound,
            show sourceCtx.declared = base.declared from rfl,
            show targetCtx.declared = base.declared from rfl,
            declared, Bool.false_eq_true, if_false, if_true,
            Sem.throwUnsupported, Sem.throwTypeError, throw_bind_sem]
      | some function => rw [sourceFound, targetFound] at related; cases related
    | some sourceCallee =>
      cases targetFound : targetCtx.functions requested with
      | none => rw [sourceFound, targetFound] at related; cases related
      | some targetCallee =>
        rw [sourceFound, targetFound] at related
        cases related with
        | present _ _ body _ =>
          apply runCallReq_eq_of_effectRelation sourceCtx targetCtx fuel depth requested args strategy
            sourceCallee targetCallee sourceFound targetFound body
          intro world
          exact effects requested sourceCallee targetCallee sourceFound targetFound depth args strategy world
  · intro sourceRecurse targetRecurse effects paired callDepth pc values panic state fresh
    exact AllBlocksSimulation.lowerRows_layer_effect sourceRecurse targetRecurse base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions
      (headerAgreement_withFunction base selected sourceFunction targetFunction rfl rfl) effects
      blocks ready sourceTypes targetTypes preserved typed paired callDepth pc values panic state fresh

/-- Consume the ACTUAL factory result, deriving its inference and trace facts
    rather than accepting a supplied semantic equivalence relation. -/
theorem functions_expanded_framedCallsEquivalent
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows) (source target : EvalFunction)
    (actual : AllBlocks.functions direct indirect header blocks = .ok (.expanded source target))
    (base : EvalContext) (selected : FuncId) :
    FramedCallsEquivalent (withFunction base selected source) (withFunction base selected target) := by
  have correct := AllBlocks.functions_correct direct indirect header blocks
  rw [actual] at correct
  obtain ⟨sourceInferred, targetInferred, _sourceRun, _targetRun, sourceEq, targetEq,
    ready, _noSuspends, preserved, typed, _calls, _entryCalls⟩ := correct
  rw [sourceEq, targetEq, AllBlocks.withInferredGraph_eq, AllBlocks.withInferredGraph_eq]
  exact lowerRows_framedCallsEquivalent base selected header blocks ready sourceInferred.table
    targetInferred.table preserved typed

/-- A literal no-op or an expanded result of the actual all-block factory.
    This records producer evidence, not an assumed semantic relation. -/
def FactoryReplacement (source target : EvalFunction) : Prop :=
  source = target ∨ ∃ (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : Rows),
      AllBlocks.functions direct indirect header blocks = .ok (.expanded source target)

theorem FactoryReplacement.framedCallsEquivalent {source target : EvalFunction}
    (prepared : FactoryReplacement source target) (base : EvalContext) (selected : FuncId) :
    FramedCallsEquivalent (withFunction base selected source) (withFunction base selected target) := by
  rcases prepared with same | ⟨direct, indirect, header, blocks, actual⟩
  · rw [same]
    exact FramedCallsEquivalent.refl _
  · exact functions_expanded_framedCallsEquivalent direct indirect header blocks source target actual base selected

structure FunctionUpdate where
  id : FuncId
  source : EvalFunction
  target : EvalFunction

/-- Literal source-order updates, with the FIRST executable occurrence winning.
    This is a table specification for composition; it does not change the
    module runner's existing indexed table implementation. -/
def installFirst (choose : FunctionUpdate → EvalFunction) (base : EvalContext)
    (updates : List FunctionUpdate) : EvalContext :=
  updates.foldr (fun update ctx => withFunction ctx update.id (choose update)) base

theorem installFirst_functions (choose : FunctionUpdate → EvalFunction) (base : EvalContext)
    (updates : List FunctionUpdate) (requested : FuncId) :
    (installFirst choose base updates).functions requested =
      match updates.find? (fun update => requested == update.id) with
      | some update => some (choose update)
      | none => base.functions requested := by
  induction updates with
  | nil => rfl
  | cons update rest ih =>
    cases found : requested == update.id <;>
      simp only [installFirst, List.foldr, withFunction, List.find?, found,
        Bool.false_eq_true, if_false, if_true] at ih ⊢
    exact ih

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

/-- Compose genuine factory replacements in the actual first-match order.
    Later duplicate executable keys are masked by their earlier occurrence;
    no uniqueness assumption or same-order overwrite argument is used. -/
theorem installFirst_framedCallsEquivalent (updates : List FunctionUpdate)
    (prepared : ∀ update ∈ updates, FactoryReplacement update.source update.target)
    (base : EvalContext) :
    FramedCallsEquivalent (installFirst FunctionUpdate.source base updates)
      (installFirst FunctionUpdate.target base updates) := by
  suffices all : ∀ count (rows : List FunctionUpdate), rows.length = count →
      ∀ ctx, (∀ update ∈ rows, FactoryReplacement update.source update.target) →
        FramedCallsEquivalent (installFirst FunctionUpdate.source ctx rows)
          (installFirst FunctionUpdate.target ctx rows) from
    all updates.length updates rfl base prepared
  intro count
  induction count using trustIrNatStrongInduction with
  | ind count ih =>
    intro rows census ctx produced
    cases rows with
    | nil => exact FramedCallsEquivalent.refl _
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
      have first := (produced update ((trustIrListMemConsSelf _ _))).framedCallsEquivalent
        (installFirst FunctionUpdate.source ctx retained) update.id
      have second := ih retained.length shorter retained rfl
        (withFunction ctx update.id update.target) retainedProduced
      have after : FramedCallsEquivalent
          (withFunction (installFirst FunctionUpdate.source ctx retained) update.id update.target)
          (withFunction (installFirst FunctionUpdate.target ctx retained) update.id update.target) := by
        rw [installFirst_commute _ _ _ _ _ retainedDifferent,
          installFirst_commute _ _ _ _ _ retainedDifferent]
        exact second
      change FramedCallsEquivalent
        (withFunction (installFirst FunctionUpdate.source ctx rest) update.id update.source)
        (withFunction (installFirst FunctionUpdate.target ctx rest) update.id update.target)
      rw [installFirst_mask FunctionUpdate.source ctx rest update.id update.source,
        installFirst_mask FunctionUpdate.target ctx rest update.id update.target]
      exact FramedCallsEquivalent.trans first after

namespace Controls

def signature : FuncTyDef :=
  { params := [.Ptr, .I32, .Bool], returns := [.I32], isVararg := false }

def direct (id : FuncId) : Option FuncTyDef :=
  if id == ⟨0⟩ || id == ⟨1⟩ then some signature else none

def header : EvalFunction :=
  { body := { paramTys := [.Ptr, .I32, .Bool], returnTys := [.I32] }
    cfg := fun _ => none
    entryBlock := ⟨0⟩ }

/-- Each graph has both a call-free suspend path and a body Call to the
    other table entry before suspending. The recursive edge supplies false
    so the other entry can take its base path. No successful outcome is
    assumed by the subsequent all-caller, all-resource context relation. -/
def graph (callee : FuncId) : Rows := [
  (⟨0⟩, {
    params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .Bool)]
    body := [], terminator := .CondBr ⟨2⟩ ⟨1⟩ [] ⟨2⟩ [] }),
  (⟨1⟩, {
    params := []
    body := [.Const .Bool (.bool false), .Call callee [⟨0⟩, ⟨1⟩, ⟨3⟩]]
    bodyResultDests := [[⟨3⟩], [⟨4⟩]]
    terminator := .CoroSuspend ⟨0⟩ 1 19 ⟨4⟩ }),
  (⟨2⟩, { params := [], body := [], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩ })]

private def outputTag {blocks : Rows} :
    Except SemError (AllBlocks.Expansion GenericCoroFreshIds.u32Domain blocks) → Nat
  | .error _ => 0
  | .ok (.unchanged _) => 1
  | .ok (.capacity _ _) => 2
  | .ok (.expanded _ _) => 3

theorem both_mutual_factory_results_are_expanded :
    outputTag (AllBlocks.functions direct (fun _ => none) header (graph ⟨1⟩)) = 3 ∧
      outputTag (AllBlocks.functions direct (fun _ => none) header (graph ⟨0⟩)) = 3 := ⟨rfl, rfl⟩

private theorem replacement_of_tag (callee : FuncId)
    (result : Except SemError (AllBlocks.Expansion GenericCoroFreshIds.u32Domain (graph callee)))
    (actual : AllBlocks.functions direct (fun _ => none) header (graph callee) = result)
    (tag : outputTag result = 3) :
    ∃ source target,
      AllBlocks.functions direct (fun _ => none) header (graph callee) = .ok (.expanded source target) ∧
      FactoryReplacement source target := by
  cases result with
  | error _ => cases tag
  | ok result =>
    cases result with
    | unchanged _ => cases tag
    | capacity _ _ => cases tag
    | expanded source target =>
      exact ⟨source, target, actual, Or.inr ⟨direct, (fun _ => none), header, graph callee, actual⟩⟩

private theorem mutual_replacements : ∃ leftSource leftTarget rightSource rightTarget,
    AllBlocks.functions direct (fun _ => none) header (graph ⟨1⟩) = .ok (.expanded leftSource leftTarget) ∧
    AllBlocks.functions direct (fun _ => none) header (graph ⟨0⟩) = .ok (.expanded rightSource rightTarget) ∧
    FactoryReplacement leftSource leftTarget ∧ FactoryReplacement rightSource rightTarget := by
  have leftTag := both_mutual_factory_results_are_expanded.1
  have rightTag := both_mutual_factory_results_are_expanded.2
  generalize leftActual : AllBlocks.functions direct (fun _ => none) header (graph ⟨1⟩) = left at leftTag
  generalize rightActual : AllBlocks.functions direct (fun _ => none) header (graph ⟨0⟩) = right at rightTag
  obtain ⟨leftSource, leftTarget, leftRun, leftPrepared⟩ := replacement_of_tag ⟨1⟩ left leftActual leftTag
  obtain ⟨rightSource, rightTarget, rightRun, rightPrepared⟩ := replacement_of_tag ⟨0⟩ right rightActual rightTag
  exact ⟨leftSource, leftTarget, rightSource, rightTarget,
    leftActual.symm.trans leftRun, rightActual.symm.trans rightRun, leftPrepared, rightPrepared⟩

/-- Inhabited composition of TWO actually expanded, mutually recursive table
    entries. There is no supplied outcome, semantic relation or callback. -/
theorem two_updated_mutual_entries_preserve_every_framed_call :
    ∃ leftSource leftTarget rightSource rightTarget,
      AllBlocks.functions direct (fun _ => none) header (graph ⟨1⟩) = .ok (.expanded leftSource leftTarget) ∧
      AllBlocks.functions direct (fun _ => none) header (graph ⟨0⟩) = .ok (.expanded rightSource rightTarget) ∧
      ∀ base,
        FramedCallsEquivalent
          (installFirst FunctionUpdate.source base
            [⟨⟨0⟩, leftSource, leftTarget⟩, ⟨⟨1⟩, rightSource, rightTarget⟩])
          (installFirst FunctionUpdate.target base
            [⟨⟨0⟩, leftSource, leftTarget⟩, ⟨⟨1⟩, rightSource, rightTarget⟩]) := by
  obtain ⟨leftSource, leftTarget, rightSource, rightTarget, leftRun, rightRun, leftPrepared, rightPrepared⟩ :=
    mutual_replacements
  refine ⟨leftSource, leftTarget, rightSource, rightTarget, leftRun, rightRun, ?_⟩
  intro base
  apply installFirst_framedCallsEquivalent
  intro update member
  rcases List.mem_cons.mp member with same | later
  · cases same; exact leftPrepared
  · rcases List.mem_cons.mp later with same | impossible
    · cases same; exact rightPrepared
    · cases impossible

/-- Shadowed duplicates are raw ordered-table controls, not validator-admitted
    module claims. The later source/target entry cannot replace the first one. -/
theorem duplicate_key_composition_preserves_winning_occurrence :
    ∃ leftSource leftTarget rightSource rightTarget,
      AllBlocks.functions direct (fun _ => none) header (graph ⟨1⟩) = .ok (.expanded leftSource leftTarget) ∧
      AllBlocks.functions direct (fun _ => none) header (graph ⟨0⟩) = .ok (.expanded rightSource rightTarget) ∧
      ∀ base,
        let updates : List FunctionUpdate :=
          [⟨⟨0⟩, leftSource, leftTarget⟩, ⟨⟨1⟩, rightSource, rightTarget⟩, ⟨⟨0⟩, rightSource, rightTarget⟩]
        (installFirst FunctionUpdate.source base updates).functions ⟨0⟩ = some leftSource ∧
        (installFirst FunctionUpdate.target base updates).functions ⟨0⟩ = some leftTarget ∧
        FramedCallsEquivalent (installFirst FunctionUpdate.source base updates)
          (installFirst FunctionUpdate.target base updates) := by
  obtain ⟨leftSource, leftTarget, rightSource, rightTarget, leftRun, rightRun, leftPrepared, rightPrepared⟩ :=
    mutual_replacements
  refine ⟨leftSource, leftTarget, rightSource, rightTarget, leftRun, rightRun, ?_⟩
  intro base
  refine ⟨rfl, rfl, ?_⟩
  apply installFirst_framedCallsEquivalent
  intro update member
  rcases List.mem_cons.mp member with same | later
  · cases same; exact leftPrepared
  · rcases List.mem_cons.mp later with same | later
    · cases same; exact rightPrepared
    · rcases List.mem_cons.mp later with same | impossible
      · cases same; exact rightPrepared
      · cases impossible

theorem undefined_and_bodyless_other_entries_keep_exact_errors
    (leftSource leftTarget rightSource rightTarget : EvalFunction) (fuel depth : Nat)
    (args : List Value) (strategy : PanicStrategy) (caller : MachineState) :
    let updates : List FunctionUpdate :=
      [⟨⟨0⟩, leftSource, leftTarget⟩, ⟨⟨1⟩, rightSource, rightTarget⟩]
    Sem.run (runCallReq (installFirst FunctionUpdate.source EvalContext.empty updates)
      fuel depth ⟨99⟩ args strategy) caller = .error (.typeError "Call: undefined function") ∧
    Sem.run (runCallReq (installFirst FunctionUpdate.target
      { EvalContext.empty with declared := fun _ => true } updates)
      fuel depth ⟨99⟩ args strategy) caller =
        .error (.unsupported .interproceduralCall "Call: callee is a bodyless declaration") := ⟨rfl, rfl⟩

end Controls
end TrustIr.GenericCoro.AllBlocksContext
