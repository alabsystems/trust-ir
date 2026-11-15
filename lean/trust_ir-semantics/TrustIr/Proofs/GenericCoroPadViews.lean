-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroTermContext
import TrustIr.Proofs.SSAFreshUnwindBody

namespace TrustIr.GenericCoro.PadViews
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshDispatch SSAFreshUnwindBody

/-- The outer option records block presence; the inner option records whether
    its first instruction is a landing pad. Neither distinction is erased. -/
abbrev PadView := Option (Option (Bool × List Nat))

def padView (cfg : CFG) (destination : BlockId) : PadView :=
  (cfg destination).map (fun block => block.body.head?.bind Inst.padClauses)

def PadViewsAgree (source target : CFG) : Prop :=
  ∀ destination, padView source destination = padView target destination

/-- Pad entry observes only presence and the first instruction's exact pad
    clauses. Exception lookup, typed-catch refusal, selector and throw state
    remain the actual production computation. -/
theorem semEnterPad_congr (source target : CFG) (exception : Addr) (destination : BlockId)
    (view : padView source destination = padView target destination) :
    semEnterPad source exception destination = semEnterPad target exception destination := by
  trustIrCompilerProof {
    cases sourceFound : source destination with
    | none =>
      cases targetFound : target destination with
      | none => simp only [semEnterPad, sourceFound, targetFound]
      | some block => simp only [padView, sourceFound, targetFound, Option.map] at view
    | some sourceBlock =>
      cases targetFound : target destination with
      | none => simp only [padView, sourceFound, targetFound, Option.map] at view
      | some targetBlock =>
        simp only [padView, sourceFound, targetFound, Option.map, Option.some.injEq] at view
        simp only [semEnterPad, sourceFound, targetFound, view]
  } {
    cases sourceFound : source destination with
    | none =>
      cases targetFound : target destination with
      | none => simp only [semEnterPad, sourceFound, targetFound]
      | some block =>
        simp only [padView, sourceFound, targetFound, Option.map] at view
        cases view
    | some sourceBlock =>
      cases targetFound : target destination with
      | none =>
        simp only [padView, sourceFound, targetFound, Option.map] at view
        cases view
      | some targetBlock =>
        simp only [padView, sourceFound, targetFound, Option.map, Option.some.injEq] at view
        simp only [semEnterPad, sourceFound, targetFound, view]
  }

theorem stepTermUnwind_congr (source target : CFG) (term : Inst) (model : ByteModel)
    (views : PadViewsAgree source target) :
    stepTermUnwind source term model = stepTermUnwind target term model := by
  have pads : ∀ exception destination,
      semEnterPad source exception destination = semEnterPad target exception destination :=
    fun exception destination => semEnterPad_congr source target exception destination (views destination)
  cases term <;> simp only [stepTermUnwind, pads]

/-- Different CFGs need only agree on actual unwind observations. Callable
    resolution and byte-model equality are the existing complete observations;
    no CFG identity or recursive-evaluator equality is assumed. -/
theorem stepTermWithContext_congr (source target : EvalContext) (depth : Nat)
    (sourceCFG targetCFG : CFG) (term : Inst) (strategy : PanicStrategy)
    (models : source.byteModel = target.byteModel)
    (functions : ∀ held function signature,
      functionCall source held function signature = functionCall target held function signature)
    (closures : ∀ cid function captures signature args convention,
      closureCall source cid function captures signature args convention =
        closureCall target cid function captures signature args convention)
    (views : PadViewsAgree sourceCFG targetCFG) :
    stepTermWithContext source depth sourceCFG term strategy =
      stepTermWithContext target depth targetCFG term strategy := by
  cases strategy <;> unfold stepTermWithContext <;>
    apply closureTermWithContext_congr source target depth term _ _ functions closures
  · rw [models]
  · rw [models]
    exact stepTermUnwind_congr sourceCFG targetCFG term target.byteModel views

/-- Only inHand changes on successful pad entry. All error paths retain their
    production behavior, without a successful-entry or exception premise. -/
theorem semEnterPad_fresh (cfg : CFG) (exception : Addr) (destination : BlockId) :
    KeepsFresh (semEnterPad cfg exception destination) := by
  unfold semEnterPad
  with_reducible (repeat' (first
    | exact throw_fresh _
    | exact throwTypeError_fresh _
    | exact throwUnsupported_fresh _ _
    | exact modify_fresh _ (fun state fresh => sameSSA_fresh state _ fresh rfl rfl)
    | exact pure_fresh _
    | refine bind_fresh _ _ get_fresh (fun state => ?_)
    | intro value
    | split))

theorem semResumeUnwind_fresh (exception : ValueId) :
    KeepsFresh (semResumeUnwind exception) := by
  unfold semResumeUnwind
  refine bind_fresh _ _ (lookup_fresh exception) (fun value => ?_)
  refine bind_fresh _ _ get_fresh (fun state => ?_)
  cases value <;> dsimp only
  all_goals first
    | exact throwUB_fresh _
    | (split <;> first | exact throw_fresh _ | exact throwUB_fresh _)

theorem stepTermUnwind_fresh (cfg : CFG) (term : Inst) (model : ByteModel) :
    KeepsFresh (stepTermUnwind cfg term model) := by
  cases term <;> simp only [stepTermUnwind]
  case AssertInvoke condition kind site normal normalArgs unwind =>
    apply tryCatch_fresh _ _ (stepInst_fresh _ _)
    intro error
    cases error
    case panic message site =>
      exact bind_fresh _ _ (semAllocException_fresh _ _ _) (fun exception =>
        bind_fresh _ _ (semEnterPad_fresh cfg exception _) (fun _ => pure_fresh _))
    all_goals exact throw_fresh _
  case Resume exception => exact semResumeUnwind_fresh exception
  all_goals exact stepInst_fresh _ _

/-- Function and closure resolvers are pure checks. This terminator prelude
    never executes a callee body and needs no callback/caller premise. -/
theorem closureTermWithContext_fresh (ctx : EvalContext) (depth : Nat) (term : Inst)
    (fallback : Sem InstrResult) (fallbackFresh : KeepsFresh fallback) :
    KeepsFresh (closureTermWithContext ctx depth term fallback) := by
  cases term <;> try exact fallbackFresh
  all_goals
    unfold closureTermWithContext
    with_reducible (repeat' (first
      | exact fallbackFresh
      | exact throw_fresh _
      | exact throwTypeError_fresh _
      | exact pure_fresh _
      | exact lookup_fresh _
      | exact mapM_fresh Sem.lookupValue _ lookup_fresh
      | refine bind_fresh _ _ ?_ (fun value => ?_)
      | intro value
      | split))

/-- Successful high-water preservation for every actual contextual
    terminator, CFG, strategy and resource depth. No callee runs here. -/
theorem stepTermWithContext_fresh (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (term : Inst) (strategy : PanicStrategy) :
    KeepsFresh (stepTermWithContext ctx depth cfg term strategy) := by
  cases strategy <;> unfold stepTermWithContext <;> apply closureTermWithContext_fresh
  · exact stepInst_fresh _ _
  · exact stepTermUnwind_fresh _ _ _

namespace Controls

def missing : CFG := fun _ => none

def withoutPad : CFG := fun _ => some { params := [], body := [], terminator := .Return [] }

def cleanup : CFG := fun _ => some {
  params := [], body := [.LandingPad true []], terminator := .Return [] }

def catchAll : CFG := fun _ => some {
  params := [], body := [.LandingPad false [0]], terminator := .Return [] }

def typedCatch : CFG := fun _ => some {
  params := [], body := [.LandingPad false [1]], terminator := .Return [] }

def raised : MachineState := { MachineState.empty with exceptions := [(7, ⟨0⟩, "pad-view", none)] }

theorem absence_and_nonpad_are_distinct : padView missing ⟨9⟩ ≠ padView withoutPad ⟨9⟩ := by
  intro equality
  cases equality

theorem missing_block_keeps_error :
    Sem.run (semEnterPad missing 7 ⟨9⟩) raised =
      .error (.typeError (trustIrStringBuild s!"undefined block: {repr (⟨9⟩ : BlockId)}")) := rfl

theorem present_nonpad_keeps_error :
    Sem.run (semEnterPad withoutPad 7 ⟨9⟩) raised =
      .error (.typeError "unwind destination does not begin with a landing pad") := rfl

theorem cleanup_selector_zero :
    (Sem.run (semEnterPad cleanup 7 ⟨9⟩) raised).map (fun result => result.2.inHand) =
      .ok (some (7, ⟨0⟩, 0)) := rfl

theorem catch_all_selector_one :
    (Sem.run (semEnterPad catchAll 7 ⟨9⟩) raised).map (fun result => result.2.inHand) =
      .ok (some (7, ⟨0⟩, 1)) := rfl

theorem typed_catch_keeps_refusal :
    Sem.run (semEnterPad typedCatch 7 ⟨9⟩) raised =
      .error (.unsupported .typedCatch
        "landingpad: a typed catch clause needs a typeinfo model the format does not have") := rfl


def cleanupWithTail : CFG := fun _ => some {
  params := [], body := [.LandingPad true [], .Const .I64 (.int 99)], terminator := .Unreachable }

theorem different_cfgs_have_equal_pad_views : PadViewsAgree cleanup cleanupWithTail :=
  fun _ => rfl

theorem actual_pad_entry_ignores_other_cfg_fields :
    semEnterPad cleanup 7 ⟨9⟩ = semEnterPad cleanupWithTail 7 ⟨9⟩ :=
  semEnterPad_congr _ _ _ _ rfl

theorem typed_catch_checks_exception_first :
    Sem.run (semEnterPad typedCatch 7 ⟨9⟩) MachineState.empty =
      .error (.typeError "an unwinding carries an exception this run never raised") := rfl

end Controls
end TrustIr.GenericCoro.PadViews

#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.absence_and_nonpad_are_distinct == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.catch_all_selector_one == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.cleanup_selector_zero == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.different_cfgs_have_equal_pad_views == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.missing_block_keeps_error == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.present_nonpad_keeps_error == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.typed_catch_checks_exception_first == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.Controls.typed_catch_keeps_refusal == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.PadViewsAgree == []
#trustIrAxiomsExact TrustIr.GenericCoro.PadViews.padView == []
