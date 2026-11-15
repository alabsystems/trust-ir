-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameInstructionAdmission
import TrustIr.Proofs.DecodedFunctionLookupProps
import TrustIr.Proofs.GenericCoroIndexedCFG

namespace TrustIr.FrameLifetime
open GenericCoro

/-- A proof-side source-position check. This is not a new runtime admission
rule, type validator or compiler certificate. Declarations and decode failures
retain their original lazy runtime treatment. -/
def decoded_frame_shape_check (source : TrustIrEval.Module) : Bool :=
  source.functions.all (fun function =>
    if function.isDeclaration then true else
      match function.blocks with
      | .error _ => true
      | .ok blocks => blocks.all (fun row =>
          row.2.body.all (fun inst => !inst.isTerminator) && row.2.terminator.isTerminator))

private theorem find_some_member {α : Type} (predicate : α → Bool) (rows : List α)
    (value : α) (found : rows.find? predicate = some value) : value ∈ rows := by
  induction rows with
  | nil => cases found
  | cons head rest ih =>
    cases selected : predicate head <;> simp only [List.find?,selected] at found
    · exact .tail _ (ih found)
    · cases found; exact .head _

private theorem filter_map_property {α β : Type} (select : α → Option β) (rows : List α) (property : β → Prop)
    (safe : ∀ row ∈ rows, ∀ value, select row = some value → property value) :
    ∀ value ∈ rows.filterMap select, property value := by
  induction rows with
  | nil => intro value member; cases member
  | cons head rest ih =>
    intro value member
    cases selected : select head <;> simp only [List.filterMap,selected] at member
    · exact ih (fun row member => safe row (.tail _ member)) value member
    · cases member with
      | head => exact safe head (.head _) _ selected
      | tail _ member => exact ih (fun row member => safe row (.tail _ member)) value member

/-- Exact prepared first-match selection retains a property of actual
successful executable rows, without assuming unique ids or metadata success. -/
theorem prepared_function_property (source : List TrustIrEval.Function)
    (definitions : List (FuncId × TrustIrEval.D EvalFunction)) (property : EvalFunction → Prop)
    (safe : ∀ row ∈ definitions, ∀ function, row.2 = .ok function → property function)
    (id : FuncId) (function : EvalFunction)
    (found : TrustIrEval.FunctionLookup.findFunction (TrustIrEval.FunctionLookup.prepare source definitions) id = some function) :
    property function := by
  rw [TrustIrEval.FunctionLookup.findFunction_prepare] at found
  cases selected : definitions.find? (fun row => row.1 == id) with
  | none => rw [selected] at found; cases found
  | some row =>
    obtain ⟨key,result⟩ := row
    have member := find_some_member _ _ _ selected
    cases result with
    | error error => rw [selected] at found; cases found
    | ok held =>
      rw [selected] at found
      cases found
      exact safe _ member _ rfl

/-- Successful conversion preserves the exact source CFG through its actual
first-wins index. Original signature and inference failures stay unchanged. -/
theorem converted_function_block_shape (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef)
    (source : TrustIrEval.Function) (blocks : List (BlockId × BasicBlock)) (function : EvalFunction)
    (converted : TrustIrEval.evalFunctionOfWithTypes signatures direct source blocks = .ok function)
    (shape : ∀ row ∈ blocks, (∀ inst ∈ row.2.body, inst.isTerminator = false) ∧ row.2.terminator.isTerminator = true) :
    FrameBlockShape function.cfg := by
  have cfg : function.cfg = TrustIrEval.cfgOf blocks := by
    unfold TrustIrEval.evalFunctionOfWithTypes at converted
    simp only [bind,pure,Except.bind,Except.pure,TrustIrEval.malformed,
      throw,throwThe,MonadExceptOf.throw] at converted
    repeat' first
      | (solve | cases converted; exact IndexedCFG.indexedCFG_eq_cfgOf blocks)
      | (solve | cases converted)
      | split at converted
  rw [cfg]
  intro pc block found
  unfold TrustIrEval.cfgOf at found
  cases selected : blocks.find? (fun row => row.1 == pc) with
  | none => rw [selected] at found; cases found
  | some row =>
    obtain ⟨key,held⟩ := row
    rw [selected] at found
    cases found
    exact shape (key,held) (find_some_member _ _ _ selected)

private theorem decoded_definitions_shape (source : TrustIrEval.Module) (checked : decoded_frame_shape_check source = true)
    (signatures : Array FuncTyDef) (direct : FuncId → Option FuncTyDef) :
    ∀ row ∈ source.functions.filterMap (fun function =>
      match function.blocks with
      | .ok blocks => if function.isDeclaration then none
          else some (function.id, TrustIrEval.evalFunctionOfWithTypes signatures direct function blocks)
      | .error _ => none),
      ∀ function, row.2 = .ok function → FrameBlockShape function.cfg := by
  trustIrCompilerProof {
    apply filter_map_property
    intro original member row selected function converted
    have held := List.all_eq_true.mp checked original member
    cases decoded : original.blocks with
    | error error => rw [decoded] at selected; cases selected
    | ok blocks =>
      rw [decoded] at selected
      cases declaration : original.isDeclaration with
      | true => simp only [declaration,↓reduceIte] at selected
      | false =>
        simp only [declaration,↓reduceIte] at selected
        cases selected
        apply converted_function_block_shape signatures direct original blocks function converted
        simp only [declaration,decoded,↓reduceIte] at held
        intro row member
        have block := List.all_eq_true.mp held row member
        have parts := (Bool.and_eq_true_iff _ _).mp block
        refine ⟨?_,parts.2⟩
        intro inst member
        have ordinary := List.all_eq_true.mp parts.1 inst member
        cases flag : inst.isTerminator <;> simp_all only [Bool.not_false,Bool.not_true,Bool.false_eq_true]
  } {
    apply filter_map_property
    intro original member row selected function converted
    have held := List.all_eq_true.mp checked original member
    cases decoded : original.blocks with
    | error error => rw [decoded] at selected; cases selected
    | ok blocks =>
      rw [decoded] at selected
      cases declaration : original.isDeclaration with
      | true => simp only [declaration,↓reduceIte] at selected; cases selected
      | false =>
        simp only [declaration,↓reduceIte] at selected
        cases selected
        apply converted_function_block_shape signatures direct original blocks function converted
        simp only [declaration,decoded,↓reduceIte] at held
        intro row member
        have block := List.all_eq_true.mp held row member
        have parts := Bool.and_eq_true_iff.mp block
        refine ⟨?_,parts.2⟩
        intro inst member
        have ordinary := List.all_eq_true.mp parts.1 inst member
        cases flag : inst.isTerminator <;> simp_all only [Bool.not_false,Bool.not_true,Bool.false_eq_true]
  }

/-- Actual complete context assembly, source filtering and prepared lookups
supply the callee shape premise from a source-side finite check. -/
theorem decoded_context_program_shape (source : TrustIrEval.Module) (depth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source depth = .ok ctx) (checked : decoded_frame_shape_check source = true) :
    FrameProgramShape ctx := by
  unfold TrustIrEval.contextOf at assembled
  simp only [bind,pure,Except.bind,Except.pure,TrustIrEval.unsupported,
    throw,throwThe,MonadExceptOf.throw] at assembled
  repeat' first
    | (solve | cases assembled)
    | split at assembled
  cases assembled
  intro id function found
  exact prepared_function_property source.functions _ (fun function => FrameBlockShape function.cfg)
    (decoded_definitions_shape source checked (TrustIrEval.localTypeHeadersOf source).1 (TrustIrEval.localTypeHeadersOf source).2) id function found

/-- The public entry runner retains its original ABI/arity/poison guards,
actual callee scope, configured depth, unwind conversion and return check. -/
theorem shaped_function_frame_exit (ctx : EvalContext) (program : FrameProgramShape ctx)
    (safe : StaticFunctionErrors ctx) (headers : HeaderContextErrors ctx) (memory : MemoryContextErrors ctx)
    (entry : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (evalFunctionInContext ctx entry args fuel strategy) state) := by
  trustIrCompilerProof {
    unfold evalFunctionInContext
    cases selected : ctx.functions entry with
    | none => exact True.intro
    | some function =>
      simp only [selected,pure_bind]
      cases abi : function.body.abi with
      | some descriptor =>
        simp only [requireUntypedAbi,abi,Option.isSome,↓reduceIte]
        exact True.intro
      | none =>
        simp only [requireUntypedAbi,abi,Option.isSome,↓reduceIte,pure_bind]
        cases arity : checkCallArity args function.body.paramTys with
        | error message => simp only [arity]; exact True.intro
        | ok unit =>
          cases unit
          simp only [arity,pure_bind]
          unfold Sem.rejectPoisonValues
          by_cases poison : args.any Value.isPoison = true
          · simp only [poison,↓reduceIte]; exact True.intro
          · simp only [poison,↓reduceIte,pure_bind]
            apply (FrameActionExit.callee state _).1
            apply FrameActionExit.bind MintedArgs MintedArgs _ _ state
              ((FrameActionExit.callee state _).2
                (shaped_frame_entry_exit (ctx.forFunction function) function.cfg (program entry function selected)
                  (show FrameProgramShape (ctx.forFunction function) from program)
                  (StaticFunctionErrors.forFunction ctx function safe)
                  (HeaderContextErrors.forFunction ctx function headers)
                  (MemoryContextErrors.forFunction ctx function memory)
                  fuel ctx.maxCallDepth function.entryBlock args strategy state valid incoming))
            intro returned after afterValid minted
            by_cases rejected : returned.any Value.isPoison = true
            · simp only [rejected,↓reduceIte]; exact True.intro
            · simp only [rejected,↓reduceIte,pure_bind]
              exact ⟨afterValid,minted,.refl _⟩
  } {
    unfold evalFunctionInContext
    cases selected : ctx.functions entry with
    | none => exact True.intro
    | some function =>
      simp only [selected,pure_bind]
      cases abi : function.body.abi with
      | some descriptor =>
        simp only [requireUntypedAbi,abi,Option.isSome,Bool.false_eq_true,↓reduceIte]
        exact True.intro
      | none =>
        simp only [requireUntypedAbi,abi,Option.isSome,Bool.false_eq_true,↓reduceIte,pure_bind]
        cases arity : checkCallArity args function.body.paramTys with
        | error message => simp only [arity]; exact True.intro
        | ok unit =>
          cases unit
          simp only [arity,pure_bind]
          unfold Sem.rejectPoisonValues
          by_cases poison : args.any Value.isPoison = true
          · simp only [poison,Bool.false_eq_true,↓reduceIte]; exact True.intro
          · simp only [poison,Bool.false_eq_true,↓reduceIte,pure_bind]
            apply (FrameActionExit.callee state _).1
            apply FrameActionExit.bind MintedArgs MintedArgs _ _ state
              ((FrameActionExit.callee state _).2
                (shaped_frame_entry_exit (ctx.forFunction function) function.cfg (program entry function selected)
                  (show FrameProgramShape (ctx.forFunction function) from program)
                  (StaticFunctionErrors.forFunction ctx function safe)
                  (HeaderContextErrors.forFunction ctx function headers)
                  (MemoryContextErrors.forFunction ctx function memory)
                  fuel ctx.maxCallDepth function.entryBlock args strategy state valid incoming))
            intro returned after afterValid minted
            by_cases rejected : returned.any Value.isPoison = true
            · simp only [rejected,Bool.false_eq_true,↓reduceIte]; exact True.intro
            · simp only [rejected,Bool.false_eq_true,↓reduceIte,pure_bind]
              exact ⟨afterValid,minted,.refl _⟩
  }

/-- Full original public entry execution from actual decoded source assembly.
Only the finite source-position check and initial frame premises remain. -/
theorem decoded_module_frame_exit (source : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source maxDepth = .ok ctx) (checked : decoded_frame_shape_check source = true)
    (entry : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameCalleeExit state (Sem.run (evalFunctionInContext ctx entry args fuel strategy) state) :=
  shaped_function_frame_exit ctx (decoded_context_program_shape source maxDepth ctx assembled checked)
    (decoded_context_errors_static source maxDepth ctx assembled)
    (decoded_context_header_errors source maxDepth ctx assembled)
    (decoded_context_memory_errors source maxDepth ctx assembled)
    entry args fuel strategy state valid incoming

/-- The ordinary empty-machine entry needs only frame-free arguments. -/
theorem decoded_module_empty_frame_exit (source : TrustIrEval.Module) (maxDepth : Nat) (ctx : EvalContext)
    (assembled : TrustIrEval.contextOf source maxDepth = .ok ctx) (checked : decoded_frame_shape_check source = true)
    (entry : FuncId) (args : List Value) (fuel : Nat) (strategy : PanicStrategy) (incoming : MintedArgs 0 args) :
    FrameCalleeExit MachineState.empty (Sem.run (evalFunctionInContext ctx entry args fuel strategy) MachineState.empty) :=
  decoded_module_frame_exit source maxDepth ctx assembled checked entry args fuel strategy
    MachineState.empty WellMintedState.empty incoming

end TrustIr.FrameLifetime
