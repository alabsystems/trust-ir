-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrEval.ModuleRunBatchProof
import TrustIr.Proofs.GenericCoroModuleFactoryControls

namespace TrustIrEval.ModuleRunBatch.Controls
open TrustIr TrustIr.GenericCoro TrustIr.GenericCoroAllBlocksPlanner
open ModuleFactory

/-- This really is the published two-function, nonentry-suspend factory
    output; the request rows, choice rows and all resource values stay fixed. -/
theorem actual_multifunction_batch (fuel depth : Nat) (strategy : PanicStrategy)
    (runs : List (FuncId × List Value)) (choices : List (List Bool)) :
    runBatch fuel depth strategy {module := ModuleFactory.Controls.source, runs := runs, floatZeroChoices := choices} =
    runBatch fuel depth strategy {module := ModuleFactory.Controls.target, runs := runs, floatZeroChoices := choices} :=
  transform_ready_runBatch _ _ ModuleFactory.Controls.actual_multifunction_ast
    fuel depth strategy _ rfl

/-- A nonempty successful response from the actual changed module, whose
    source table also contains both lowered coroutine definitions. -/
theorem actual_changed_module_positive :
    runBatch 1 0 .abort {module := ModuleFactory.Controls.target, runs := [(⟨3⟩, [.int 32 42])]} =
    .arr #[obj [("ok", Observation.renderGraph [.int 32 42])]] := by
  rw [← actual_multifunction_batch 1 0 .abort [(⟨3⟩, [.int 32 42])] []]
  rfl

def signature : FuncTyDef :=
  {params := [.I32], returns := [.I32], isVararg := false}

def declaration : Function :=
  {id := ⟨17⟩, name := "declared-first", ty := ⟨0⟩, entry := ⟨0⟩,
    isDeclaration := true, blocks := .ok []}

def identity : Function :=
  {id := ⟨17⟩, name := "executable-later", ty := ⟨0⟩, entry := ⟨0⟩,
    isDeclaration := false, blocks := .ok [(⟨0⟩,
      {params := [(⟨0⟩, .I32)], body := [], terminator := .Return [⟨0⟩]})]}

def duplicateModule : Module :=
  {functions := [declaration, identity], funcTys := [signature], globals := [],
    enums := [], structs := [], types := []}

theorem actual_duplicate_ready : transform duplicateModule = .ready duplicateModule := rfl

/-- First raw declaration, later executable definition, and any-declaration
    classification coexist. This is raw-AST evidence, not validator credit. -/
theorem duplicate_success :
    runBatch 1 0 .abort {module := duplicateModule, runs := [(⟨17⟩, [.int 32 42])], floatZeroChoices := [[true, false]]} =
    .arr #[obj [("ok", Observation.renderGraph [.int 32 42])]] := rfl

theorem duplicate_zero_fuel :
    runBatch 0 0 .abort {module := duplicateModule, runs := [(⟨17⟩, [.int 32 42])]} =
    .arr #[obj [("out_of_fuel", .bool true)]] := rfl

theorem missing_entry_exact :
    runBatch 0 0 .unwind {module := duplicateModule, runs := [(⟨99⟩, [])]} =
    .arr #[obj [("error", jstr "entry function 99 is not in the module")]] := rfl

theorem bodyless_entry_exact :
    runBatch 0 0 .abort {module := {duplicateModule with functions := [declaration]}, runs := [(⟨17⟩, [])]} =
    .arr #[obj [("unsupported", jstr "interprocedural_call"),
      ("detail", jstr "entry function is a bodyless declaration")]] := rfl

def dropBlock : BasicBlock :=
  {params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32)], body := [.Drop .I32 ⟨1⟩],
    bodyResultDests := [[]], terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨1⟩}

def dropFunction : Function :=
  {id := ⟨5⟩, name := "partial-drop-table", ty := ⟨0⟩, entry := ⟨0⟩,
    isDeclaration := false, blocks := .ok [(⟨0⟩, dropBlock)]}

def dropSource : Module :=
  {functions := [dropFunction],
    funcTys := [{params := [.Ptr, .I32], returns := [.I32], isVararg := false}],
    globals := [], enums := [], structs := [], types := [], dropGlue := [(⟨65537⟩, none)]}

def dropTarget : Module :=
  {dropSource with functions := [{dropFunction with
    blocks := .ok [(⟨0⟩, expandedEntry ⟨⟨2⟩, ⟨3⟩, ⟨4⟩⟩ dropBlock)]}]}

theorem actual_partial_drop_ready : transform dropSource = .ready dropTarget := rfl

theorem partial_drop_source_preflight :
    reachableDecodeFailure dropSource ⟨5⟩ = some (.unsupported "drop_glue.key") := rfl

theorem partial_drop_target_preflight :
    reachableDecodeFailure dropTarget ⟨5⟩ = some (.unsupported "drop_glue.key") :=
  (transform_ready_reachableDecodeFailure dropSource dropTarget actual_partial_drop_ready ⟨5⟩).symm.trans
    partial_drop_source_preflight

/-- The actual changed target retains the partial-key refusal BEFORE both
    the zero-fuel and malformed entry-arity paths. -/
theorem partial_drop_batch_priority :
    runBatch 0 0 .unwind {module := dropTarget, runs := [(⟨5⟩, [])], floatZeroChoices := [[true]]} =
    .arr #[renderDecodeError (.unsupported "drop_glue.key")] := by
  rw [← transform_ready_runBatch dropSource dropTarget actual_partial_drop_ready 0 0 .unwind
    {module := dropSource, runs := [(⟨5⟩, [])], floatZeroChoices := [[true]]} rfl]
  rfl

/-- First-match raw-row lookup is not silently replaced by executable lookup. -/
theorem duplicate_raw_preflight :
    reachableDecodeFailure {dropSource with functions :=
      [{declaration with id := ⟨5⟩}, dropFunction]} ⟨5⟩ = none := rfl

theorem namespace_overflow_exact :
    initialStateForFunctionCount .le32 (2 ^ 32 - 1) =
      .error (.typeError "function address namespace exceeds target pointer width") := rfl

theorem empty_batch_context_error :
    runBatch 0 0 .abort {module := {duplicateModule with
      byteModel := .error (.unsupported "target.control")}, runs := []} = .arr #[] := rfl

end TrustIrEval.ModuleRunBatch.Controls
