-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Multi-step evaluation: stepBlock, stepN (fuel-based).
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 2

import TrustIrNativeLink
import TrustIr.Semantics.ClosureTypes
import TrustIr.Semantics.Step
import TrustIr.Semantics.LocalTypes
import TrustIr.Semantics.CharValidity
import TrustIr.Semantics.FunctionItemPresence
import TrustIr.Semantics.AggregateAccess
import TrustIr.StringCompat

namespace TrustIr

/-!
# Multi-Step Evaluation

## Basic Blocks

A basic block is a sequence of non-terminator instructions followed
by exactly one terminator. Block parameters receive values from
incoming branches (replaces phi nodes).

## Fuel-Based Termination

For Lean's termination checker, we use a fuel parameter for loops.
`stepN` takes `fuel : Nat` and decrements it on each block step.
`SemError.outOfFuel` is produced when fuel runs out.

For terminating programs with sufficient fuel, `outOfFuel` is never
produced. Proofs about total correctness prove sufficient fuel exists.
Proofs about partial correctness ignore the fuel parameter.
-/

/-- A basic block: parameters, body instructions, and terminator. -/
structure BasicBlock where
  params     : List (ValueId × Ty)     -- Block parameters
  body       : List Inst               -- Non-terminator instructions
  /-- Result destinations for `body`, positionally mirroring Rust
      `InstrNode.results`.  Older Lean fixtures that only rely on fresh
      sequential SSA ids leave this empty. -/
  bodyResultDests : List (List ValueId) := []
  terminator : Inst                    -- Terminator instruction
  /-- Result destinations for a value-producing TERMINATOR (`Inst.Invoke`:
      the callee's returns bind the invoke node's own results on the normal
      edge), mirroring Rust `InstrNode.results`. Empty for ordinary
      terminators. -/
  terminatorResultDests : List ValueId := []
  deriving Repr

/-- A control flow graph: mapping from BlockId to BasicBlock. -/
def CFG := BlockId → Option BasicBlock

/-- Bind block parameters to incoming values. -/
def bindBlockParams (params : List (ValueId × Ty)) (args : List Value) : Sem Unit := do
  if params.length != args.length then
    Sem.throwTypeError (trustIrStringBuild s!"block parameter count mismatch: expected {params.length}, got {args.length}")
  else
    let s ← Sem.getState
    let locals' := (params.zip args).foldl
      (fun locals binding => locals.set binding.fst.fst binding.snd)
      s.locals
    let nextValueId' := params.foldl
      (fun next param => max next (param.fst.index + 1))
      s.nextValueId
    Sem.setState { s with locals := locals', nextValueId := nextValueId' }

/-- Contextual block binding keeps the original arity refusal and checks only
    top-level Char integer validity before publishing the parameters. -/
def bindBlockParamsChecked (params : List (ValueId × Ty)) (args : List Value) : Sem Unit := do
  if params.length != args.length then bindBlockParams params args
  else
    match checkSSACharValues (params.map Prod.snd) args with
    | .ok () => bindBlockParams params args
    | .error error => throw error

/-- Pair body instructions with their call-site/result destinations.
    Missing destination rows default to `[]` so existing Lean blocks keep their
    historical fresh-result behavior. -/
def bodyInstsWithResultDests :
    List Inst → List (List ValueId) → List (Inst × List ValueId)
  | [], _ => []
  | inst :: insts, [] =>
      (inst, []) :: bodyInstsWithResultDests insts []
  | inst :: insts, dests :: restDests =>
      (inst, dests) :: bodyInstsWithResultDests insts restDests

/-- Bind returned values to explicit SSA destinations from the enclosing
    instruction node. -/
def bindResultDests (dests : List ValueId) (values : List Value) : Sem Unit := do
  if dests.length != values.length then
    Sem.throwTypeError
      (trustIrStringBuild s!"call result count mismatch: expected {dests.length}, got {values.length}")
  else
    let s ← Sem.getState
    let locals' := (dests.zip values).foldl
      (fun locals binding => locals.set binding.fst binding.snd)
      s.locals
    let nextValueId' := dests.foldl
      (fun next dest => max next (dest.index + 1))
      s.nextValueId
    Sem.setState { s with locals := locals', nextValueId := nextValueId' }

/-- Bind a body instruction's results to the explicit result destinations of
    its node, mirroring Rust interpret.rs `bind_results`.

    * A single-result instruction (`.value (some r)`) binds one destination;
      an absent destination row (`[]`) keeps the historical fresh-result
      behavior of hand-written Lean blocks. With an explicit destination,
      a distinct private result id is retired after publication, just as the
      multiple-result case retires its private component ids.
    * A multi-result instruction (`.values rs` — `Overflow`, `CmpXchg`) binds
      its components POSITIONALLY: `dests[i] := rs[i]`. It requires
      `dests.length == rs.length` EXACTLY — including the empty row, since a
      multi-result instruction has no historical fresh convention (the packed
      aggregate is deleted, WS2.24) — and any mismatch is the TypeError
      "instruction result count mismatch", exactly as Rust refuses a node
      whose declared results differ from what the instruction produced.
      The fresh component ids the instruction bound are then RETIRED unless
      they are themselves destinations, so the node defines exactly its
      destinations (a stale temporary would let a read Rust refuses as an
      undefined value succeed in Lean). -/
def bindInstrResultDests : InstrResult → List ValueId → Sem Unit
  | .value none, [] => pure ()
  | .value none, _ :: _ =>
      Sem.throwTypeError "instruction result count mismatch"
  | .value (some _), [] => pure ()
  | .value (some result), dest :: [] => do
      let value ← Sem.lookupValue result
      bindResultDests [dest] [value]
      if result != dest then
        let s ← Sem.getState
        Sem.setState { s with locals := fun id => if id == result then none else s.locals id }
  | .value (some _), _ :: _ :: _ =>
      Sem.throwTypeError "instruction result count mismatch"
  | .values results, dests =>
      if dests.length != results.length then
        Sem.throwTypeError "instruction result count mismatch"
      else do
        let values ← results.mapM Sem.lookupValue
        bindResultDests dests values
        -- The node's results are EXACTLY its declared destinations: retire
        -- every fresh component id that is not itself a destination, so a
        -- later read of it is the same undefined-value error Rust raises
        -- (interpret.rs binds only `node.results`; it has no temporaries).
        let s ← Sem.getState
        let locals' := results.foldl
          (fun locals tmp =>
            if dests.contains tmp then locals
            else fun id => if id == tmp then none else locals id)
          s.locals
        Sem.setState { s with locals := locals' }
  | .terminator _, _ =>
      Sem.throwTypeError "body instruction produced a terminator"

/-- Step through a single basic block.
    Execute all body instructions, then the terminator.
    Returns the step result (Continue/Ret/Stuck). -/
def stepBlock (block : BasicBlock) (args : List Value) : Sem StepResult := do
  -- Bind block parameters
  bindBlockParams block.params args
  -- Execute body instructions
  for inst in block.body do
    let instResult ← stepInst inst
    match instResult with
    | .value _ => pure ()
    | .values _ => pure ()
    | .terminator (.CallReq _ _) =>
      Sem.throwUnsupported .interproceduralCall
        "stepBlock: inter-procedural call in block body requires function table context"
    | .terminator (.CallIndirectReq _ _ _) =>
      Sem.throwUnsupported .interproceduralIndirectCall
        "stepBlock: inter-procedural indirect call in block body requires function table context"
    | .terminator (.SeqMapReq _ _) =>
      Sem.throwUnsupported .interproceduralCall
        "stepBlock: SeqMap element application in block body requires function table context"
    | .terminator _ =>
      Sem.throwTypeError "body instruction produced a terminator"
  -- Execute terminator
  let result ← stepInst block.terminator
  match result with
  | .terminator sr => pure sr
  | .value _       => Sem.throwTypeError "basic block does not end with a terminator"
  | .values _      => Sem.throwTypeError "basic block does not end with a terminator"

/-- Multi-step evaluation with fuel-based termination.
    Executes blocks until Return, Stuck, or fuel exhaustion.

    `fuel` ensures termination for Lean's kernel. For terminating
    programs, sufficient fuel always exists. -/
def stepN (fuel : Nat) (cfg : CFG) (pc : BlockId) (args : List Value)
    : Sem (List Value) := do
  match fuel with
  | 0 => throw SemError.outOfFuel
  | fuel + 1 =>
    match cfg pc with
    | none => Sem.throwTypeError s!"undefined block: {repr pc}"
    | some block => do
      let result ← stepBlock block args
      match result with
      | .Ret values     => pure values
      | .Stuck          => Sem.throwUB "reached unreachable"
      | .Continue nextPc nextArgs => stepN fuel cfg nextPc nextArgs
      -- Call requests: the evaluator would need function tables to
      -- dispatch these. For now, signal that inter-procedural
      -- evaluation is not yet supported at this level.
      | .CallReq _ _ =>
        Sem.throwUnsupported .interproceduralCall
          "stepN: inter-procedural call requires function table context"
      | .CallIndirectReq _ _ _ =>
        Sem.throwUnsupported .interproceduralIndirectCall
          "stepN: inter-procedural indirect call requires function table context"
      | .InvokeReq _ _ _ _ _ =>
        Sem.throwUnsupported .interproceduralCall
          "stepN: invoke requires function table context"
      | .InvokeIndirectReq _ _ _ _ _ _ =>
        Sem.throwUnsupported .interproceduralIndirectCall
          "stepN: indirect invoke requires function table context"
      | .SeqMapReq _ _ =>
        Sem.throwUnsupported .interproceduralCall
          "stepN: SeqMap element application requires function table context"

/-- Evaluate a function from its entry block.
    Convenience wrapper around stepN with a default fuel limit. -/
def evalFunction (cfg : CFG) (entryBlock : BlockId) (args : List Value)
    (fuel : Nat := 10000) : Sem (List Value) :=
  stepN fuel cfg entryBlock args

/-!
## Contextual Interprocedural Evaluation

`stepN` is the historical single-function evaluator and intentionally keeps
its fail-closed behavior for calls.  `stepNWithContext` is the executable
interprocedural entry point: it carries function and function-pointer tables,
sets up a fresh local frame for callees, restores the caller frame on return,
and bounds calls by both block fuel and call depth.
-/

/-- Executable function body carried by an evaluator context. -/
structure EvalFunction where
  /-- Actual decoded identity; absent in the context-free manual body API. -/
  sourceId : Option FuncId := none
  body       : FuncBody
  cfg        : CFG
  entryBlock : BlockId
  callingConv : CallingConv := .C
  /-- Original function-local declarations, derived before execution. -/
  localTypes : Option LocalTypeTable := none

def EvalFunction.header (function : EvalFunction) : FunctionHeader :=
  { signature :=
      { params := function.body.paramTys
        returns := function.body.returnTys
        isVararg := function.body.isVararg
        abi := function.body.abi }
    callingConv := function.callingConv }

/-- A module-level global's definition (type + optional initializer), carried by
    the evaluator context so `GlobalAddr` can reserve the global's TRUE byte size
    and write its initializer with full storage fidelity. Mirrors Rust `Global`. -/
structure GlobalDef where
  ty          : Ty
  initializer : Option Constant
  /-- The DECLARED over-alignment (`Global.align`), if any. -/
  align       : Option Nat := none

/-- GlobalId -> definition lookup, mirroring `Module.globals`. -/
def GlobalsTable := GlobalId → Option GlobalDef

/-- Evaluator context for interprocedural execution. -/
structure EvalContext where
  /-- Selected from the module target before any instruction executes. -/
  byteModel : ByteModel := .le64
  /-- One finite source carrier supplies both declaration lookup and nominal
      value containment. A context cannot forge an unrelated presence result. -/
  valueSource : FunctionItemPresence.Prepared := FunctionItemPresence.prepare {}
  /-- Original source layouts and statically prepared image roots. Actual
      decoded modules always install this; manual scalar contexts may omit it. -/
  memoryService : Option AggregateMemory.Service := none
  /-- Active function's declarations; calls replace this lexical context. -/
  localTypes : Option LocalTypeTable := none
  functionReturnTypes : Option (List Ty) := none
  currentFunction : Option FuncId := none
  functions    : FuncId -> Option EvalFunction
  /-- Complete original headers, including declarations and lazily refused
      bodies. A known malformed header is an error, not an absent entry. -/
  functionHeaders : FuncId → Option (Except SemError FunctionHeader) := fun _ => none
  funcPtrs     : FuncPtrTable
  /-- Original source order for memory code words, independent of executable
      bodies and call depth. No table is inferred from `functions`. -/
  functionOrder : FunctionAddressOrder := none
  funcTys      : FuncTyTable
  maxCallDepth : Nat
  /-- Module globals, enabling full-fidelity `GlobalAddr` (real size + initializer)
      under `stepNWithContext`. The bare `stepInst` keeps the honest size-1
      partial when no module context is available. -/
  globalsTable : GlobalsTable
  /-- WS2.19: the functions the module DECLARES without a body. A call that
      resolves to one is `unsupported.interprocedural_call` (the reference
      interpreter's `UnsupportedCall`: a bodyless declaration is not
      executable in-format, WS2.12), not the `Call: undefined function` type
      error a function absent from the module altogether gets. Defaults to
      "nothing is declared", so every existing context is unchanged. -/
  declared : FuncId → Bool := fun _ => false
  /-- A decoded target outside the executable fragment is refused only when
      called. Passing an unused function value must not evaluate its body. -/
  functionErrors : FuncId → Option SemError := fun _ => none
  /-- Producer tuple layouts retain original source TyIds and field order. -/
  tupleLayouts : List TupleLayoutDescriptor := []
  /-- Amendment D (§20): the module drop-glue table, as a lookup from the
      dropped type to its glue (`Module.drop_glue`; derived `Ty` equality,
      the tuple-layout rule). A drop at a type the table maps RESOLVES to a
      call of the glue (`resolveDrop`); at any other type it is UNRESOLVED and
      the bare `stepInst` refuses it (`unsupported.destructor`). Defaults to
      "every drop unresolved", so every existing context is unchanged. -/
  dropGlue : Ty → Option FuncId := fun _ => none

namespace EvalContext

def types (ctx : EvalContext) : TyId → Option Ty := ctx.valueSource.ty
def structs (ctx : EvalContext) : StructId → Option StructDef := ctx.valueSource.firstStructDef
def enums (ctx : EvalContext) : EnumId → Option EnumDef := ctx.valueSource.firstEnumDef
def records (ctx : EvalContext) : RecordId → Option RecordDef := ctx.valueSource.firstRecordDef
def closures (ctx : EvalContext) : ClosureTyId → Option ClosureTy := ctx.valueSource.closureTy

/-- Static item declarations share the finite source authority used by frame
    origins and value containment; metadata cannot supply a runtime unwind. -/
def functionItems (ctx : EvalContext) : FuncId → Option (Except String FunctionItemHeader) :=
  ctx.valueSource.functionItem

/-- Existing canonical leaf layouts/codecs depend only on the byte model
    and function namespace. Producer aggregate metadata cannot change them.
    Descriptor-dependent shapes use the service without a legacy fallback. -/
def memoryServiceFor (ctx : EvalContext) (ty : Ty) : Option AggregateMemory.Service :=
  if ty.hasCanonicalMemoryLayout then none else ctx.memoryService

def memoryLayout (ctx : EvalContext) (ty : Ty) : Except SemError MemoryTypeLayout :=
  match ctx.memoryServiceFor ty with
  | some service => AggregateMemory.layoutQuery service ctx.byteModel ty
  | none => scalarMemoryLayout ctx.byteModel ty

/-- Canonical leaves use the original held-value arithmetic for every
    context, including arbitrary aggregate services and every error path. -/
theorem semGEPUsing_canonical (ctx : EvalContext) (reader : IntegerOperandReader)
    (ty : Ty) (base : ValueId) (indices : List ValueId)
    (canonical : ty.hasCanonicalMemoryLayout = true) :
    semGEPUsing ctx.memoryLayout reader ty base indices ctx.byteModel =
      semGEPUsing (scalarMemoryLayout ctx.byteModel) reader ty base indices ctx.byteModel := by
  simp only [semGEPUsing, semGEPValuesUsing, gepOffsetUsing,
    memoryLayout, memoryServiceFor, canonical, if_true]

/-- A callee gets its own declarations. The caller retains its lexical context
    for the continuation, just as its local values are restored from a frame. -/
def forFunction (ctx : EvalContext) (function : EvalFunction) : EvalContext :=
  { ctx with
    localTypes := function.localTypes
    currentFunction := function.sourceId
    functionReturnTypes := some function.body.returnTys }

/-- Interpret a typed integer without imposing a consumer-specific sign guard.
    Poison is inspected before metadata, including in an untyped context. -/
def integerOperand (ctx : EvalContext) (id : ValueId) (value : Value) :
    Except SemError Int := do
  if value.isPoison || value.isUninit then
    throw (.ub "typed integer: use of an uninitialized operand")
  let table ← match ctx.localTypes with
    | some table => pure table
    | none => throw (.unsupported .ssaTypeTable "original function SSA declarations are unavailable")
  let ty ← match table id with
    | some ty => pure ty
    | none => throw (.typeError "SSA types: value has no declaration")
  typedIntegerValue ctx.byteModel ty value

/-- General runtime integer use includes Char's raw unsigned carrier. The
    instruction-specific validator still controls which source operands admit
    it; Unicode validity is checked at SSA binding, not recursively here. -/
def carrierIntegerOperand (ctx : EvalContext) (id : ValueId) (value : Value) :
    Except SemError Int := do
  if value.isPoison || value.isUninit then
    throw (.ub "integer operand: use of an uninitialized value")
  let table ← match ctx.localTypes with
    | some table => pure table
    | none => throw (.unsupported .ssaTypeTable "original function SSA declarations are unavailable")
  let ty ← match table id with
    | some ty => pure ty
    | none => throw (.typeError "SSA types: value has no declaration")
  typedIntegerCarrierValue ctx.byteModel ty value

def elementIndex (ctx : EvalContext) (id : ValueId) (value : Value) : Sem Nat := do
  let checked := do
    let integer ← ctx.integerOperand id value
    nonnegativeElementIndex integer
  match checked with
  | .ok index => pure index
  | .error error => throw error

/-- A manual context's fallback uses real callee header fields, never a guessed
    signature or an executable body's inferred return value. -/
def resultTypeHeaders (ctx : EvalContext) (id : FuncId) : Option FuncTyDef :=
  (ctx.functions id).map (fun function =>
    { params := function.body.paramTys, returns := function.body.returnTys,
      isVararg := function.body.isVararg, abi := function.body.abi })

def instructionResultTypes (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (produced : Nat) : Except SemError (List Ty) :=
  ssaInstructionResultTypes ctx.localTypes ctx.resultTypeHeaders ctx.funcTys inst dests produced

def checkInstructionResults (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) : Sem Unit := do
  let types ← match ctx.instructionResultTypes inst dests values.length with
    | .ok types => pure types
    | .error error => throw error
  match checkSSACharValues types values with
  | .ok () => pure ()
  | .error error => throw error

/-- Call/invoke results already have their actual ordered values. Keep the
    existing arity refusal before checking the source declaration association. -/
def bindCallResults (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) : Sem Unit := do
  if dests.length != values.length then bindResultDests dests values
  else
    ctx.checkInstructionResults inst dests values
    bindResultDests dests values

trustIrDenseMatch
/-- Check the values the instruction actually returned, before the existing
    destination binding/temporary retirement. An absent manual destination row
    keeps its historical single fresh-result convention; a populated original
    table still requires every source destination and its exact type. -/
def bindInstructionResults (ctx : EvalContext) (inst : Inst) :
    InstrResult → List ValueId → Sem Unit
  | .value none, [] => do
    ctx.checkInstructionResults inst [] []
    bindInstrResultDests (.value none) []
  | .value (some result), [] => do
    let value ← Sem.lookupValue result
    ctx.checkInstructionResults inst [] [value]
    bindInstrResultDests (.value (some result)) []
  | .value (some result), [dest] => do
    let value ← Sem.lookupValue result
    ctx.checkInstructionResults inst [dest] [value]
    bindInstrResultDests (.value (some result)) [dest]
  | .values results, dests =>
    if dests.length != results.length then bindInstrResultDests (.values results) dests
    else do
      let values ← results.mapM Sem.lookupValue
      ctx.checkInstructionResults inst dests values
      bindInstrResultDests (.values results) dests
  | result, dests => bindInstrResultDests result dests

trustIrDenseMatch
/-- Amendment D (`docs/SPEC_RATIFICATIONS.md` §20 rule 3, NORMATIVE): a
    resolved `drop T, %p` IS `call glue(%p)` and a resolved `drop_invoke T,
    %p to bbN(args) unwind bbM` IS `invoke glue(%p) to bbN(args) unwind bbM`.
    Resolution happens BEFORE dispatch, so a resolved drop literally runs the
    existing `Call` / `Invoke` rules; an unresolved one is left as is, and
    the bare `stepInst` refuses it. Every other instruction is unchanged. -/
def resolveDrop (ctx : EvalContext) : Inst → Inst
  | .Drop ty p =>
    match ctx.dropGlue ty with
    | some g => .Call g [p]
    | none => .Drop ty p
  | .DropInvoke ty p nd na ud =>
    match ctx.dropGlue ty with
    | some g => .Invoke g [p] nd na ud
    | none => .DropInvoke ty p nd na ud
  | i => i

#trustIrAxiomsExact resolveDrop == []

/-- A block with every drop resolved (`resolveDrop` on each body instruction
    and on the terminator). -/
def resolveBlock (ctx : EvalContext) (b : BasicBlock) : BasicBlock :=
  { b with body := b.body.map ctx.resolveDrop, terminator := ctx.resolveDrop b.terminator }

/-- A CFG with every drop resolved: the producer-side "resolution rewrite"
    (Drop → Call, DropInvoke → Invoke). `stepNWithContext_resolveDrops`
    (`Proofs/DropProps.lean`) proves running it IS running the original. -/
def resolveCfg (ctx : EvalContext) (cfg : CFG) : CFG :=
  fun pc => (cfg pc).map ctx.resolveBlock

/-- Empty context used by tests that want fail-closed call behavior. -/
def empty : EvalContext :=
  { functions := fun _ => none
    funcPtrs := fun _ => none
    funcTys := fun _ => none
    maxCallDepth := 0
    globalsTable := fun _ => none }

end EvalContext

/-- Check that a returned value list matches the declared result arity. -/
def checkReturnArity (values : List Value) (returnTys : List Ty) :
    Except String Unit :=
  if values.length == returnTys.length then .ok ()
  else .error "return arity mismatch"

/-- Check that an indirect-call signature denotes the resolved callee. -/
def checkIndirectSignature (sig : FuncTyDef) (body : FuncBody) :
    Except String Unit :=
  if sig.abi.isSome || body.abi.isSome then
    .error "typed ABI transport semantics unsupported"
  else if closureTyListEq sig.params body.paramTys &&
      closureTyListEq sig.returns body.returnTys && !sig.isVararg && !body.isVararg then
    .ok ()
  else
    .error "indirect call signature mismatch"

/-- Retaining ABI claims must not imply that value-only execution checks
    register/stack transport. Refuse every typed descriptor until those
    semantics are implemented, including manually constructed contexts. -/
def requireUntypedAbi (abi : Option SignatureAbi) : Sem Unit :=
  if abi.isSome then
    Sem.throwUnsupported .interproceduralCall "typed ABI transport semantics unsupported"
  else pure ()

@[simp] theorem requireUntypedAbi_none : requireUntypedAbi none = pure () := rfl

trustIrDenseMatch
/-- Resolve a typed function value without fabricating a native address.
    The value's signature id and the actual target's complete logical signature
    are separate checks. A declaration needs a host model, which this context
    does not install; a typed ABI is not value-only execution authority. -/
def functionCall (ctx : EvalContext) (held : FuncTyId) (target : FuncId)
    (sig : FuncTyId) : Except SemError FuncId := do
  if held != sig then throw (.typeError "CallIndirect: function value signature id mismatch")
  let expected ← match ctx.funcTys sig with
    | some s => pure s
    | none => throw (.typeError "CallIndirect: undefined function type")
  let callee ← match ctx.functions target with
    | some f => pure f
    | none =>
      if let some e := ctx.functionErrors target then throw e
      if ctx.declared target then
        throw (.unsupported .interproceduralCall "CallIndirect: callee is a bodyless declaration")
      else throw (.typeError "CallIndirect: undefined function")
  if expected.abi.isSome || callee.body.abi.isSome then
    throw (.unsupported .interproceduralCall "typed ABI transport semantics unsupported")
  match checkIndirectSignature expected callee.body with
  | .ok () => pure target
  | .error msg => throw (.typeError (trustIrStringAppend "CallIndirect: " msg))

#trustIrAxiomsExact TrustIr.functionCall == []

/-- Apply signature-only resolution and inspect the resolved target's actual
    convention before entering it. The repeated target lookup is pure. -/
def functionCallWithConvention (ctx : EvalContext) (held : FuncTyId) (target : FuncId)
    (sig : FuncTyId) (convention : CallingConv) : Except SemError FuncId :=
  match functionCall ctx held target sig with
  | .error error => .error error
  | .ok resolved =>
    match ctx.functions resolved with
    | none => .error (.typeError "CallIndirect: undefined function")
    | some callee =>
      if callee.callingConv != convention then
        .error (.typeError "CallIndirect: calling convention mismatch")
      else .ok resolved

/-- Item construction inspects the unique original header, never its body. -/
def functionItemDeclaration (ctx : EvalContext) (target : FuncId) :
    Except SemError FunctionItemHeader :=
  match ctx.functionItems target with
  | some (.ok header) => .ok header
  | some (.error message) => .error (.typeError message)
  | none => .error (.typeError "FnItem: original function declaration is absent")

/-- Static declaration failures cannot carry a runtime unwind state. This is
    a consequence of the finite metadata carrier, with no context premise. -/
theorem functionItemDeclaration_error_is_typeError (ctx : EvalContext) (target : FuncId)
    (error : SemError) (failed : functionItemDeclaration ctx target = .error error) :
    ∃ message, error = .typeError message := by
  unfold functionItemDeclaration at failed
  cases found : ctx.functionItems target with
  | none =>
    rw [found] at failed
    cases failed
    exact ⟨"FnItem: original function declaration is absent", rfl⟩
  | some declaration =>
    rw [found] at failed
    cases declaration with
    | error message =>
      cases failed
      exact ⟨message, rfl⟩
    | ok header => cases failed

/-- Application retains nominal identity, original signature id and calling
    convention before entering the ordinary function-call machinery. -/
def functionItemCall (ctx : EvalContext) (target : FuncId) (sig : FuncTyId)
    (convention : CallingConv) : Except SemError FuncId := do
  let declaration ← functionItemDeclaration ctx target
  if declaration.header.callingConv != convention then
    throw (.typeError "CallIndirect: function item calling convention mismatch")
  if declaration.signatureId != sig then
    throw (.typeError "CallIndirect: function item signature id mismatch")
  let expected ← match ctx.funcTys sig with
    | some expected => pure expected
    | none => throw (.typeError "CallIndirect: undefined function type")
  if expected.abi.isSome || declaration.header.signature.abi.isSome then
    throw (.unsupported .interproceduralCall "typed ABI transport semantics unsupported")
  if !(closureTyListEq expected.params declaration.header.signature.params) ||
      !(closureTyListEq expected.returns declaration.header.signature.returns) ||
      expected.isVararg || declaration.header.signature.isVararg then
    throw (.typeError "CallIndirect: function item signature mismatch")
  pure target

/-- A runtime item cannot replace a pointer or a differently declared item.
    Existing pointer/closure declarations keep their own validation path. -/
def checkFunctionItemCalleeType (ctx : EvalContext) (operand : ValueId)
    (value : Value) : Except SemError Unit :=
  match ctx.localTypes.bind (fun table => table operand), value with
  | some (.FnItem expected), .fnItem held =>
    if expected == held then .ok ()
    else .error (.typeError "CallIndirect: function item identity differs from its SSA declaration")
  | some (.FnItem _), _ | _, .fnItem _ =>
    .error (.typeError "CallIndirect: nominal function item declaration is absent or mismatched")
  | _, _ => .ok ()

/-- The body stays lazy until depth and argument inspection have completed. -/
def resolveFunctionItemBody (ctx : EvalContext) (target : FuncId) :
    Except SemError EvalFunction :=
  match ctx.functions target with
  | some function => .ok function
  | none =>
    match ctx.functionErrors target with
    | some error => .error error
    | none =>
      if ctx.declared target then
        .error (.unsupported .interproceduralCall "CallIndirect: callee is a bodyless declaration")
      else .error (.typeError "CallIndirect: undefined function")

/-- Resolve a nominal closure's code contract. A missing table or an ABI
    transport outside this evaluator's model is an explicit refusal. This
    check is shared by construction, updates and application. -/
def closureContract (ctx : EvalContext) (ty : ClosureTyId) (fn : FuncId) :
    Except SemError (ClosureTy × FuncTyDef × EvalFunction) := do
  let defn ← match ctx.closures ty with
    | some d => pure d
    | none => throw (.unsupported .closureDefTable "closure definition is absent")
  let apparent ← match ctx.funcTys defn.func with
    | some s => pure s
    | none => throw (.typeError "closure apparent signature is absent")
  let target ← match ctx.functions fn with
    | some f => pure f
    | none =>
      if ctx.declared fn then
        throw (.unsupported .interproceduralCall "closure target is a bodyless declaration")
      else throw (.typeError "closure target is absent")
  if apparent.abi.isSome || target.body.abi.isSome then
    throw (.unsupported .interproceduralCall "typed ABI transport semantics unsupported")
  if apparent.isVararg || target.body.isVararg ||
      !(closureTyListEq target.body.paramTys (defn.captures ++ apparent.params)) ||
      !(closureTyListEq target.body.returnTys apparent.returns) || target.body.abi != apparent.abi then
    throw (.typeError "closure target does not have captures ++ apparent signature")
  pure (defn, apparent, target)

/-- Mirror of Rust `EnumDef::effective_discriminants`: an explicit
    discriminant where one is given, otherwise the predecessor plus one
    (starting at 0); `none` on a repeated value, and — as Rust's
    `checked_add` — `none` when an implicit successor would pass
    `i128::MAX`. -/
def enumEffectiveDiscriminants (d : EnumDef) : Option (List Int) :=
  -- One entry per variant: its explicit discriminant, if the table has one.
  let explicit : List (Option Int) :=
    (List.range d.variants.length).map (fun i => ((trustIrListGet? d.discriminants i)).join)
  let rec go : List (Option Int) → Option Int → List Int → Option (List Int)
    | [], _, acc => some acc
    | given :: rest, next, acc =>
      match given.orElse (fun _ => next) with
      | none => none
      | some value =>
        if acc.contains value then none
        else go rest (if value + 1 < 2 ^ 127 then some (value + 1) else none) (acc ++ [value])
  go explicit (some 0) []

/-- Does a discriminant fit the tag representation? Mirror of Rust
    `EnumTagRepr::fits`. -/
def EnumTagRepr.fits : EnumTagRepr → Int → Bool
  | .u8, v => 0 ≤ v && v < 2 ^ 8
  | .u16, v => 0 ≤ v && v < 2 ^ 16
  | .u32, v => 0 ≤ v && v < 2 ^ 32
  | .u64, v => 0 ≤ v && v < 2 ^ 64
  | .u128, v => 0 ≤ v && v < 2 ^ 127
  | .i8, v => -(2 ^ 7) ≤ v && v < 2 ^ 7
  | .i16, v => -(2 ^ 15) ≤ v && v < 2 ^ 15
  | .i32, v => -(2 ^ 31) ≤ v && v < 2 ^ 31
  | .i64, v => -(2 ^ 63) ≤ v && v < 2 ^ 63
  | .i128, v => -(2 ^ 127) ≤ v && v < 2 ^ 127

def EnumTagRepr.bitWidth : EnumTagRepr → Nat
  | .u8 | .i8 => 8
  | .u16 | .i16 => 16
  | .u32 | .i32 => 32
  | .u64 | .i64 => 64
  | .u128 | .i128 => 128

/-- Logical type of the enum's in-register tag lane. Concrete memory
    encodings do not change this canonical value-level representation. -/
def EnumTagRepr.ty : EnumTagRepr → Ty
  | .u8 => .U8 | .u16 => .U16 | .u32 => .U32 | .u64 => .U64 | .u128 => .U128
  | .i8 => .I8 | .i16 => .I16 | .i32 => .I32 | .i64 => .I64 | .i128 => .I128

/-- Mirror of Rust `EnumTagRepr::smallest_for`: the narrowest unsigned (all
    discriminants non-negative) or signed representation holding both
    extremes, capped at 64 bits. -/
def enumSmallestTagRepr (min max : Int) : Option EnumTagRepr :=
  let candidates : List EnumTagRepr :=
    if 0 ≤ min then [.u8, .u16, .u32, .u64] else [.i8, .i16, .i32, .i64]
  candidates.find? (fun r => r.fits min && r.fits max)

/-- Mirror of Rust `EnumDef::canonical_tag_repr`: the explicit `tagRepr` hint
    when present (`none` unless every effective discriminant fits it),
    otherwise the smallest width; `none` for an uninhabited or unresolvable
    enum. -/
def enumCanonicalTagRepr (d : EnumDef) : Option EnumTagRepr := do
  if d.variants.isEmpty then none
  let discs ← enumEffectiveDiscriminants d
  match d.tagRepr with
  | some hint => if discs.all hint.fits then some hint else none
  | none =>
    let min ← discs.foldl (fun acc v => some (match acc with | some a => if v < a then v else a | none => v)) none
    let max ← discs.foldl (fun acc v => some (match acc with | some a => if a < v then v else a | none => v)) none
    enumSmallestTagRepr min max

/-- Position of the first element equal to `x`, if any. -/
def listIndexOf? (xs : List Int) (x : Int) : Option Nat :=
  let rec go : List Int → Nat → Option Nat
    | [], _ => none
    | y :: ys, i => if y == x then some i else go ys (i + 1)
  go xs 0

/-- Complete immutable declaration equality, matching the native origin
    check; source names and raw type identities are not erased. -/
def bindingFrameDeclarationEq (left right : BindingFrameDef) : Bool :=
  left.id == right.id && left.name == right.name &&
    left.slots.length == right.slots.length &&
    (left.slots.zip right.slots).all (fun (a, b) => a.name == b.name && closureTyEq a.ty b.ty)

/-- Authenticate a frame snapshot against the original finite declaration
    table, including exact slot census. Ptr is only the SSA transport type. -/
def bindingFrameTypes (ctx : EvalContext) (value : Value) : Except SemError (List Ty) := do
  match value with
  | .sourceFrame _ origin declaration values =>
    let original ← match ctx.valueSource.bindingFrame origin declaration.id with
      | some original => pure original
      | none => throw (.typeError "binding frame: original declaration is absent or ambiguous")
    if !(bindingFrameDeclarationEq original declaration) then
      throw (.typeError "binding frame: original declaration differs from held origin")
    if original.slots.length != values.length then
      throw (.typeError "binding frame: slot census differs from original declaration")
    pure (original.slots.map (·.ty))
  | _ => throw (.typeError "binding frame: authenticated source origin is absent")

private def distinctFieldNames : List String → Bool
  | [] => true
  | name :: rest => !rest.contains name && distinctFieldNames rest

/-- Check only nominal item lanes against their declared source positions.
    Unwritten aggregate lanes remain transport markers. Stored array seeds
    are visited once; pointer pointees and inactive enum fields are not read.
    One complete declaration-directed check layer. The recursion parameter
    is explicit so the match compiler does not duplicate its fuel iterator. -/
def checkFunctionItemLayer (ctx : EvalContext)
    (recurse : Ty → Value → Except SemError Unit) (ty : Ty) (value : Value) :
    Except SemError Unit := do
    if value.isUninit then return ()
    let relevant := ctx.valueSource.hasFnItem ty
    let fields (types : List Ty) (values : List Value) : Except SemError Unit :=
      do
      if relevant && types.length != values.length then
        throw (.typeError "FnItem: container field census differs from its declaration")
      ((types ++ List.replicate values.length Ty.Error).zip values).forM
        (fun (ty, value) => recurse ty value)
    match ty, value with
    | .Ptr, .sourceFrame _ _ _ values =>
      let types ← bindingFrameTypes ctx value
      (types.zip values).forM (fun (ty, value) => recurse ty value)
    | _, .sourceFrame _ _ _ _ =>
      throw (.typeError "binding frame: runtime handle requires its Ptr transport type")
    | .FnItem expected, .fnItem held =>
      if expected != held then throw (.typeError "FnItem: runtime identity differs from declared type")
      let _ ← functionItemDeclaration ctx expected
      pure ()
    | .FnItem _, _ | _, .fnItem _ =>
      throw (.typeError "FnItem: runtime kind differs from declared type")
    | .Tuple types, .aggregate values => fields types values
    | .Struct id, .aggregate values =>
      fields (((ctx.structs id).map (fun definition => definition.fields.map (·.ty))).getD []) values
    | .Enum id, .aggregate values =>
      match values with
      | [] =>
        if relevant then throw (.typeError "FnItem: enum tag is absent") else pure ()
      | tag :: values => do
        let _ ← recurse .Error tag
        let types := do
          let definition ← ctx.enums id
          let repr ← enumCanonicalTagRepr definition
          let discriminants ← enumEffectiveDiscriminants definition
          let raw ← match tag with | .int width raw => if width == repr.bitWidth then some raw else none | _ => none
          let tag := if SourceLayout.tagSigned repr then toSigned raw repr.bitWidth else truncateUnsigned raw repr.bitWidth
          let selected ← listIndexOf? discriminants tag
          pure (← trustIrListGet? definition.variants selected).fields
        if relevant && types.isNone then
          throw (.typeError "FnItem: enum tag does not select a declared payload")
        fields (types.getD []) values
    | .Array element count, .array values =>
      if relevant && values.size != count then
        throw (.typeError "FnItem: array length differs from its declaration")
      values.tree.checkStored (recurse ((ctx.types element).getD .Error))
    | .Vector count element, .vector values =>
      if relevant && values.length != count then
        throw (.typeError "FnItem: vector length differs from its declaration")
      values.forM (recurse element)
    | .Sequence element, .sequence values | .Set element _, .set values =>
      values.forM (recurse ((ctx.types element).getD .Error))
    | .Record id, .record values =>
      if relevant then
        let declared ← match ctx.records id with
          | some definition => pure definition.fields
          | none => throw (.typeError "FnItem: record declaration is absent")
        if declared.length != values.length ||
            !distinctFieldNames (declared.map (·.name)) ||
            !distinctFieldNames (values.map (·.fst)) then
          throw (.typeError "FnItem: record field census differs from its declaration")
      values.forM fun (name, value) => do
        let field := (ctx.records id).bind (fun definition => definition.fields.find? (fun field => field.name == name))
        if relevant && field.isNone then
          throw (.typeError "FnItem: record field is not declared")
        recurse ((field.map (·.ty)).getD .Error) value
    | .Closure id, .typedClosure held _ captures =>
      if relevant && held != id then
        throw (.typeError "FnItem: closure identity differs from its declaration")
      fields (((ctx.closures id).map (·.captures)).getD []) captures
    | .Closure id, .closure _ captures =>
      fields (((ctx.closures id).map (·.captures)).getD []) captures
    | .FatPtr kind, .fatPtr _ _ metadata =>
      recurse (kind.metadataTyAtModel ctx.byteModel) metadata
    | _, _ =>
      if relevant then throw (.typeError "FnItem: container runtime kind differs from its declaration")
      match value with
      | .aggregate values | .vector values | .sequence values | .set values
      | .closure _ values | .typedClosure _ _ values | .frame _ values => fields [] values
      | .array values => values.tree.checkStored (recurse .Error)
      | .record values => values.forM (fun (_, value) => recurse .Error value)
      | _ => pure ()

/-- Iterate the same layer along the actual stored value depth. Nominal
    containment itself comes from the complete finite source fixed point. -/
def checkFunctionItemLanes (ctx : EvalContext) (fuel : Nat) (ty : Ty) (value : Value) :
    Except SemError Unit :=
  match fuel with
  | 0 =>
    match ty, value with
    | .FnItem _, _ | _, .fnItem _ =>
      .error (.typeError "FnItem: value nesting does not match its declaration")
    | _, .sourceFrame _ _ _ _ =>
      .error (.typeError "binding frame: value nesting does not match its declaration")
    | _, _ => .ok ()
  | fuel + 1 => checkFunctionItemLayer ctx (checkFunctionItemLanes ctx fuel) ty value

def checkFunctionItemValues (ctx : EvalContext) (types : List Ty) (values : List Value) :
    Except SemError Unit :=
  (types.zip values).forM (fun (ty, value) => checkFunctionItemLanes ctx (value.depth + 1) ty value)

/-- Runtime value/type check for closure boundaries. References retain their
    actual pointer/provenance; this never dereferences or reconstructs them.
    Integer signedness remains instruction-level in the legacy value model;
    float membership, container lanes, record labels and active enum payloads
    are checked at their declared types. Unwritten tuple/struct fields are
    transport lanes, not inspected values: they move with the enclosing
    aggregate and fault only when projected. Whole poison/unwritten captures
    still refuse. Shapes without a modeled value rule refuse. -/
def checkClosureValueAt (ctx : EvalContext) (fuel : Nat) (ty : Ty) (v : Value) :
    Except SemError Unit :=
  match fuel with
  | 0 => .error (.unsupported .closureDefTable "closure value structural budget exhausted")
  | fuel + 1 => do
    let mismatch := Except.error (SemError.typeError "closure value does not match its declared type")
    if v.isPoison || v.isUninit then
      throw (.ub "closure boundary: uninitialized value")
    match ty, v with
    | .Bool, .bool _ => pure ()
    | .Char, .int w n =>
      if w != 32 then mismatch
      else if n < 0 || !(decide (validChar n.toNat)) then
        throw (.ub "closure boundary: invalid Unicode scalar value")
      else pure ()
    | t, .int w n =>
      if !(t.isInteger && t.bitWidthFor ctx.byteModel == some w) then mismatch
      else if 0 ≤ n && n < (2 : Int) ^ w then pure () else mismatch
    | .F16, .float f | .F32, .float f | .F64, .float f => checkFloatAt ty f
    | .Ptr, .ptr _ _ | .Ptr, .nullPtr
    | .Ref _, .ptr _ _ | .Ref _, .nullPtr
    | .RefMut _, .ptr _ _ | .RefMut _, .nullPtr
    | .PtrConst _, .ptr _ _ | .PtrConst _, .nullPtr
    | .PtrMut _, .ptr _ _ | .PtrMut _, .nullPtr => pure ()
    | .Unit, .aggregate [] => pure ()
    | .FnItem expected, .fnItem held =>
      if expected != held then mismatch
      else do let _ ← functionItemDeclaration ctx expected; pure ()
    | .Func sig, .fnDef held _ => if sig == held then pure () else mismatch
    | .Func _, .nullPtr => pure ()
    | .Tuple ts, .aggregate vs =>
      if ts.length != vs.length then mismatch
      else (ts.zip vs).forM (fun (t, x) =>
        if x.isUninit then pure () else checkClosureValueAt ctx fuel t x)
    | .Struct sid, .aggregate vs =>
      let d ← match ctx.structs sid with
        | some d => pure d
        | none => throw (.unsupported .enumDefTable "closure capture struct definition is absent")
      if d.fields.length != vs.length then mismatch
      else (d.fields.zip vs).forM (fun (f, x) =>
        if x.isUninit then pure () else checkClosureValueAt ctx fuel f.ty x)
    | .Array tid n, .array vs =>
      let t ← match ctx.types tid with
        | some t => pure t
        | none => throw (.unsupported .enumDefTable "closure capture element type is absent")
      if n != vs.size then mismatch
      else vs.tree.checkStored (checkClosureValueAt ctx fuel t)
    | .Vector n elemTy, .vector vs =>
      if n == 0 || n != vs.length then mismatch
      else vs.forM (checkClosureValueAt ctx fuel elemTy)
    | .Sequence tid, .sequence vs | .Set tid _, .set vs =>
      let elemTy ← match ctx.types tid with
        | some t => pure t
        | none => throw (.unsupported .enumDefTable "closure capture element type is absent")
      vs.forM (checkClosureValueAt ctx fuel elemTy)
    | .Record rid, .record fields =>
      let d ← match ctx.records rid with
        | some d => pure d
        | none => throw (.unsupported .enumDefTable "closure capture record definition is absent")
      if d.fields.length != fields.length then mismatch
      else (d.fields.zip fields).forM (fun (declared, (name, x)) => do
        if name != declared.name then mismatch
        else checkClosureValueAt ctx fuel declared.ty x)
    | .Enum eid, .aggregate vs =>
      let d ← match ctx.enums eid with
        | some d => pure d
        | none => throw (.unsupported .enumDefTable "closure capture enum definition is absent")
      let discs ← match enumEffectiveDiscriminants d with
        | some ds => pure ds
        | none => throw (.typeError "closure capture enum discriminants are invalid")
      let repr ← match enumCanonicalTagRepr d with
        | some r => pure r
        | none => throw (.typeError "closure capture enum tag representation is invalid")
      match vs with
      | [] => mismatch
      | tagValue :: payload => do
        -- The tag is a real child value, so its membership/poison checks use
        -- the same decremented structural fuel as every payload child.
        checkClosureValueAt ctx fuel repr.ty tagValue
        match tagValue with
        | .int _ tag => do
          -- Signed discriminants are carried by their canonical-width residue.
          -- Use the trusted declared width, never an unchecked runtime width.
          let residues := discs.map (fun disc => disc % ((2 : Int) ^ repr.bitWidth))
          let index ← match listIndexOf? residues tag with
            | some i => pure i
            | none => throw (.typeError "closure capture enum tag names no variant")
          let variant ← match (trustIrListGet? d.variants index) with
            | some variant => pure variant
            | none => throw (.typeError "closure capture enum tag names no variant")
          if variant.fields.length != payload.length then mismatch
          else (variant.fields.zip payload).forM (fun (t, x) => checkClosureValueAt ctx fuel t x)
        | _ => mismatch
    | .Closure cid, .typedClosure held _fn captures =>
      if held != cid then mismatch else
        let d ← match ctx.closures cid with
          | some d => pure d
          | none => throw (.unsupported .closureDefTable "closure definition is absent")
        if d.captures.length != captures.length then mismatch
        else (d.captures.zip captures).forM (fun (t, x) => checkClosureValueAt ctx fuel t x)
    | .FatPtr kind, .fatPtr _ _ metadata =>
      checkClosureValueAt ctx fuel (kind.metadataTyAtModel ctx.byteModel) metadata
    | _, _ => mismatch

/-- The budget comes from the actual finite value tree, not a configurable
    evaluation depth. Every recursive edge checks a strict subvalue. It makes
    this check kernel-reducible even with recursive nominal type tables. -/
def checkClosureValue (ctx : EvalContext) (ty : Ty) (v : Value) : Except SemError Unit :=
  checkClosureValueAt ctx (v.depth + 1) ty v

/-- Construct from live SSA values. The result keeps all capture values exactly,
    including pointer allocation identities. -/
def makeClosureValue (ctx : EvalContext) (ty : ClosureTyId) (fn : FuncId)
    (captures : List Value) : Except SemError Value := do
  let (d, _, _) ← closureContract ctx ty fn
  if captures.length != d.captures.length then
    throw (.typeError "MakeClosure: capture arity mismatch")
  (d.captures.zip captures).forM (fun (t, v) => checkClosureValue ctx t v)
  pure (.typedClosure ty fn captures)

/-- Apply the exact nominal signature and prepend the environment to arguments.
    This is only argument resolution: `stepNWithContext` performs the ordinary
    frame transition and retains the callee's memory on return. -/
def closureCall (ctx : EvalContext) (ty : ClosureTyId) (fn : FuncId)
    (captures : List Value) (sig : FuncTyId) (args : List Value)
    (conv : CallingConv) : Except SemError (FuncId × List Value) := do
  let (d, apparent, target) ← closureContract ctx ty fn
  if d.func != sig then throw (.typeError "CallIndirect: closure signature id mismatch")
  if target.callingConv != conv then
    throw (.typeError "CallIndirect: closure calling convention mismatch")
  let _ ← makeClosureValue ctx ty fn captures
  if args.length != apparent.params.length then
    throw (.typeError "CallIndirect: closure argument arity mismatch")
  (apparent.params.zip args).forM (fun (t, v) => checkClosureValue ctx t v)
  pure (fn, captures ++ args)

/-- Capture access needs the declared environment, not an application of its
    code. Legacy constants may carry a target checked only when called, exactly
    as in the Rust interpreter; merely projecting data cannot invoke it. -/
def checkedClosureCaptures (ctx : EvalContext) (cid : ClosureTyId)
    (captures : List Value) : Except SemError ClosureTy := do
  let d ← match ctx.closures cid with
    | some d => pure d
    | none => throw (.unsupported .closureDefTable "closure definition is absent")
  if d.captures.length != captures.length then
    throw (.typeError "closure capture arity mismatch")
  (d.captures.zip captures).forM (fun (t, v) => checkClosureValue ctx t v)
  pure d

/-- Closure capture access checks the actual declared type, not an inferred
    value shape. The function identity and nominal type survive every update. -/
def closureExtract (ctx : EvalContext) (resultTy : Ty) (cid : ClosureTyId)
    (_fn : FuncId) (captures : List Value) (field : Nat) : Except SemError Value := do
  let d ← checkedClosureCaptures ctx cid captures
  let fieldTy ← match (trustIrListGet? d.captures field) with
    | some t => pure t
    | none => throw (.ub "ExtractField: closure capture index out of bounds")
  if !(closureTyEq fieldTy resultTy) then throw (.typeError "ExtractField: closure capture type mismatch")
  match (trustIrListGet? captures field) with
  | some v => pure v
  | none => throw (.typeError "ExtractField: closure capture arity mismatch")

def closureInsert (ctx : EvalContext) (resultTy : Ty) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) (v : Value) : Except SemError Value := do
  if !(closureTyEq resultTy (.Closure cid)) then throw (.typeError "InsertField: closure type mismatch")
  let d ← checkedClosureCaptures ctx cid captures
  let fieldTy ← match (trustIrListGet? d.captures field) with
    | some t => pure t
    | none => throw (.ub "InsertField: closure capture index out of bounds")
  checkClosureValue ctx fieldTy v
  pure (.typedClosure cid fn (captures.set field v))

/-- The global initializer's pure typed denotation shares the ordinary Const
    converter, including inline tuple/vector widths and typed null pointers.
    Actual global materialization uses `constValueAtChecked` and validates the
    encoded byte count before touching memory. -/
def valueOfConstAtTy (ty : Ty) (c : Constant) (model : ByteModel := .le64) : Value :=
  constValueAt ty c model

/-- Full-fidelity `GlobalAddr`: materialize a pointer to a module global with its
    TRUE byte size and initializer content. The first address-of a `GlobalId`
    reserves `def.ty.byteSize` bytes from the allocator, writes the encoded
    initializer (if present) OR zero-fills the storage (BSS/.tbss loader
    semantics) when there is no initializer, and caches the address; a later
    address-of returns the cached address — cache lookup happens FIRST, so the
    existing `semGlobalAddr_cache_hit` aliasing reasoning carries over to the
    cached branch. Faithful to the Rust reference interpreter's `global_pointer`
    (crates/trust-ir/src/interpret.rs; BSS zero-fill, commit 2b3954e), whose
    placement it shares: aligned to the max of the type's natural alignment,
    a power-of-two declared one and `globalSectionAlign`.

    PARTIAL (honest, NOT faked): an initializer whose value has no byte encoding
    (`encodeValueAt` refuses — aggregate/sequence/set/record/closure) is
    rejected with a structured `unsupported` error rather than silently
    mis-encoded. Byte-layout for those shapes is documented follow-up. A float
    initializer is encoded at the global's float type; a refusal from the
    float codec keeps its own `unsupported.float` reason. -/
def semGlobalAddrUsing (encode : Ty → Value → Except SemError (List UInt8))
    (globalsTable : GlobalsTable) (global : GlobalId) (model : ByteModel := .le64) :
    Sem ValueId := do
  let s ← Sem.getState
  match s.lookupGlobal global with
  | some (addr, allocId) => do
    let addr ← Sem.targetAddress model "GlobalAddr" addr
    Sem.bindFresh (.ptr addr (some allocId))
  | none =>
    let gdef ← match globalsTable global with
      | some d => pure d
      | none => Sem.throwTypeError "GlobalAddr: global not in module table"
    let byteSize ← match (gdef.ty.byteSizeFor model) with
      | some n => pure n
      | none => Sem.throwUnsupported .layout "GlobalAddr: global type has no byte size"
    -- The interpreter's `global_pointer` placement: the max of the natural
    -- alignment, a power-of-two declared one, and `globalSectionAlign`.
    let natural := (gdef.ty.byteAlignFor model).getD 1
    let declared := match gdef.align with
      | some a => if isPow2 a then a else 1
      | none => 1
    Sem.checkTargetAllocation model s.memory byteSize (max (max natural declared) globalSectionAlign) 0
    let (baseAddr, mem') :=
      s.memory.alloc byteSize (max (max natural declared) globalSectionAlign) 0 .rustHeap
    let allocId := AllocId.mk s.memory.nextAllocId
    let perms' := s.permissions.set allocId .owned
    let mem'' ← match gdef.initializer with
      | none =>
        -- BSS / .tbss loader semantics: a global with NO initializer is
        -- zero-filled at load time, so a Load through its pointer reads a
        -- DEFINED zero (not uninitialized / poison). Mirrors the Rust
        -- reference interpreter (interpret.rs commit 2b3954e).
        pure (mem'.writeImage baseAddr (ByteImage.fill byteSize (some 0)))
      | some initC =>
        -- A relocatable `&symbol + addend` slot (a vtable / fn-pointer table)
        -- has no load-time value this model (or the reference interpreter)
        -- can produce: refuse it before lowering, at any nesting depth.
        if initC.hasSymbolAddr then
          Sem.throwUnsupported .linkTimeAddress
            "GlobalAddr: initializer holds a link-time symbol address"
        else do
          let initialValue ← match constValueAtChecked gdef.ty initC model false with
            | .ok value => pure value
            | .error error => throw error
          match encode gdef.ty initialValue with
          | .ok bytes =>
            if bytes.length != byteSize then
              Sem.throwTypeError "GlobalAddr: initializer byte count does not match the declared type"
            else pure (mem'.writeBytes baseAddr bytes)
          | .error (.unsupported feature msg) => Sem.throwUnsupported feature msg
          | .error error =>
            match gdef.ty with
            | .Func _ => throw error
            | _ =>
              Sem.throwUnsupported .vectorShape
                "GlobalAddr: initializer value has no byte encoding (aggregate/record/etc.)"
    Sem.setState
      { s with
        memory := mem''
        permissions := perms'
        globals := (global, baseAddr, allocId) :: s.globals }
    Sem.bindFresh (.ptr baseAddr (some allocId))

/-- The context-free global entry retains its existing byte codec. -/
def semGlobalAddrWithCtx (globalsTable : GlobalsTable) (global : GlobalId)
    (model : ByteModel := .le64) : Sem ValueId :=
  semGlobalAddrUsing (encodeMemoryAt model) globalsTable global model

-- ---------------------------------------------------------------------------
-- WS2.19: definition-table-directed constant lowering and lane typing
-- ---------------------------------------------------------------------------

/-- The module data a constant can inspect. Function bodies and call budgets
    are deliberately absent: changing a CFG cannot change a literal value. -/
structure ConstantEvalContext where
  byteModel : ByteModel
  valueSource : FunctionItemPresence.Prepared := FunctionItemPresence.prepare {}

def ConstantEvalContext.types (ctx : ConstantEvalContext) : TyId → Option Ty := ctx.valueSource.ty
def ConstantEvalContext.structs (ctx : ConstantEvalContext) : StructId → Option StructDef := ctx.valueSource.firstStructDef
def ConstantEvalContext.enums (ctx : ConstantEvalContext) : EnumId → Option EnumDef := ctx.valueSource.firstEnumDef
def ConstantEvalContext.records (ctx : ConstantEvalContext) : RecordId → Option RecordDef := ctx.valueSource.firstRecordDef
def ConstantEvalContext.closures (ctx : ConstantEvalContext) : ClosureTyId → Option ClosureTy := ctx.valueSource.closureTy

def ConstantEvalContext.functionItems (ctx : ConstantEvalContext) :
    FuncId → Option (Except String FunctionItemHeader) := ctx.valueSource.functionItem

/-- Project exactly the definition tables used by constant lowering. -/
def EvalContext.constantContext (ctx : EvalContext) : ConstantEvalContext :=
  ⟨ctx.byteModel, ctx.valueSource⟩

/-- Distinct supplied record names, together with the declared census and
    membership checks below, name every declared field exactly once. -/
def constRecordNamesDistinct : List (String × Constant) → Bool
  | [] => true
  | (name, _) :: rest =>
    !(rest.any (fun field => field.fst == name)) && constRecordNamesDistinct rest

mutual

/-- Lower a constant at its declared type WITH the definition tables: an
    enum-typed aggregate `[tag, fields..]` types its tag lane at the canonical
    tag width and each payload lane at the ACTIVE variant's field type; a
    struct-typed aggregate types each lane at its declared field type; a
    tuple each lane at its element type; an array literal each element at the
    element type the type table names. Sequences and sets likewise resolve
    their element type through that table; records select each supplied name
    from the record definition before lowering its value. A positional record
    aggregate uses declaration order and attaches those declared names. Bytes
    require the resolved element type to be U8. Every remaining form passes
    through the checked scalar/inline converter.
    Mirrors the reference interpreter's `constant_to_value_in` (a
    discriminant naming no variant, or a lane-count mismatch, is a type error
    there too). Nested lanes recurse.

    FAIL CLOSED on a missing table. An enum / struct / array / sequence /
    set / record constant whose table entry the context does not carry is `unsupported.enum_def_table`
    (the module-definition-table refusal `MakeAggregate` already uses), never
    the untyped `constValueAt` lowering: that lowering gives every integer
    lane the 64-bit default, and `stepInstWithContext`'s `ExtractField` lane
    check (`laneMatchesTy`) would read a default-width lane of a VALID
    aggregate as a wrong-lane projection — a fabricated UB. So under the
    module context every aggregate lane this function produces carries its
    declared width, which is what makes that check sound. -/
def constValueAtWithDefsIn (ctx : ConstantEvalContext) (ty : Ty) (c : Constant)
    (allowUninitFields : Bool := true) : Except SemError Value := do
  if !constPointerFormsSupported ty c then
    throw (.typeError "constant requires null pointer spellings and matching inline field census")
  match ty, c with
  | .FnItem expected, .fnItem held =>
    if expected != held then throw (.typeError "FnItem: constant identity differs from type")
    match ctx.functionItems expected with
    | some (.ok _) => pure (.fnItem expected)
    | some (.error message) => throw (.typeError message)
    | none => throw (.typeError "FnItem: original function declaration is absent")
  | .FnItem _, _ | _, .fnItem _ =>
    throw (.typeError "FnItem: constant and nominal type must have the same identity")
  | .Closure cid, .closure fn cs => do
    let d ← match ctx.closures cid with
      | some d => pure d
      | none => throw (.unsupported .closureDefTable "closure definition is absent")
    if d.captures.length != cs.length then
      throw (.typeError "Const: closure capture arity mismatch")
    let captures ← constFieldsAtWithDefsIn ctx d.captures cs
    pure (.typedClosure cid fn captures)
  | _, .closure _ _ => throw (.typeError "Const: closure requires a nominal closure type")
  | .Enum eid, .aggregate cs =>
    match ctx.enums eid with
    | none =>
      throw (.unsupported .enumDefTable
        "Const: an enum constant's lane types need the module's enum table")
    | some d =>
      match cs with
      | .int disc :: fieldCs => do
        let discs ← match enumEffectiveDiscriminants d with
          | some ds => pure ds
          | none => throw (.typeError "Const: enum has no canonical discriminant assignment")
        let repr ← match enumCanonicalTagRepr d with
          | some r => pure r
          | none => throw (.typeError "Const: enum has no canonical tag representation")
        let variantIdx ← match listIndexOf? discs disc with
          | some i => pure i
          | none => throw (.typeError "Const: discriminant names no variant of the enum")
        let variant ← match (trustIrListGet? d.variants variantIdx) with
          | some v => pure v
          | none => throw (.typeError "Const: discriminant names no variant of the enum")
        if variant.fields.length != fieldCs.length then
          throw (.typeError "Const: enum constant payload arity does not match the variant")
        let lanes ← constFieldsAtWithDefsIn ctx variant.fields fieldCs
        -- The variant is found by the discriminant's VALUE (`disc`, an `Int`,
        -- negative for `Less = -1`); the tag LANE holds its residue at the tag
        -- width, the representation every other integer value has.
        pure (.aggregate (Value.intAt repr.bitWidth disc :: lanes))
      | _ => throw (.typeError "Const: an enum constant is `[integer discriminant, fields..]`")
  | .Struct sid, .aggregate cs =>
    match ctx.structs sid with
    | none =>
      throw (.unsupported .enumDefTable
        "Const: a struct constant's lane types need the module's struct table")
    | some d => do
      if d.fields.length != cs.length then
        throw (.typeError "Const: struct constant arity does not match the definition")
      let lanes ← constUninitFieldsAtWithDefsIn ctx (d.fields.map (·.ty)) cs allowUninitFields
      pure (.aggregate lanes)
  | .Tuple tys, .aggregate cs =>
    if tys.length == cs.length then do
      let lanes ← constUninitFieldsAtWithDefsIn ctx tys cs allowUninitFields
      pure (.aggregate lanes)
    else throw (.typeError "Const: tuple constant arity does not match the type")
  | .Array tid n, .bytes data _ => do
    if data.length != n then
      throw (.typeError "Const: bytes constant length does not match the array type")
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: a bytes constant's element type needs the module's type table")
    if !(elemTy == .U8) then
      throw (.typeError "Const: bytes constant requires an array of U8")
    pure (.array (CompactArray.Packed.ofArray (data.map (fun byte => .int 8 (Int.ofNat byte.toNat))).toArray))
  | .Array tid n, .array cs | .Array tid n, .aggregate cs => do
    if cs.length != n then
      throw (.typeError "Const: array constant length does not match the type")
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: an array constant's element type needs the module's type table")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.array (CompactArray.Packed.ofArray lanes.toArray))
  | .Sequence tid, .sequence cs => do
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: a sequence constant's element type needs the module's type table")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.sequence lanes)
  | _, .sequence _ => throw (.typeError "Const: sequence requires a sequence type")
  | .Set tid _, .set cs => do
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: a set constant's element type needs the module's type table")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.set lanes)
  | _, .set _ => throw (.typeError "Const: set requires a set type")
  | .Record rid, .aggregate cs => do
    let d ← match ctx.records rid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable
          "Const: a record constant's field types need the module's record table")
    if d.fields.length != cs.length then
      throw (.typeError "Const: record constant arity does not match the definition")
    let lanes ← constFieldsAtWithDefsIn ctx (d.fields.map (·.ty)) cs
    pure (.record ((d.fields.map (·.name)).zip lanes))
  | .Record rid, .record fs => do
    let d ← match ctx.records rid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable
          "Const: a record constant's field types need the module's record table")
    if d.fields.length != fs.length then
      throw (.typeError "Const: record constant arity does not match the definition")
    if !constRecordNamesDistinct fs then
      throw (.typeError "Const: record constant repeats a declared field name")
    let fields ← constRecordFieldsAtWithDefsIn ctx d.fields fs
    pure (.record fields)
  | _, .record _ => throw (.typeError "Const: record requires a record type")
  | .Vector count elemTy, .vector cs => do
    if (vectorScalarByteSize elemTy).isNone then
      throw (.typeError "vector constant requires an admitted scalar lane type")
    if count == 0 || cs.length != count then
      throw (.unsupported .vectorShape "vector constant lane count does not match its declared type")
    let lanes ← constLanesAtWithDefsIn ctx elemTy cs
    pure (.vector lanes)
  | .Array tid n, .splat elem count => do
    if count != n then
      throw (.typeError "Const: splat constant length does not match the type")
    let elemTy ← match ctx.types tid with
      | some t => pure t
      | none => throw (.unsupported .enumDefTable
          "Const: an array constant's element type needs the module's type table")
    let v ← constValueAtWithDefsIn ctx elemTy elem false
    pure (.array (CompactArray.Packed.uniform n v))
  | _, _ => constValueAtChecked ty c ctx.byteModel allowUninitFields

/-- Tuple/struct fields at the root instruction may be unwritten. Recursion
    into every written field revokes that placement permission. -/
def constUninitFieldsAtWithDefsIn (ctx : ConstantEvalContext) (tys : List Ty)
    (cs : List Constant) (allowUninit : Bool) : Except SemError (List Value) :=
  match tys, cs with
  | [], [] => pure []
  | _ :: tys, .uninit :: cs => do
    if !allowUninit then
      throw (.typeError "uninit is only a direct field of an instruction tuple/struct constant")
    let rest ← constUninitFieldsAtWithDefsIn ctx tys cs allowUninit
    pure (.uninit :: rest)
  | ty :: tys, c :: cs => do
    let first ← constValueAtWithDefsIn ctx ty c false
    let rest ← constUninitFieldsAtWithDefsIn ctx tys cs allowUninit
    pure (first :: rest)
  | _, _ => throw (.typeError "Const: field count does not match its declared type")

/-- Lower strict positional fields from left to right. These callers do not
    admit Uninit lanes. Recursing on the constant list keeps the complete
    constant lowering kernel-reducible. -/
def constFieldsAtWithDefsIn (ctx : ConstantEvalContext) (tys : List Ty) (cs : List Constant) :
    Except SemError (List Value) :=
  match tys, cs with
  | t :: ts, c :: cs => do
    let v ← constValueAtWithDefsIn ctx t c false
    let vs ← constFieldsAtWithDefsIn ctx ts cs
    pure (v :: vs)
  | [], [] => pure []
  | _, _ => throw (.typeError "Const: field count does not match its declared type")

/-- Lower homogeneous array lanes from left to right at their declared type. -/
def constLanesAtWithDefsIn (ctx : ConstantEvalContext) (elemTy : Ty) (cs : List Constant) :
    Except SemError (List Value) :=
  match cs with
  | [] => pure []
  | c :: cs => do
    let v ← constValueAtWithDefsIn ctx elemTy c false
    let vs ← constLanesAtWithDefsIn ctx elemTy cs
    pure (v :: vs)

/-- Resolve record names against their declaration while preserving literal
    order and left-to-right failures. The enclosing record conversion checks
    census and distinct names before this membership/type walk. -/
def constRecordFieldsAtWithDefsIn (ctx : ConstantEvalContext) (declared : List FieldDef)
    (fields : List (String × Constant)) : Except SemError (List (String × Value)) :=
  match fields with
  | [] => pure []
  | (name, c) :: rest => do
    let field ← match declared.find? (fun f => f.name == name) with
      | some f => pure f
      | none => throw (.typeError s!"Const: record field {name} not declared")
    let v ← constValueAtWithDefsIn ctx field.ty c false
    let vs ← constRecordFieldsAtWithDefsIn ctx declared rest
    pure ((name, v) :: vs)

end

/-- Lower a module constant using only its byte model and definition tables.
    Total structural recursion makes this executable definition available to
    kernel proofs; no extra execution fuel or refusal policy is introduced. -/
def constValueAtWithDefs (ctx : EvalContext) (ty : Ty) (c : Constant) :
    Except SemError Value :=
  constValueAtWithDefsIn ctx.constantContext ty c

/-- WS2.19: a projected lane must have the DECLARED result type, where the
    value model can tell: an integer lane's width against `ty.bitWidth`, and
    Bool against `Ty.Bool`. On an enum value this is the reference
    interpreter's WS2.2 item 5 rule — lane `field` must be a field of the
    ACTIVE variant at the access type, else UB — restricted to what an untyped
    `Value` shows (the model has no signedness, so an `i32` lane read at `u32`
    is invisible here; recorded in the B3 depth ledger). Permissive wherever
    the value cannot tell (float / pointer / composite lanes, a type with no
    bit width), so it can only ever ADD a UB verdict where the widths differ.

    Why this is not a fabricated UB on a struct / tuple / array: a validated
    struct or tuple lane holds a value of its declared type, and under the
    module context every aggregate VALUE the evaluator builds carries its
    lanes at their declared widths — constants through
    `constValueAtWithDefs` (which refuses, rather than defaults, a lane type
    it cannot resolve), `MakeAggregate` / `InsertField` from typed SSA
    values. So a width disagreement is a read of a lane the active enum
    variant does not have at that type, which the interpreter calls UB. -/
def laneMatchesTy (ty : Ty) (v : Value) (model : ByteModel := .le64) : Bool :=
  match v, ty with
  | .int w _, .Bool => w == 1
  | .int w _, t =>
    match t.bitWidthFor model with
    | some w' => w == w'
    | none => true
  | .bool _, .Bool => true
  | .bool _, t => (t.bitWidthFor model).isNone
  | _, _ => true

/-- WS2.19: the `InsertField` twin of `laneMatchesTy`. `InsertField`'s `ty` is
    the AGGREGATE type, so the lane's type is the inserted value's; the lane
    the aggregate already holds at `field` must agree with it in width (an
    integer against an integer; `Bool` against `Bool` or a 1-bit integer).
    On an enum value this is the interpreter's WS2.2 item 5 rule for a write:
    a lane of another variant is UB. Permissive across every other pair of
    value kinds, and sound on a struct / tuple by the same argument as
    `laneMatchesTy` (the context builds every aggregate at its declared lane
    widths, and the inserted value has the lane's declared type). -/
def lanesAgree (held inserted : Value) : Bool :=
  match held, inserted with
  | .int w₁ _, .int w₂ _ => w₁ == w₂
  | .bool _, .int w _ => w == 1
  | .int w _, .bool _ => w == 1
  | _, _ => true

/-- A constructor inspects its immediate operands. It transports each
    composite operand intact, matching the reference interpreter's
    `reject_partial` followed by `expect_ty`, rather than recursively reading
    its fields. The source validator supplies nominal type correspondence;
    the value model can additionally check scalar families and carrier widths.
    In particular a nested Uninit or raw Char carrier is not inspected here. -/
def checkAggregateLane (model : ByteModel) (ty : Ty) (value : Value) :
    Except SemError Unit := do
  if value.isPoison || value.isUninit then
    throw (.ub "MakeAggregate: uninitialized immediate operand")
  let mismatch := Except.error (SemError.typeError "MakeAggregate: operand does not match its declared type")
  match ty, value with
  | .Bool, .bool _ => pure ()
  | .I8, .int w _ | .U8, .int w _ => if w == 8 then pure () else mismatch
  | .I16, .int w _ | .U16, .int w _ => if w == 16 then pure () else mismatch
  | .I32, .int w _ | .U32, .int w _ | .Char, .int w _ =>
    if w == 32 then pure () else mismatch
  | .I64, .int w _ | .U64, .int w _ => if w == 64 then pure () else mismatch
  | .I128, .int w _ | .U128, .int w _ => if w == 128 then pure () else mismatch
  | .Isize, .int w _ | .Usize, .int w _ =>
    if w == model.pointerBits then pure () else mismatch
  | .F16, .float f | .F32, .float f | .F64, .float f => checkFloatAt ty f
  | .Ptr, .ptr _ _ | .Ptr, .nullPtr
  | .Ref _, .ptr _ _ | .Ref _, .nullPtr
  | .RefMut _, .ptr _ _ | .RefMut _, .nullPtr
  | .PtrConst _, .ptr _ _ | .PtrConst _, .nullPtr
  | .PtrMut _, .ptr _ _ | .PtrMut _, .nullPtr
  | .Rc _, .ptr _ _ | .Rc _, .nullPtr => pure ()
  | .Unit, .aggregate [] => pure ()
  | .FnItem expected, .fnItem held => if expected == held then pure () else mismatch
  | .Func expected, .fnDef held _ => if expected == held then pure () else mismatch
  | .Func _, .nullPtr => pure ()
  | .Tuple _, .aggregate _ | .Struct _, .aggregate _ | .Array _ _, .array _
  | .Enum _, .aggregate _ | .Vector _ _, .vector _
  | .Sequence _, .sequence _ | .Set _ _, .set _ | .Record _, .record _
  | .FatPtr _, .fatPtr _ _ _ => pure ()
  | .Closure expected, .typedClosure held _ _ =>
    if expected == held then pure () else mismatch
  | .Closure _, .closure _ _ => pure ()
  | _, _ => mismatch

/-- Build an enum or named record from actual register values and module
    declarations. This is value construction, not byte layout. Only immediate
    lanes are inspected; composite contents retain their existing state. -/
def makeAggregateValueWithContext (ctx : EvalContext) (ty : Ty) (variant : Option Nat)
    (lanes : List Value) : Except SemError Value := do
  match ty, variant with
  | .Enum _, none =>
    throw (.typeError "MakeAggregate: an enum construction needs a variant index")
  | .Enum eid, some index =>
    let d ← match ctx.enums eid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable "MakeAggregate: enum definition is absent")
    let selected ← match (trustIrListGet? d.variants index) with
      | some selected => pure selected
      | none => throw (.typeError "MakeAggregate: enum variant index is out of bounds")
    let discs ← match enumEffectiveDiscriminants d with
      | some discs => pure discs
      | none => throw (.typeError "MakeAggregate: enum discriminants are invalid")
    let repr ← match enumCanonicalTagRepr d with
      | some repr => pure repr
      | none => throw (.typeError "MakeAggregate: enum tag representation is invalid")
    let disc ← match (trustIrListGet? discs index) with
      | some disc => pure disc
      | none => throw (.typeError "MakeAggregate: enum variant has no discriminant")
    if selected.fields.length != lanes.length then
      throw (.typeError "MakeAggregate: enum payload arity mismatch")
    (selected.fields.zip lanes).forM (fun (t, v) => checkAggregateLane ctx.byteModel t v)
    pure (.aggregate (Value.intAt repr.bitWidth disc :: lanes))
  | .Record _, some _ =>
    throw (.typeError "MakeAggregate: a variant index is only meaningful for an enum")
  | .Record rid, none =>
    let d ← match ctx.records rid with
      | some d => pure d
      | none => throw (.unsupported .enumDefTable "MakeAggregate: record definition is absent")
    if d.fields.length != lanes.length then
      throw (.typeError "MakeAggregate: record field arity mismatch")
    (d.fields.zip lanes).forM (fun (field, v) => checkAggregateLane ctx.byteModel field.ty v)
    pure (.record ((d.fields.map (·.name)).zip lanes))
  | _, _ =>
    throw (.typeError "MakeAggregate: contextual construction requires an enum or record type")

/-- Inspect an actual array operand's original declaration, preserving table
    absence separately from an absent entry and retaining exact type identity. -/
def checkArrayRegisterType (table : Option LocalTypeTable) (elementTy : Ty)
    (id : ValueId) : Except SemError Unit := do
  let table ← match table with
    | some table => pure table
    | none => throw (.unsupported .ssaTypeTable "MakeAggregate: original SSA declarations are absent")
  let sourceTy ← match table id with
    | some ty => pure ty
    | none => throw (.typeError "MakeAggregate: operand has no SSA declaration")
  if !(closureTyEq elementTy sourceTy) then
    throw (.typeError "MakeAggregate: operand type differs from the declared element type")

/-- Construct an array from the actual lane values and original register
    declarations. Type identity is checked without inspecting payload contents;
    the stateful caller supplies lookupLanes, preserving operand error order. -/
def makeArrayValueWithContext (ctx : EvalContext) (element : TyId) (count : Nat)
    (variant : Option Nat) (ids : List ValueId) (lanes : List Value) : Except SemError Value := do
  if variant.isSome then
    throw (.typeError "MakeAggregate: a variant index is only meaningful for an enum")
  if lanes.length != count || ids.length != count then
    throw (.typeError "MakeAggregate: array lane count does not match its type")
  let elementTy ← match ctx.types element with
    | some ty => pure ty
    | none => throw (.unsupported .enumDefTable "MakeAggregate: array element declaration is absent")
  ids.forM (checkArrayRegisterType ctx.localTypes elementTy)
  pure (.array (CompactArray.Packed.ofArray lanes.toArray))

/-- Stable diagnostics for non-partial Undef. Classification is independent
    of pointer width; size selection is needed only for admitted scalar poison. -/
def nonpartialUndefMessage : Ty → String
  | .Vector _ _ => "undef of non-scalar vector type is not executable"
  | .Func _ => "Undef of function type is not executable (function poison unmodelled)"
  | _ => "Undef of non-scalar type is not executable (aggregate poison unmodelled)"

/-- Resolve a field against the original aggregate declaration and, for enums,
    the active tag. Equal-width integer values do not retain signedness. -/
def declaredFieldTy (ctx : EvalContext) (aggregateTy : Ty) (held : Value)
    (field : Nat) : Except SemError Ty := do
  let missing := SemError.unsupported .enumDefTable "field access requires its original definition"
  let bounds := SemError.ub "field access is outside the active aggregate"
  match aggregateTy with
  | .Tuple fields => match (trustIrListGet? fields field) with
    | some ty => pure ty
    | none => throw bounds
  | .Struct sid =>
    let d ← match ctx.structs sid with | some d => pure d | none => throw missing
    match (trustIrListGet? d.fields field) with
    | some f => pure f.ty
    | none => throw bounds
  | .Record rid =>
    let d ← match ctx.records rid with | some d => pure d | none => throw missing
    match (trustIrListGet? d.fields field) with
    | some f => pure f.ty
    | none => throw bounds
  | .Enum eid =>
    let d ← match ctx.enums eid with | some d => pure d | none => throw missing
    let repr ← match enumCanonicalTagRepr d with
      | some repr => pure repr
      | none => throw (.typeError "field access: enum has no canonical tag representation")
    if field == 0 then return repr.ty
    let discs ← match enumEffectiveDiscriminants d with
      | some discs => pure discs
      | none => throw (.typeError "field access: enum discriminants are invalid")
    let tag ← match getField held 0 with
      | some (.int width tag) =>
        if width == repr.bitWidth then pure tag
        else throw (.typeError "field access: enum tag width mismatch")
      | _ => throw (.typeError "field access: enum tag is not an integer")
    let residues := discs.map (fun disc => disc % ((2 : Int) ^ repr.bitWidth))
    let index ← match listIndexOf? residues tag with
      | some index => pure index
      | none => throw (.typeError "field access: enum tag names no variant")
    let variant ← match (trustIrListGet? d.variants index) with
      | some variant => pure variant
      | none => throw bounds
    match (trustIrListGet? variant.fields (field - 1)) with
    | some ty => pure ty
    | none => throw bounds
  | _ => throw (.typeError "field access requires an aggregate declaration")

/-- The contextual lane check retains nominal identity and signedness.
    Context-free stepping remains a separately documented partial model. -/
def checkDeclaredField (ctx : EvalContext) (aggregateId : ValueId) (held : Value)
    (field : Nat) (accessTy : Ty) : Except SemError Unit := do
  match ctx.localTypes with
  | none => pure ()
  | some table =>
    let aggregateTy ← match table aggregateId with
      | some ty => pure ty
      | none => throw (.typeError "field access: aggregate SSA declaration is absent")
    let expected ← declaredFieldTy ctx aggregateTy held field
    if closureTyEq expected accessTy then pure ()
    else match aggregateTy, field with
      | .Enum _, _ + 1 => throw (.ub "field access does not match the active enum lane type")
      | _, _ => throw (.typeError "field access does not match the exact declared lane type")

/-- The loader zero-fills absent image bytes; typed Store deliberately does
    not. Actual named initializer typing uses the same original source tables
    as contextual Const, with the global Uninit role disabled. -/
def semGlobalAddrInContext (ctx : EvalContext) (global : GlobalId) : Sem ValueId := do
  let service := match ctx.globalsTable global with
    | some definition => ctx.memoryServiceFor definition.ty
    | none => ctx.memoryService
  match service with
  | none => semGlobalAddrUsing (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder) ctx.globalsTable global ctx.byteModel
  | some service =>
    let state ← Sem.getState
    match state.lookupGlobal global with
    | some (address, allocation) =>
      let address ← Sem.targetAddress ctx.byteModel "GlobalAddr" address
      Sem.bindFresh (.ptr address (some allocation))
    | none =>
      let definition ← match ctx.globalsTable global with
        | some definition => pure definition
        | none => Sem.throwTypeError "GlobalAddr: global not in module table"
      if service.model != ctx.byteModel then
        Sem.throwTypeError "GlobalAddr: source layout target does not match evaluator target"
      let layout ← Sem.fromMemoryExcept (service.queryLayout definition.ty)
      let declared := match definition.align with
        | some alignment => if isPow2 alignment then alignment else 1
        | none => 1
      let alignment := max (max layout.alignment declared) globalSectionAlign
      Sem.checkTargetAllocation ctx.byteModel state.memory layout.size alignment 0
      let (address, memory) := state.memory.alloc layout.size alignment 0 .rustHeap
      let allocation : AllocId := ⟨state.memory.nextAllocId⟩
      let bytes ← match definition.initializer with
        | none => pure (ByteImage.fill layout.size (some 0))
        | some constant =>
          if constant.hasSymbolAddr then
            Sem.throwUnsupported .linkTimeAddress "GlobalAddr: initializer holds a link-time symbol address"
          else
            let value ← Sem.fromMemoryExcept
              (constValueAtWithDefsIn ctx.constantContext definition.ty constant false)
            let plan ← Sem.fromMemoryExcept (service.query definition.ty)
            let image ← Sem.fromMemoryExcept
              (AggregateMemory.encode ctx.byteModel ctx.functionOrder plan value false)
            pure image.zeroUninit
      if bytes.size != layout.size then
        Sem.throwTypeError "GlobalAddr: initializer byte count does not match source layout"
      Sem.setState { state with
        memory := memory.writeImage address bytes,
        permissions := state.permissions.set allocation .owned,
        globals := (global, address, allocation) :: state.globals }
      Sem.bindFresh (.ptr address (some allocation))

/-- Dispatch a body instruction WITH module context: memory consumers use the
    source-order Func codec, and globals retain their full initializer image;
    an aggregate `Const` lowers its lanes
    at their declared types through the definition tables
    (`constValueAtWithDefs`); `ExtractField` checks the projected lane against
    its declared type (`laneMatchesTy`) and `InsertField` the replaced lane
    against the inserted value (`lanesAgree`); enum/record `MakeAggregate`
    resolves and checks its actual lanes against those tables without a byte
    layout query. Every other instruction
    delegates to the bare `stepInst` (whose `GlobalAddr` arm is the honest
    size-1 partial and whose aggregate lanes keep the untyped default). -/
def stepInstWithContext (ctx : EvalContext) (inst : Inst) :
    Sem InstrResult := do
  match inst with
  | .OpenFrame declaration =>
    match ctx.currentFunction with
    | none =>
      -- The context-free API retains its ordinary typed-unwritten carrier.
      pure (.value (some (← semOpenFrame declaration)))
    | some origin => do
      let original ← match ctx.valueSource.bindingFrame origin declaration.id with
        | some original => pure original
        | none => Sem.throwTypeError "OpenFrame: original declaration is absent or ambiguous"
      if !(bindingFrameDeclarationEq original declaration) then
        Sem.throwTypeError "OpenFrame: instruction differs from original slot declaration"
      let state ← Sem.getState
      if state.nextFrameLineage < 2 ^ Sem.frameLineageBits - 1 then
        Sem.setFrameState (state.nextFrameLineage :: state.openFrameLineages) (state.nextFrameLineage + 1)
        let id ← Sem.bindFresh (.sourceFrame state.nextFrameLineage origin original (original.slots.map (fun _ => .uninit)))
        pure (.value (some id))
      else Sem.throwUB "OpenFrame: frame id overflow"
  | .BindSlot frame slot value =>
    let (lineage, slots) ← Sem.frameHandle frame "BindSlot"
    let state ← Sem.getState
    if !(state.openFrameLineages.contains lineage) then
      Sem.throwUB "BindSlot: frame is not open"
    let held ← Sem.lookupValue frame
    match held with
    | .frame _ _ => do
      let value ← Sem.lookupValue value
      if slot < slots.length then
        -- An ordinary carrier supplies no original nominal slot authority.
        Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) .Error value)
        let result ← match bindSlot held slot value with
          | some result => pure result
          | none => Sem.throwUB s!"BindSlot: slot {slot} out of range for frame of {slots.length} slots"
        pure (.value (some (← Sem.bindFresh result)))
      else Sem.throwUB s!"BindSlot: slot {slot} out of range for frame of {slots.length} slots"
    | _ => do
      let types ← Sem.fromMemoryExcept (bindingFrameTypes ctx held)
      let value ← Sem.lookupValue value
      let ty ← match trustIrListGet? types slot with
        | some ty => pure ty
        | none => Sem.throwUB "BindSlot: slot out of bounds"
      Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) ty value)
      let result ← match bindSlot held slot value with
        | some result => pure result
        | none => Sem.throwUB "BindSlot: slot out of bounds"
      pure (.value (some (← Sem.bindFresh result)))
  | .LoadSlot frame slot ty =>
    let (lineage, slots) ← Sem.frameHandle frame "LoadSlot"
    let state ← Sem.getState
    if !(state.openFrameLineages.contains lineage) then
      Sem.throwUB "LoadSlot: frame is not open"
    let held ← Sem.lookupValue frame
    match held with
    | .frame _ _ =>
      match trustIrListGet? slots slot with
      | none => Sem.throwUB s!"LoadSlot: slot {slot} out of range for frame of {slots.length} slots"
      | some value => do
        Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) .Error value)
        pure (.value (some (← Sem.bindFresh value)))
    | _ => do
      let types ← Sem.fromMemoryExcept (bindingFrameTypes ctx held)
      let declared ← match trustIrListGet? types slot with
        | some declared => pure declared
        | none => Sem.throwUB "LoadSlot: slot out of bounds"
      if !(closureTyEq declared ty) then
        Sem.throwTypeError "LoadSlot: requested type differs from original slot declaration"
      let value ← match loadSlot held slot with
        | some value => pure value
        | none => Sem.throwUB "LoadSlot: slot out of bounds"
      if value.isUninit then
        if isPartialLoadTy ty then
          pure (.value (some (← Sem.bindFresh (.undef ty))))
        else Sem.throwUB (nonpartialUndefMessage ty)
      else
        Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) ty value)
        pure (.value (some (← Sem.bindFresh value)))
  | .CloseFrame frame =>
    let held ← Sem.lookupValue frame
    match held with
    | .sourceFrame _ _ _ _ => do
      let _ ← Sem.fromMemoryExcept (bindingFrameTypes ctx held)
      semCloseFrame frame
      pure (.value none)
    | _ =>
      semCloseFrame frame
      pure (.value none)
  | .Alloca ty count align =>
    let id ← semAllocaUsing ctx.memoryLayout ctx.carrierIntegerOperand
      ty count align ctx.byteModel
    pure (.value (some id))
  | .HeapAlloc ty count align origin =>
    let id ← semHeapAllocUsing ctx.memoryLayout ctx.carrierIntegerOperand
      ty count origin align ctx.byteModel
    pure (.value (some id))
  | .GEP ty base indices _ =>
    let id ← semGEPUsing ctx.memoryLayout ctx.carrierIntegerOperand
      ty base indices ctx.byteModel
    pure (.value (some id))
  | .Cast .ReifyFnPointer (.FnItem source) (.Func signature) operand =>
    let value ← Sem.lookupValue operand
    Sem.rejectPartial value "ReifyFnPointer"
    match value with
    | .fnItem held =>
      if held != source then Sem.throwTypeError "ReifyFnPointer: item identity differs from source type"
      let declaration ← Sem.fromMemoryExcept (functionItemDeclaration ctx source)
      if declaration.signatureId != signature then
        Sem.throwTypeError "ReifyFnPointer: destination signature differs from item declaration"
      pure (.value (some (← Sem.bindFresh (.fnDef signature source))))
    | _ => Sem.throwTypeError "ReifyFnPointer: source is not a nominal function item"
  | .Cast op source destination operand =>
    if (op == .Bitcast || op == .Transmute) &&
        ((match source with | .FnItem _ => true | _ => false) ||
         (match destination with | .FnItem _ => true | _ => false)) then do
      let service ← match ctx.memoryService with
        | some service => pure service
        | none => Sem.throwTypeError "FnItem cast: original source layouts are absent"
      if service.model != ctx.byteModel then
        Sem.throwTypeError "FnItem cast: source layout target differs from evaluator target"
      let sourcePlan ← Sem.fromMemoryExcept (service.query source)
      let destinationPlan ← Sem.fromMemoryExcept (service.query destination)
      if sourcePlan.layout.size != destinationPlan.layout.size then
        Sem.throwTypeError "FnItem cast: byte extents differ"
      let value ← Sem.lookupValue operand
      Sem.rejectPartial value "FnItem cast"
      let image ← Sem.fromMemoryExcept
        (AggregateMemory.encode ctx.byteModel ctx.functionOrder sourcePlan value false)
      let state ← Sem.getState
      let result ← Sem.fromMemoryExcept
        (AggregateMemory.decode ctx.byteModel ctx.functionOrder state.memory destinationPlan image.bytes)
      pure (.value (some (← Sem.bindFresh result)))
    else stepInst inst ctx.byteModel
  | .ExtractElement ty array index =>
    let vid ← semExtractElementUsing (ctx.elementIndex index) ty array index
    pure (.value (some vid))
  | .InsertElement ty array index value =>
    let vid ← semInsertElementUsing (ctx.elementIndex index) ty array index value
    pure (.value (some vid))
  | .ArraySplat ty valueId =>
    let value ← Sem.lookupValue valueId
    Sem.rejectPartial value "ArraySplat"
    let elementId ← match ty with
      | .Array elementId _ => pure elementId
      | _ => Sem.throwTypeError "ArraySplat: not an array type"
    let elementTy ← match ctx.types elementId with
      | some ty => pure ty
      | none => Sem.throwUnsupported .enumDefTable "ArraySplat: element declaration is absent"
    let table ← match ctx.localTypes with
      | some table => pure table
      | none => Sem.throwUnsupported .ssaTypeTable "ArraySplat: original SSA declarations are absent"
    let sourceTy ← match table valueId with
      | some ty => pure ty
      | none => Sem.throwTypeError "ArraySplat: operand has no SSA declaration"
    if !(closureTyEq elementTy sourceTy) then
      Sem.throwTypeError "ArraySplat: operand type differs from the declared element type"
    -- Rust's expect_ty checks register identity, not byte-image validity or
    -- closure membership. Replication preserves the original value unchanged.
    stepInst inst ctx.byteModel
  | .Undef ty =>
    if isPartialLoadTy ty then stepInst inst ctx.byteModel
    else Sem.throwUB (nonpartialUndefMessage ty)
  | .BinOp op .Bool lhs rhs =>
    let vid ← semBoolBinOpInst op lhs rhs
    pure (.value (some vid))
  | .GlobalAddr global =>
    let vid ← semGlobalAddrInContext ctx global
    pure (.value (some vid))
  | .Load ty ptr strict align =>
    let vid ← match ctx.memoryServiceFor ty with
      | some service => AggregateMemory.load service ctx.functionOrder ty ptr strict align ctx.byteModel
      | none => semLoadUsing (fun mem bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder mem ty bytes) ty ptr strict align ctx.byteModel
    pure (.value (some vid))
  | .Store ty ptr value strict align =>
    match ctx.memoryServiceFor ty with
    | some service => AggregateMemory.store service ctx.functionOrder ty ptr value strict align ctx.byteModel
    | none => semStoreUsing (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty ptr value strict align ctx.byteModel
    pure (.value none)
  | .AtomicLoad ty ptr ordering =>
    let vid ← match ctx.memoryServiceFor ty with
      | some service => AggregateMemory.atomicLoad service ctx.functionOrder ty ptr ordering ctx.byteModel
      | none => semAtomicLoadUsing (fun mem bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder mem ty bytes) ty ptr ordering ctx.byteModel
    pure (.value (some vid))
  | .AtomicStore ty ptr value ordering =>
    match ctx.memoryServiceFor ty with
    | some service => AggregateMemory.atomicStore service ctx.functionOrder ty ptr value ordering ctx.byteModel
    | none => semAtomicStoreUsing (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty ptr value ordering ctx.byteModel
    pure (.value none)
  | .AtomicRMW op ty ptr value ordering =>
    let vid ← match ctx.memoryServiceFor ty with
      | some service => AggregateMemory.atomicRMW service ctx.functionOrder op ty ptr value ordering ctx.byteModel
      | none =>
        semAtomicRMWUsing
          (fun mem bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder mem ty bytes)
          (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) op ty ptr value ordering ctx.byteModel
    pure (.value (some vid))
  | .CmpXchg ty ptr expected desired _success _failure weak =>
    if weak then stepInst inst ctx.byteModel
    else
      let exchanged ← match ctx.memoryServiceFor ty with
        | some service => AggregateMemory.cmpXchgExchange service ctx.functionOrder ty ptr expected desired ctx.byteModel
        | none =>
          semCmpXchgExchangeUsing
            (fun mem bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder mem ty bytes)
            (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty ptr expected desired ctx.byteModel
      let ids ← Sem.bindFreshPair exchanged.1 (.bool exchanged.2)
      pure (.values [ids.1, ids.2])
  | .Const ty c@(.aggregate _) | .Const ty c@(.array _)
  | .Const ty c@(.splat _ _) | .Const ty c@(.vector _)
  | .Const ty c@(.sequence _) | .Const ty c@(.set _) | .Const ty c@(.record _)
  | .Const ty c@(.closure _ _) | .Const ty c@(.bytes _ _)
  | .Const ty c@(.fnItem _) =>
    -- Resolve every named element/field type before checking float width:
    -- the inline type alone cannot determine every named field/element leaf.
    if c.hasSymbolAddr then
      Sem.throwUnsupported .linkTimeAddress
        "Const: a link-time symbol address has no compile-time value"
    else
      match constValueAtWithDefs ctx ty c with
      | .ok v =>
        let vid ← Sem.bindFresh v
        pure (.value (some vid))
      | .error e => throw e
  | .MakeAggregate (.Array tid count) variant fields =>
    let lanes ← lookupLanes fields
    let value ← match makeArrayValueWithContext ctx tid count variant fields lanes with
      | .ok value => pure value
      | .error error => throw error
    pure (.value (some (← Sem.bindFresh value)))
  | .MakeAggregate ty@(.Enum _) variant fields
  | .MakeAggregate ty@(.Record _) variant fields =>
    let lanes ← lookupLanes fields
    let v ← match makeAggregateValueWithContext ctx ty variant lanes with
      | .ok v => pure v
      | .error e => throw e
    pure (.value (some (← Sem.bindFresh v)))
  | .MakeClosure cid fn captureIds =>
    let captures ← captureIds.mapM Sem.lookupValue
    let v ← match makeClosureValue ctx cid fn captures with
      | .ok v => pure v
      | .error e => throw e
    pure (.value (some (← Sem.bindFresh v)))
  | .ExtractField ty aggregateId field =>
    let held ← Sem.lookupValue aggregateId
    if let .typedClosure cid fn captures := held then
      let v ← match closureExtract ctx ty cid fn captures field with
        | .ok v => pure v
        | .error e => throw e
      return .value (some (← Sem.bindFresh v))
    let r ← stepInst inst ctx.byteModel
    match r with
    | .value (some vid) =>
      let v ← Sem.lookupValue vid
      match checkDeclaredField ctx aggregateId held field ty with
      | .error e => throw e
      | .ok () => pure ()
      if laneMatchesTy ty v ctx.byteModel then pure r
      else
        Sem.throwUB s!"ExtractField: lane {field} of value {aggregateId.index} is not at the access type"
    | other => pure other
  | .InsertField ty aggregateId field valueId =>
    -- The lookups `semInsertField` makes first, in the same order, so a
    -- missing operand is the same type error; its poison / lane-0 / bounds
    -- checks then run unchanged inside `stepInst`.
    let held ← Sem.lookupValue aggregateId
    let inserted ← Sem.lookupValue valueId
    if let .typedClosure cid fn captures := held then
      let v ← match closureInsert ctx ty cid fn captures field inserted with
        | .ok v => pure v
        | .error e => throw e
      return .value (some (← Sem.bindFresh v))
    if let some table := ctx.localTypes then
      Sem.rejectPartial held "InsertField"
      Sem.rejectPartial inserted "InsertField"
      let aggregateTy ← match table aggregateId with
        | some ty => pure ty
        | none => Sem.throwTypeError "InsertField: aggregate SSA declaration is absent"
      if !(closureTyEq aggregateTy ty) then
        Sem.throwTypeError "InsertField: aggregate result type differs from its declaration"
      -- Rust rejects a tag rewrite after checking the aggregate type,
      -- before inspecting the replacement's type against a payload lane.
      match ty, field with
      | .Enum _, 0 => Sem.throwUB "InsertField: cannot rewrite an enum discriminant"
      | _, _ => pure ()
    match getField held field with
    | some lane =>
      if let some table := ctx.localTypes then
        let insertedTy ← match table valueId with
          | some ty => pure ty
          | none => Sem.throwTypeError "InsertField: inserted SSA declaration is absent"
        match checkDeclaredField ctx aggregateId held field insertedTy with
        | .error e => throw e
        | .ok () => pure ()
      if lanesAgree lane inserted then stepInst inst ctx.byteModel
      else
        Sem.throwUB s!"InsertField: lane {field} of value {aggregateId.index} is not at the inserted value's type"
    | none => stepInst inst ctx.byteModel
  | _ => stepInst inst ctx.byteModel

/-!
## Unwinding as an exit (amendment D, Part 2; `docs/SPEC_RATIFICATIONS.md` §21)

The contextual evaluator runs under a named `PanicStrategy`. Under `.abort`
(the default) every construct keeps the ratified panic=abort projection
(`docs/ub-numerics-policy.md` §4): a failed check is the terminal panic, an
unwind edge is never taken, a landing pad reached without one and a `Resume`
are refused. Under `.unwind` a failed check RAISES, an unwinding propagates
out of every plain call, an invoke-family terminator catches it into its
landing pad, and `Resume` re-raises it. The strategy is an ARGUMENT of the
evaluator (not a context field), so an abort run and an unwind run share one
`EvalContext`: `Proofs/UnwindProps.lean` relates them instruction by
instruction (`stepNWithContext_abort_prefix`).
-/

/-- Which panic semantics the contextual evaluator runs (amendment D,
    Part 2). Mirrors Rust `trust_ir::interpret::PanicStrategy`. -/
inductive PanicStrategy where
  /-- The ratified panic=abort projection: unwind edges are never taken. -/
  | abort
  /-- Unwinding is an exit: a failed check raises an exception that the
      invoke-family terminators catch into their landing pads. -/
  | unwind
  deriving Repr, DecidableEq, BEq

/-- R1, the exception object: a fresh one-byte allocation placed by the one
    placement rule (`Memory.alloc` at size 1, alignment 1, no slack: the
    interpreter's `raise_exception`, `memory.alloc(1, 1)`), dead from birth
    (so every memory operation through it is undefined behaviour by the
    existing dead-allocation rules), recorded by its address with the
    allocation its pointer names and the panic outcome its raise reports.
    Returns its address, the exception value. -/
def semAllocException (msg : String) (site : Option PanicOutcomeSite) (model : ByteModel := .le64) : Sem Addr := do
  let s ← Sem.getState
  let id := AllocId.mk s.memory.nextAllocId
  Sem.checkTargetAllocation model s.memory 1 1 0
  let (base, mem) := s.memory.alloc 1 1 0 .rustHeap
  Sem.setState { s with
    memory := { mem with
      allocations := mem.allocations.map fun a =>
        if a.id == id then { a with alive := false } else a }
    exceptions := s.exceptions ++ [(base, id, msg, site)] }
  pure base

/-- R1, the raise: allocate the exception object, then start the unwinding. -/
def semRaise {α : Type} (msg : String) (site : Option PanicOutcomeSite) (model : ByteModel := .le64) : Sem α := do
  let exn ← semAllocException msg site model
  let s ← Sem.getState
  throw (.unwinding exn s)

/-- A failed body `Assert` under the strategy: `.abort` keeps the terminal
    panic; `.unwind` turns it into a raise (the panic outcome, operands and
    location already resolved exactly as under `.abort`, is what the
    exception records). Every other error, and success, pass unchanged. -/
def raiseIfUnwind (strat : PanicStrategy) (m : Sem InstrResult) (model : ByteModel := .le64) : Sem InstrResult :=
  match strat with
  | .abort => m
  | .unwind =>
    tryCatch m (fun e =>
      match e with
      | .panic msg site => semRaise msg site model
      | e => throw e)

trustIrDenseMatch
/-- A landing pad's `(isCleanup, clauses)`; `none` for any other
    instruction. -/
def Inst.padClauses : Inst → Option (Bool × List Nat)
  | .LandingPad isCleanup clauses => some (isCleanup, clauses)
  | _ => none

trustIrDenseMatch
/-- R4, U(e, d): enter the landing pad heading `dest` with exception `exn`.
    The exception's pointer is the one its raise recorded (an unwinding
    carrying an address no raise recorded is a malformed run, a type error,
    as in the interpreter). A clause other than 0 (a typed catch, or
    trust-cg's empty filter) is refused (`unsupported.typed_catch`); a
    catch-all clause 0 puts `(exn, its allocation, 1)` in hand; a cleanup pad
    puts `(exn, its allocation, 0)` in hand; a pad with no action
    re-propagates the unwinding out of this frame. The caller then continues
    at `dest` with no arguments. -/
def semEnterPad (cfg : CFG) (exn : Addr) (dest : BlockId) : Sem Unit := do
  match cfg dest with
  | none => Sem.throwTypeError (trustIrStringBuild s!"undefined block: {repr dest}")
  | some blk =>
    match blk.body.head?.bind Inst.padClauses with
    | some (isCleanup, clauses) => do
      let s ← Sem.getState
      match s.exceptions.find? (fun row => row.1 == exn) with
      | none => Sem.throwTypeError "an unwinding carries an exception this run never raised"
      | some (_, id, _, _) =>
        if clauses.any (· != 0) then
          Sem.throwUnsupported .typedCatch
            "landingpad: a typed catch clause needs a typeinfo model the format does not have"
        else if clauses.contains 0 then
          Sem.modifyState (fun s => { s with inHand := some (exn, id, 1) })
        else if isCleanup then
          Sem.modifyState (fun s => { s with inHand := some (exn, id, 0) })
        else
          throw (.unwinding exn s)
    | _ => Sem.throwTypeError "unwind destination does not begin with a landing pad"

/-- R5, a body `LandingPad` under the strategy. Under `.unwind` with an
    exception in hand it binds its two results to the exception object and
    the selector (`Ptr`, `I32`) and clears the hand; otherwise (`.abort`, or
    nothing in hand) it is today's refusal (`unsupported.host_unwind`). -/
def semLandingPadWith (strat : PanicStrategy) (ctx : EvalContext) (pad : Inst)
    (resultDests : List ValueId) : Sem Unit :=
  match strat with
  | .abort => do
    let r ← stepInstWithContext ctx pad
    ctx.bindInstructionResults pad r resultDests
  | .unwind => do
    let s ← Sem.getState
    match s.inHand with
    | some (exn, id, sel) => do
      Sem.setState { s with inHand := none }
      ctx.bindCallResults pad resultDests [.ptr exn (some id), .int 32 (sel : Int)]
    | none => do
      let r ← stepInstWithContext ctx pad
      ctx.bindInstructionResults pad r resultDests

/-- R6, `Resume` under `.unwind`: a pointer whose ADDRESS is a recorded
    exception object re-raises that exception, whatever its provenance (a
    stored and reloaded exception pointer, whose allocation is dead, is the
    same exception, as in the interpreter); any other value (a poison one
    included) is undefined behaviour. -/
def semResumeUnwind (exnId : ValueId) : Sem InstrResult := do
  let v ← Sem.lookupValue exnId
  let s ← Sem.getState
  match v with
  | .ptr a _ =>
    if s.exceptions.any (fun row => row.1 == a) then throw (.unwinding a s)
    else Sem.throwUB "Resume: the value is not an exception object a landing pad produced"
  | _ => Sem.throwUB "Resume: the value is not an exception object a landing pad produced"

/-- The terminator step under `.unwind`. A failing `AssertInvoke` raises and
    is caught by itself: its exception enters the pad at `unwindDest` (R4)
    and control continues there with no arguments. `Resume` re-raises (R6).
    Every other terminator steps exactly as under `.abort`. -/
def stepTermUnwind (cfg : CFG) (term : Inst) (model : ByteModel := .le64) : Sem InstrResult :=
  match term with
  | .AssertInvoke _ _ _ _ _ unwindDest =>
    tryCatch (stepInst term model) (fun e =>
      match e with
      | .panic msg site => do
        let exn ← semAllocException msg site model
        semEnterPad cfg exn unwindDest
        pure (.terminator (.Continue unwindDest []))
      | e => throw e)
  | .Resume exnId => semResumeUnwind exnId
  | _ => stepInst term model

/-- Contextual function/closure application shares its guard across both panic
    strategies. The fallback retains raw-pointer and other term rules. -/
def closureTermWithContext (ctx : EvalContext) (callDepth : Nat) (term : Inst)
    (fallback : Sem InstrResult) : Sem InstrResult :=
  match term with
  | .CallIndirect valueId sig argIds conv => do
    let value ← Sem.lookupValue valueId
    let _ ← Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx valueId value)
    match value with
    | .nullPtr => Sem.throwTypeError "CallIndirect: null function pointer"
    | .fnItem target =>
      match callDepth with
      | 0 => throw SemError.outOfFuel
      | _ + 1 => do
        let fn ← Sem.fromMemoryExcept (functionItemCall ctx target sig conv)
        let args ← argIds.mapM Sem.lookupValue
        let _ ← Sem.fromMemoryExcept (resolveFunctionItemBody ctx fn)
        pure (.terminator (.CallReq fn args))
    | .fnDef held target =>
      let args ← argIds.mapM Sem.lookupValue
      match callDepth with
      | 0 => throw SemError.outOfFuel
      | _ + 1 => do
        let fn ← match functionCallWithConvention ctx held target sig conv with
          | .ok fn => pure fn
          | .error e => throw e
        pure (.terminator (.CallReq fn args))
    | .typedClosure cid fn captures =>
      let args ← argIds.mapM Sem.lookupValue
      match callDepth with
      | 0 => throw SemError.outOfFuel
      | _ + 1 => do
        let (target, physicalArgs) ← match closureCall ctx cid fn captures sig args conv with
          | .ok call => pure call
          | .error e => throw e
        pure (.terminator (.CallReq target physicalArgs))
    | _ => fallback
  | .InvokeIndirect valueId sig argIds conv normalDest normalArgs unwindDest => do
    let value ← Sem.lookupValue valueId
    let _ ← Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx valueId value)
    match value with
    | .nullPtr => Sem.throwTypeError "InvokeIndirect: null function pointer"
    | .fnItem target =>
      match callDepth with
      | 0 => throw SemError.outOfFuel
      | _ + 1 => do
        let fn ← Sem.fromMemoryExcept (functionItemCall ctx target sig conv)
        let args ← argIds.mapM Sem.lookupValue
        let _ ← Sem.fromMemoryExcept (resolveFunctionItemBody ctx fn)
        pure (.terminator (.InvokeReq fn args normalDest normalArgs unwindDest))
    | .fnDef held target =>
      let args ← argIds.mapM Sem.lookupValue
      match callDepth with
      | 0 => throw SemError.outOfFuel
      | _ + 1 => do
        let fn ← match functionCallWithConvention ctx held target sig conv with
          | .ok fn => pure fn
          | .error e => throw e
        pure (.terminator (.InvokeReq fn args normalDest normalArgs unwindDest))
    | _ => fallback
  | _ => fallback

/-- The strategy selects only the existing fallback. Closure argument
    resolution itself neither allocates nor changes unwind handling. -/
def stepTermWithContext (ctx : EvalContext) (callDepth : Nat) (cfg : CFG)
    (term : Inst) (strat : PanicStrategy) : Sem InstrResult :=
  match strat with
  | .abort => closureTermWithContext ctx callDepth term (stepInst term ctx.byteModel)
  | .unwind => closureTermWithContext ctx callDepth term (stepTermUnwind cfg term ctx.byteModel)

trustIrDenseMatch
/-- R3, the catch of an invoke-family call. `.abort` never catches (the
    callee's outcome is always `inl`); `.unwind` catches an unwinding out of
    the callee as `inr (exception, state at the throw)`. Every other error
    propagates. -/
def invokeCatch (strat : PanicStrategy) (m : Sem (List Value)) :
    Sem (List Value ⊕ (Addr × MachineState)) :=
  match strat with
  | .abort => do
    let retVals ← m
    pure (.inl retVals)
  | .unwind =>
    tryCatch (do
        let retVals ← m
        pure (.inl retVals))
      (fun e =>
        match e with
        | .unwinding exn st => pure (.inr (exn, st))
        | e => throw e)

/-- R7, the entry: under `.unwind` an unwinding that escapes the entry is
    reported as the panic its raise recorded (the same outcome an `.abort`
    run reports at the first raise). -/
def exitUnwinding (strat : PanicStrategy) (m : Sem (List Value)) : Sem (List Value) :=
  match strat with
  | .abort => m
  | .unwind =>
    tryCatch m (fun e =>
      match e with
      | .unwinding exn st =>
        match st.exceptions.find? (fun row => row.1 == exn) with
        | some (_, _, msg, site) => throw (.panic msg site)
        | none =>
          Sem.throwTypeError "an unwinding escaped the entry with no recorded exception object"
      | e => throw e)

/-- The actual direct-call lookup, shared by body calls, tail calls and
    invokes. Declaration status affects only the named missing-body refusal;
    it never authorizes execution of a declaration. -/
def EvalContext.lookupDirectCallee (ctx : EvalContext) (id : FuncId)
    (declaredMessage missingMessage : String) : Sem EvalFunction :=
  match ctx.functions id with
  | some function => pure function
  | none =>
    if ctx.declared id then
      Sem.throwUnsupported .interproceduralCall declaredMessage
    else Sem.throwTypeError missingMessage

/-- Header lookup does not demand an executable body. The optional fallback
    is a view of a genuinely supplied function in a manual context. Known
    malformed original headers propagate their error before iteration. -/
def EvalContext.lookupFunctionHeader (ctx : EvalContext) (id : FuncId) : Sem FunctionHeader :=
  match ctx.functionHeaders id with
  | some result => Sem.fromMemoryExcept result
  | none =>
    match ctx.functions id with
    | some function => pure function.header
    | none => Sem.throwTypeError "SeqMap: original function header is absent"

def FunctionHeader.matches (header : FunctionHeader) (function : EvalFunction) : Bool :=
  closureTyListEq header.signature.params function.body.paramTys &&
    closureTyListEq header.signature.returns function.body.returnTys &&
    header.signature.isVararg == function.body.isVararg &&
    header.callingConv == function.callingConv

def EvalContext.loadMemoryValue (ctx : EvalContext) (ty : Ty) (pointer : Value)
    (strict : Bool := false) : Sem Value :=
  match ctx.memoryServiceFor ty with
  | some service => AggregateMemory.loadValue service ctx.functionOrder ty pointer strict none ctx.byteModel
  | none =>
    semLoadValueUsing
      (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
      ty pointer strict none ctx.byteModel

def EvalContext.storeMemoryValue (ctx : EvalContext) (ty : Ty) (pointer value : Value)
    (strict : Bool := false) : Sem Unit :=
  match ctx.memoryServiceFor ty with
  | some service => AggregateMemory.storeValue service ctx.functionOrder ty pointer value strict none ctx.byteModel
  | none =>
    semStoreValueUsing (scalarMemoryLayout ctx.byteModel)
      (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty pointer value strict none ctx.byteModel

/-- Original SSA/element declarations retain nominal identity and signedness
    where values do not. A populated table missing a row never falls back to
    a carrier guess. Manual scalar contexts retain their explicit old model. -/
def EvalContext.checkSeqMapElement (ctx : EvalContext) (inst : Inst)
    (expected : Ty) (value : Value) : Except SemError Unit := do
  match ctx.memoryService with
  | some _ =>
    let sequence ← match inst with
      | .SeqMap _ sequence _ => pure sequence
      | _ => throw (.typeError "SeqMap: request lacks its original instruction")
    let table ← match ctx.localTypes with
      | some table => pure table
      | none => throw (.unsupported .ssaTypeTable "SeqMap: original SSA declarations are absent")
    let declared ← match table sequence with
      | some (.Sequence element) =>
        match ctx.types element with
        | some ty => pure ty
        | none => throw (.unsupported .enumDefTable "SeqMap: declared element type is absent")
      | some _ => throw (.typeError "SeqMap: operand is not declared as a sequence")
      | none => throw (.typeError "SeqMap: operand SSA declaration is absent")
    if closureTyEq declared expected then pure ()
    else throw (.typeError "SeqMap: element source type differs from the function's pointee type")
  | none =>
    let typeMatches := match expected, value with
      | .Bool, .bool _ => true
      | .Func expected, .fnDef held _ => expected == held
      | .Func _, .nullPtr => true
      | ty, .int width _ => ty.isInteger && ty.bitWidthFor ctx.byteModel == some width
      | ty, .float _ => ty.isFloat
      | _, _ => false
    if typeMatches then pure ()
    else throw (.typeError "SeqMap: element does not match the function's pointee type")

-- The heartbeat bump covers the `SeqMap` element-application arm below: the
-- per-element runner (alloc → write → call → read-back inside a `for`) makes
-- `stepNWithContext` one large elaborated definition. (Raised 1.6M → 3.2M at
-- v25: the four B1 Ty ctors — Isize/Usize/Char/Error — enlarge every Ty
-- match this definition elaborates through. Raised 3.2M → 6.4M by amendment D,
-- Part 2: the strategy-dependent arms — body `Assert` / `LandingPad`, the
-- terminator step, the invoke-family catch and pad entry.)
set_option maxHeartbeats 6400000 in
/-- Multi-step evaluation with an interprocedural context.  Calls are executed
    either as tail call-transfer terminators or as body instructions with
    explicit result destinations mirroring Rust `InstrNode.results`. -/
def stepNWithContext (ctx : EvalContext) (fuel : Nat) (callDepth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value)
    (strat : PanicStrategy := .abort) : Sem (List Value) := do
  match fuel with
  | 0 => throw SemError.outOfFuel
  | fuel + 1 =>
    match cfg pc with
    | none => Sem.throwTypeError s!"undefined block: {repr pc}"
    | some blk => do
      -- Amendment D (§20 rule 3): every drop of the block is resolved
      -- through the context's drop-glue table BEFORE dispatch, so a resolved
      -- drop runs the `Call` / `Invoke` rules below verbatim, and an
      -- unresolved one reaches the bare `stepInst`, which refuses it.
      let block := ctx.resolveBlock blk
      let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (block.params.map (·.snd)) args)
      bindBlockParamsChecked block.params args
      for bodyInst in bodyInstsWithResultDests block.body block.bodyResultDests do
        let inst := bodyInst.fst
        let resultDests := bodyInst.snd
        match inst with
        | .Call calleeId argIds => do
          let callArgs ← argIds.mapM Sem.lookupValue
          match callDepth with
          | 0 => throw SemError.outOfFuel
          | callDepth + 1 => do
            let callee ← ctx.lookupDirectCallee calleeId
              "Call: callee is a bodyless declaration" "Call: undefined function"
            requireUntypedAbi callee.body.abi
            match checkCallArity callArgs callee.body.paramTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("Call: " ++ msg)
            Sem.rejectPoisonValues callArgs "Call arguments"
            let callerState ← Sem.getState
            let frame := saveFrame callerState none
            Sem.setState
              { callerState with locals := ValueMap.empty, nextValueId := 0 }
            let retVals ← stepNWithContext (ctx.forFunction callee) fuel callDepth
              callee.cfg callee.entryBlock callArgs strat
            match checkReturnArity retVals callee.body.returnTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("Call: " ++ msg)
            Sem.rejectPoisonValues retVals "Call returns"
            let calleeState ← Sem.getState
            Sem.setState (restoreFrame calleeState frame [])
            ctx.bindCallResults inst resultDests retVals
        | .CallIndirect calleeValId sig argIds conv => do
          let calleeVal ← Sem.lookupValue calleeValId
          let _ ← Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx calleeValId calleeVal)
          -- Validate a pointer before argument lookup as before. A nominal
          -- closure is resolved only after the same call-depth boundary.
          let addr ← match calleeVal with
            | .ptr a _ => pure a
            | .fnDef _ _ => pure 0
            | .fnItem _ => pure 0
            | .typedClosure _ _ _ => pure 0
            | .nullPtr => Sem.throwTypeError "CallIndirect: null function pointer"
            | _ => Sem.throwTypeError "CallIndirect: callee is not a pointer or typed closure"
          let args ← match calleeVal with
            | .fnItem _ => pure []
            | _ => argIds.mapM Sem.lookupValue
          match callDepth with
          | 0 => throw SemError.outOfFuel
          | callDepth + 1 => do
            let (calleeId, callArgs) ← match calleeVal with
              | .fnItem target =>
                match functionItemCall ctx target sig conv with
                | .ok fn => do pure (fn, ← argIds.mapM Sem.lookupValue)
                | .error e => throw e
              | .fnDef held target =>
                match functionCallWithConvention ctx held target sig conv with
                | .ok fn => pure (fn, args)
                | .error e => throw e
              | .typedClosure cid fn captures =>
                match closureCall ctx cid fn captures sig args conv with
                | .ok call => pure call
                | .error e => throw e
              | _ => do
                let calleeId ← match ctx.funcPtrs addr with
                  | some fid => pure fid
                  | none => Sem.throwUB "CallIndirect: invalid function pointer"
                let sigDef ← match ctx.funcTys sig with
                  | some def_ => pure def_
                  | none => Sem.throwTypeError "CallIndirect: undefined function type"
                let callee ← match ctx.functions calleeId with
                  | some f => pure f
                  | none => Sem.throwTypeError "CallIndirect: undefined function"
                requireUntypedAbi sigDef.abi
                match checkIndirectSignature sigDef callee.body with
                | .ok () => pure ()
                | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
                pure (calleeId, args)
            let callee ← match ctx.functions calleeId with
              | some f => pure f
              | none =>
                match calleeVal with
                | .fnItem _ => Sem.fromMemoryExcept (resolveFunctionItemBody ctx calleeId)
                | _ => Sem.throwTypeError "CallIndirect: undefined function"
            requireUntypedAbi callee.body.abi
            match checkCallArity callArgs callee.body.paramTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
            Sem.rejectPoisonValues callArgs "CallIndirect arguments"
            let callerState ← Sem.getState
            let frame := saveFrame callerState none
            Sem.setState
              { callerState with locals := ValueMap.empty, nextValueId := 0 }
            let retVals ← stepNWithContext (ctx.forFunction callee) fuel callDepth
              callee.cfg callee.entryBlock callArgs strat
            match checkReturnArity retVals callee.body.returnTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
            Sem.rejectPoisonValues retVals "Call returns"
            if let .typedClosure _ _ _ := calleeVal then
              for (t, v) in callee.body.returnTys.zip retVals do
                match checkClosureValue ctx t v with
                | .ok () => pure ()
                | .error e => throw e
            let calleeState ← Sem.getState
            Sem.setState (restoreFrame calleeState frame [])
            ctx.bindCallResults inst resultDests retVals
        -- R1 (amendment D, Part 2): a failed check raises under `.unwind`.
        -- An `Assert` never yields a terminator, so binding its (empty)
        -- result is exactly the generic arm below.
        | .Assert _ _ _ => do
          let instResult ← raiseIfUnwind strat (stepInstWithContext ctx inst) ctx.byteModel
          ctx.bindInstructionResults inst instResult resultDests
        -- R5: a landing pad binds the exception in hand under `.unwind`.
        | .LandingPad isCleanup clauses =>
          semLandingPadWith strat ctx (.LandingPad isCleanup clauses) resultDests
        | _ => do
          let instResult ← stepInstWithContext ctx inst
          match instResult with
          | .value _ => ctx.bindInstructionResults inst instResult resultDests
          | .values _ => ctx.bindInstructionResults inst instResult resultDests
          | .terminator (.SeqMapReq fwdId elems) => do
            -- SeqMap element application (give-back loop instruction):
            -- apply the element function `fwd : fn(&mut elem)` to every
            -- element via the standard call machinery. ONE call-depth level
            -- bounds the WHOLE map — the per-element calls are sequential,
            -- so depth bounds nesting, not sequence length (do not burn
            -- depth per element). Each element round-trips through a fresh
            -- per-element memory cell: alloc → write element → call
            -- fwd(&mut cell) → read the mutated element back through its
            -- source-derived typed image. The original header is checked
            -- even for an empty map; layout, cells and executable bodies
            -- are needed only when an element is actually applied.
            match callDepth with
            | 0 => throw SemError.outOfFuel
            | callDepth + 1 => do
              let header ← ctx.lookupFunctionHeader fwdId
              requireUntypedAbi header.signature.abi
              if header.signature.isVararg then
                Sem.throwTypeError "SeqMap: element function must not be variadic"
              let elemTy ← match header.signature.params, header.signature.returns with
                | [Ty.RefMut element], [] => pure element
                | _, _ => Sem.throwTypeError "SeqMap: element function must have signature fn(&mut elem)"
              let mut mapped : List Value := []
              for elem in elems do
                Sem.fromMemoryExcept (ctx.checkSeqMapElement inst elemTy elem)
                -- Empty maps perform none of these per-element operations.
                let layout ← Sem.fromMemoryExcept (ctx.memoryLayout elemTy)
                let before ← Sem.getState
                Sem.checkTargetAllocation ctx.byteModel before.memory layout.size layout.alignment 0
                let (cellAddr, memory) := before.memory.alloc layout.size layout.alignment 0 .rustStack
                let allocId : AllocId := ⟨before.memory.nextAllocId⟩
                Sem.setState { before with memory := memory, permissions := before.permissions.set allocId .owned }
                let pointer := Value.ptr cellAddr (some allocId)
                ctx.storeMemoryValue elemTy pointer elem
                if let some error := ctx.functionErrors fwdId then throw error
                let callee ← ctx.lookupDirectCallee fwdId
                  "SeqMap: element function is declared without a body" "SeqMap: undefined element function"
                if !(header.matches callee) then
                  Sem.throwTypeError "SeqMap: original header does not match executable function metadata"
                requireUntypedAbi callee.body.abi
                let callerState ← Sem.getState
                let frame := saveFrame callerState none
                Sem.setState { callerState with locals := ValueMap.empty, nextValueId := 0 }
                let retVals ← stepNWithContext (ctx.forFunction callee) fuel callDepth
                  callee.cfg callee.entryBlock [pointer] strat
                match checkReturnArity retVals callee.body.returnTys with
                | .ok () => pure ()
                | .error msg => Sem.throwTypeError ("SeqMap: " ++ msg)
                Sem.rejectPoisonValues retVals "SeqMap returns"
                let calleeState ← Sem.getState
                Sem.setState (restoreFrame calleeState frame [])
                let newElem ← ctx.loadMemoryValue elemTy pointer
                mapped := mapped ++ [newElem]
              ctx.bindCallResults inst resultDests [Value.sequence mapped]
          | .terminator _ =>
            Sem.throwTypeError "body instruction produced a terminator"
      -- Under `.unwind` a failing `AssertInvoke` enters its pad and `Resume`
      -- re-raises (`stepTermUnwind`); under `.abort` the bare step.
      let termResult ← stepTermWithContext ctx callDepth cfg block.terminator strat
      let result ← match termResult with
        | .terminator sr => pure sr
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      match result with
      | .Ret values =>
        if let some expected := ctx.functionReturnTypes then
          let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected values)
          pure values
        else pure values
      | .Stuck => Sem.throwUB "reached unreachable"
      | .Continue nextPc nextArgs =>
        stepNWithContext ctx fuel callDepth cfg nextPc nextArgs strat
      | .CallReq calleeId callArgs =>
        match callDepth with
        | 0 => throw SemError.outOfFuel
        | callDepth + 1 => do
          let callee ← ctx.lookupDirectCallee calleeId
            "Call: callee is a bodyless declaration" "Call: undefined function"
          requireUntypedAbi callee.body.abi
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Call: " ++ msg)
          Sem.rejectPoisonValues callArgs "Call arguments"
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          let retVals ← stepNWithContext (ctx.forFunction callee) fuel callDepth
            callee.cfg callee.entryBlock callArgs strat
          match checkReturnArity retVals callee.body.returnTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Call: " ++ msg)
          Sem.rejectPoisonValues retVals "Call returns"
          match block.terminator with
          | .CallIndirect valueId _ _ _ =>
            match frame.locals valueId with
            | some (.typedClosure _ _ _) =>
              for (t, v) in callee.body.returnTys.zip retVals do
                match checkClosureValue ctx t v with
                | .ok () => pure ()
                | .error e => throw e
            | _ => pure ()
          | _ => pure ()
          let calleeState ← Sem.getState
          Sem.setState (restoreFrame calleeState frame [])
          pure retVals
      | .CallIndirectReq addr sig callArgs =>
        match callDepth with
        | 0 => throw SemError.outOfFuel
        | callDepth + 1 => do
          let calleeId ← match ctx.funcPtrs addr with
            | some fid => pure fid
            | none => Sem.throwUB "CallIndirect: invalid function pointer"
          let sigDef ← match ctx.funcTys sig with
            | some def_ => pure def_
            | none => Sem.throwTypeError "CallIndirect: undefined function type"
          let callee ← match ctx.functions calleeId with
            | some f => pure f
            | none => Sem.throwTypeError "CallIndirect: undefined function"
          requireUntypedAbi sigDef.abi
          match checkIndirectSignature sigDef callee.body with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
          requireUntypedAbi callee.body.abi
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
          Sem.rejectPoisonValues callArgs "CallIndirect arguments"
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          let retVals ← stepNWithContext (ctx.forFunction callee) fuel callDepth
            callee.cfg callee.entryBlock callArgs strat
          match checkReturnArity retVals callee.body.returnTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
          Sem.rejectPoisonValues retVals "Call returns"
          let calleeState ← Sem.getState
          Sem.setState (restoreFrame calleeState frame [])
          pure retVals
      | .InvokeReq calleeId callArgs normalDest normalArgIds unwindDest =>
        -- Mirrors interpret.rs Inst::Invoke: run the call exactly like
        -- CallReq, bind the callee's returns to the invoke node's result
        -- destinations, THEN evaluate the normal-edge arguments (they may
        -- reference those results) and take the normal edge. Under `.abort`
        -- the unwind destination is never taken; under `.unwind` an
        -- unwinding out of the callee enters its pad (R3, R4).
        match callDepth with
        | 0 => throw SemError.outOfFuel
        | innerDepth + 1 => do
          let callee ← ctx.lookupDirectCallee calleeId
            "Invoke: callee is a bodyless declaration" "Invoke: undefined function"
          requireUntypedAbi callee.body.abi
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
          Sem.rejectPoisonValues callArgs "Call arguments"
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          -- R3 (amendment D, Part 2): under `.unwind` an unwinding out of the
          -- callee is caught here; under `.abort` the outcome is always `inl`.
          let outcome ← invokeCatch strat (stepNWithContext (ctx.forFunction callee) fuel innerDepth
            callee.cfg callee.entryBlock callArgs strat)
          match outcome with
          | .inl retVals => do
            match checkReturnArity retVals callee.body.returnTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
            Sem.rejectPoisonValues retVals "Call returns"
            let calleeState ← Sem.getState
            Sem.setState (restoreFrame calleeState frame [])
            ctx.bindCallResults block.terminator block.terminatorResultDests retVals
            let edgeArgs ← normalArgIds.mapM Sem.lookupValue
            -- The normal edge continues the CALLER: depth bounds NESTING only
            -- (mirrors interpret.rs, where the caller resumes at its own depth
            -- after Step::Jump), so the continuation runs at the UNdecremented
            -- depth — an Invoke must not permanently burn depth budget.
            stepNWithContext ctx fuel (innerDepth + 1) cfg normalDest edgeArgs strat
          | .inr (exn, st) => do
            -- The caller's frame back over the memory the unwinding left; no
            -- result binds and the normal-edge arguments are not evaluated.
            Sem.setState (restoreFrame st frame [])
            semEnterPad cfg exn unwindDest
            stepNWithContext ctx fuel (innerDepth + 1) cfg unwindDest [] strat
      | .InvokeIndirectReq addr sig callArgs normalDest normalArgIds unwindDest =>
        -- Amendment D, Part 2: `CallIndirect`'s unwinding twin (mirrors
        -- interpret.rs Inst::InvokeIndirect): resolve and check the callee
        -- exactly as `CallIndirectReq`, run it, bind its returns to the
        -- node's result destinations, then evaluate the normal-edge
        -- arguments and take the normal edge at the CALLER's (undecremented)
        -- depth, exactly as `InvokeReq`, whose unwind rules it shares.
        match callDepth with
        | 0 => throw SemError.outOfFuel
        | innerDepth + 1 => do
          let calleeId ← match ctx.funcPtrs addr with
            | some fid => pure fid
            | none => Sem.throwUB "InvokeIndirect: invalid function pointer"
          let sigDef ← match ctx.funcTys sig with
            | some def_ => pure def_
            | none => Sem.throwTypeError "InvokeIndirect: undefined function type"
          let callee ← match ctx.functions calleeId with
            | some f => pure f
            | none => Sem.throwTypeError "InvokeIndirect: undefined function"
          match checkIndirectSignature sigDef callee.body with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("InvokeIndirect: " ++ msg)
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("InvokeIndirect: " ++ msg)
          Sem.rejectPoisonValues callArgs "InvokeIndirect arguments"
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          let outcome ← invokeCatch strat (stepNWithContext (ctx.forFunction callee) fuel innerDepth
            callee.cfg callee.entryBlock callArgs strat)
          match outcome with
          | .inl retVals => do
            match checkReturnArity retVals callee.body.returnTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("InvokeIndirect: " ++ msg)
            Sem.rejectPoisonValues retVals "Call returns"
            let calleeState ← Sem.getState
            Sem.setState (restoreFrame calleeState frame [])
            ctx.bindCallResults block.terminator block.terminatorResultDests retVals
            let edgeArgs ← normalArgIds.mapM Sem.lookupValue
            stepNWithContext ctx fuel (innerDepth + 1) cfg normalDest edgeArgs strat
          | .inr (exn, st) => do
            Sem.setState (restoreFrame st frame [])
            semEnterPad cfg exn unwindDest
            stepNWithContext ctx fuel (innerDepth + 1) cfg unwindDest [] strat
      | .SeqMapReq _ _ =>
        -- A SeqMap in terminator position is malformed IR (it is not a
        -- terminator; Rust-side validation rejects it). Fail closed.
        Sem.throwTypeError "SeqMap is not a terminator"

/-- Evaluate a function by FuncId through an interprocedural context. -/
def evalFunctionInContext (ctx : EvalContext) (entryFunc : FuncId)
    (args : List Value) (fuel : Nat := 10000) (strat : PanicStrategy := .abort) :
    Sem (List Value) := do
  let func ← match ctx.functions entryFunc with
    | some f => pure f
    | none => Sem.throwTypeError "evalFunctionInContext: undefined entry function"
  requireUntypedAbi func.body.abi
  match checkCallArity args func.body.paramTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("evalFunctionInContext: " ++ msg)
  -- The entry is a call boundary too (Rust `execute_function_inner` checks
  -- the entry's arguments and returns like any callee's): poison may not
  -- enter or leave it.
  Sem.rejectPoisonValues args "Call arguments"
  let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx func.body.paramTys args)
  -- R7: under `.unwind` an escaping unwinding is the panic its raise recorded.
  let retVals ← exitUnwinding strat
    (stepNWithContext (ctx.forFunction func) fuel ctx.maxCallDepth func.cfg func.entryBlock args strat)
  Sem.rejectPoisonValues retVals "Call returns"
  let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx func.body.returnTys retVals)
  pure retVals

end TrustIr

#trustIrAxiomsPinned TrustIr.EvalContext.bindInstructionResults == [] modern []
#trustIrAxiomsExact TrustIr.bindResultDests == []
#trustIrAxiomsExact TrustIr.bindBlockParams == []
#trustIrAxiomsExact TrustIr.bindBlockParamsChecked == []

#trustIrAxiomsExact TrustIr.Inst.padClauses == []
#trustIrAxiomsExact TrustIr.semEnterPad == []

#trustIrAxiomsExact TrustIr.invokeCatch == []
