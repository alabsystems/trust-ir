-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- WS8.15 (remainder): behaviour refinement under the INTERPROCEDURAL
-- evaluator `stepNWithContext`, where calls are executed.

import TrustIr.Proofs.TransformCorrectness
import TrustIr.Proofs.ConstantTypingEquations
import TrustIr.Proofs.GenericCoroPrefixLayer

namespace TrustIr

/-!
# Behaviour refinement in a module context (WS8.15, remainder)

`behaviour_refines` (`TransformCorrectness.lean`) is stated over `stepN`, the
intraprocedural evaluator, where every call is an `unsupported` behaviour. A
refinement proved there says nothing about a run that executes its calls.
This module states the same notion over `stepNWithContext`.

## Definitions

* `BehavesIn ctx strat cfg pc args s o`: `o` is a behaviour of the function
  body `cfg` run by `stepNWithContext` in the module context `ctx`. Both
  resources the evaluator bounds, block fuel and call depth, are quantified:
  a terminating outcome is exhibited at some `(fuel, depth)`, and `diverges`
  is `outOfFuel` at EVERY pair. Call depth is a resource, not a behaviour,
  exactly as fuel is.
* `behaviour_refines_in strat t`: in every module context, for every UB-free
  source run, every behaviour of `t cfg` is a behaviour of `cfg`. The
  transform rewrites ONE function body (the entry activation); the functions
  it calls are the context's, unchanged.
* `BehavesFn` / `program_refines`: the same at the whole-program level, over
  `evalFunctionInContext` with the context's `maxCallDepth` quantified.

## What holds

* `behavesIn_nonempty`, `id_refines_in`, `compose_refines_in`, and the
  program-level `behavesFn_nonempty`, `id_program_refines`,
  `compose_program_refines`.
* `unreachableToReturn_refines_in`: the UB-exploiting rewrite is a refinement
  under panic=abort with calls executed (UB is top here too).
* `ProgramRefinement.lean` builds on the local congruences here to prove
  `unreachableToReturn_program_refines`: the same rewrite in every function
  body, with recursive callee execution, SeqMap and all behaviours covered.
* `inlining_outcome` / `inlining_behaves_iff`: the frame-discipline form of
  inlining at the BEHAVIOUR level. The behaviours of a resolved `Call` are
  exactly the behaviours of the callee body run inline on a fresh frame,
  mapped through the call boundary (`callBoundary`): divergence and every
  trap verbatim, a return checked for arity and poison and given back the
  caller's frame.
* `withMaxCallDepth_program_refines`: changing the context's call-depth
  budget is a refinement, because depth is quantified.

## What does not hold

* `assertElim_not_refines_in`: trap removal is refused here too (the
  negative twin).
* `callRetarget_refines` and `callRetarget_not_refines_in`: retargeting a
  call is invisible to the intraprocedural notion, where a call is
  `unsupported` whatever it calls, and is refused once calls are executed. So
  `behaviour_refines` does not imply `behaviour_refines_in`
  (`behaviour_refines_not_imp_refines_in`): an intraprocedural proof does
  not carry over to a body that calls.
* `loop_not_refines_in`, `panicToLoop_not_refines_in` and
  `recursion_not_refines_in`: divergence stays observable with calls
  executed, and unbounded recursion (out of depth at every budget) IS
  divergence, so a transform may not introduce either into a source that
  terminates or traps.
* `withMaxCallDepth_not_fixedDepth_refines`: the mutant that reads the depth
  budget from the context instead of quantifying it refuses a depth-only
  change, which `withMaxCallDepth_program_refines` admits.

## Residue (not stated here)

* Strategy `.unwind`: behaviour/program refinement theorems remain at
  `.abort`, the ratified panic=abort projection (`docs/ub-numerics-policy.md`
  §4). The local terminator/header congruences below cover both strategies;
  they do not lift whole-program unwind behaviour.
* A general lift for arbitrary CFG relations. `ProgramRefinement.lean`
  proves the concrete whole-program `unreachableToReturn` rewrite under
  `.abort`; the local instruction congruences here alone do not establish
  recursive callee-body or control-flow preservation for other transforms.
* The splice form of inlining (`TransformCorrectness.lean`, Future work
  item 4): it needs an SSA value-id / block-id renaming and a per-instruction
  equivariance lemma for `stepInst`, which the model does not have.
-/

-- =================================================================
-- Constant lowering is independent of function bodies and resource budgets
-- =================================================================

/-- Replacing every executable function leaves constant lowering unchanged,
    including its errors. The source data tables and target model still come
    from the original context; changing those is not licensed by this fact. -/
theorem constValueAtWithDefs_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (ty : Ty) (c : Constant) :
    constValueAtWithDefs { ctx with functions := functions } ty c =
      constValueAtWithDefs ctx ty c := by
  rfl

/-- The call-depth setting cannot change the denotation of a constant. This
    includes nested nominal aggregates and closures and every refusal, rather
    than only successful scalar constants. -/
theorem constValueAtWithDefs_withMaxCallDepth (ctx : EvalContext)
    (depth : Nat) (ty : Ty) (c : Constant) :
    constValueAtWithDefs { ctx with maxCallDepth := depth } ty c =
      constValueAtWithDefs ctx ty c := by
  rfl

/-- Source-order code words belong to memory serialization, never to pure
    constant construction, including nested constants and every refusal. -/
theorem constValueAtWithDefs_withFunctionOrder (ctx : EvalContext)
    (order : FunctionAddressOrder) (ty : Ty) (c : Constant) :
    constValueAtWithDefs { ctx with functionOrder := order } ty c =
      constValueAtWithDefs ctx ty c := by
  rfl

/-- Function values have no scalar poison carrier in the reference evaluator;
    the contextual instruction refuses at construction, even if unused. -/
theorem undefFunctionInContext_is_ub (ctx : EvalContext) (signature : FuncTyId)
    (state : MachineState) :
    Sem.run (stepInstWithContext ctx (.Undef (.Func signature))) state =
      .error (.ub "Undef of function type is not executable (function poison unmodelled)") := rfl

/-- The actual contextual Const instruction has the same state transition
    and errors after replacing the executable-function table. Symbol-address
    and unresolved-width refusals keep their existing order and messages. -/
theorem stepInstWithContext_const_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (ty : Ty) (c : Constant) :
    stepInstWithContext { ctx with functions := functions } (.Const ty c) =
      stepInstWithContext ctx (.Const ty c) := by
  cases c <;> simp only [stepInstWithContext, constValueAtWithDefs_withFunctions]

set_option smartUnfolding false in
set_option maxHeartbeats 2000000 in
/-- A typed uniform array resolves its element type before constructing
    lanes. The statement is symbolic in both the literal and the length;
    `Value.intAt` retains exactly the authored eight-bit residue. -/
theorem constValueAtWithDefs_splat_i8 (ctx : EvalContext) (element : TyId)
    (count : Nat) (literal : Int) (hType : ctx.types element = some .I8) :
    constValueAtWithDefs ctx (.Array element count) (.splat (.int literal) count) =
      .ok (.array (CompactArray.Packed.uniform count (Value.intAt 8 literal))) := by
  change ctx.valueSource.ty element = some .I8 at hType
  unfold constValueAtWithDefs
  rw [constValueAtWithDefsIn_splat_eq]
  simp only [constPointerFormsSupported, Bool.not_true, Bool.false_eq_true,
    bne_self_eq_false, ↓reduceIte, EvalContext.constantContext, ConstantEvalContext.types,
    EvalContext.types, hType,
    Except.bind, Except.pure, Bind.bind, Pure.pure]
  rw [constValueAtWithDefsIn_int_eq]
  simp only [constPointerFormsSupported, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Except.bind, Except.pure, Bind.bind, Pure.pure]
  rw [constValueAtChecked_eq]
  cases hModel : ctx.byteModel <;>
    simp [constPointerFormsSupported, Ty.isInteger, constValueAt,
      EvalContext.constantContext, hModel, Ty.bitWidthFor, Ty.bitWidthAtModel, Ty.bitWidth, Ty.bitWidthAtPointerBits,
      Except.bind, Except.pure, Bind.bind, Pure.pure]

/-- Rewriting the CFG of every function keeps the source tables, signatures,
    calling conventions and entry coordinates intact. This is a candidate
    context transform; no semantic refinement follows from constructing it. -/
def mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) : EvalContext :=
  { ctx with functions := (fun fn =>
      (ctx.functions fn).map (fun f => { f with cfg := transform f.cfg })) }

/-- Nominal checks read the finite source carrier and original headers, not
    executable CFGs. The recursive value visitor is an explicit parameter. -/
theorem checkFunctionItemLayer_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (recurse : Ty → Value → Except SemError Unit)
    (ty : Ty) (value : Value) :
    checkFunctionItemLayer { ctx with functions := functions } recurse ty value =
      checkFunctionItemLayer ctx recurse ty value := rfl

theorem checkFunctionItemLanes_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (fuel : Nat) (ty : Ty) (value : Value) :
    checkFunctionItemLanes { ctx with functions := functions } fuel ty value =
      checkFunctionItemLanes ctx fuel ty value := by
  induction fuel generalizing ty value with
  | zero => rfl
  | succ fuel ih =>
    have recursion : checkFunctionItemLanes { ctx with functions := functions } fuel =
        checkFunctionItemLanes ctx fuel := funext (fun t => funext (fun v => ih t v))
    simp only [checkFunctionItemLanes, recursion, checkFunctionItemLayer_withFunctions]

theorem checkFunctionItemValues_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (types : List Ty) (values : List Value) :
    checkFunctionItemValues (mapFunctionCFGs transform ctx) types values =
      checkFunctionItemValues ctx types values := by
  simp only [checkFunctionItemValues, mapFunctionCFGs, checkFunctionItemLanes_withFunctions]

theorem checkFunctionItemCalleeType_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (operand : ValueId) (value : Value) :
    checkFunctionItemCalleeType (mapFunctionCFGs transform ctx) operand value =
      checkFunctionItemCalleeType ctx operand value := rfl

theorem functionItemCall_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (target : FuncId) (signature : FuncTyId) (convention : CallingConv) :
    functionItemCall (mapFunctionCFGs transform ctx) target signature convention =
      functionItemCall ctx target signature convention := rfl

/-- Body resolution here is observed only for its success/error. A genuine
    body changes under the map; erasing its unused value preserves that
    observation without asserting equality of the transformed CFG. -/
theorem resolveFunctionItemBody_mapUnit_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (target : FuncId) :
    (resolveFunctionItemBody (mapFunctionCFGs transform ctx) target).map (fun _ => ()) =
      (resolveFunctionItemBody ctx target).map (fun _ => ()) := by
  trustIrCompilerProof {
    cases present : ctx.functions target <;>
      simp only [resolveFunctionItemBody, mapFunctionCFGs, present, Option.map, Except.map]
  } {
    cases present : ctx.functions target <;>
      simp only [resolveFunctionItemBody, mapFunctionCFGs, present, Option.map, Except.map] <;> rfl
  }

private theorem ignoreMemoryExcept_congr {α β : Type} (source target : Except SemError α)
    (observation : source.map (fun _ => ()) = target.map (fun _ => ())) (next : Sem β) :
    (do let _ ← Sem.fromMemoryExcept source; next) =
      (do let _ ← Sem.fromMemoryExcept target; next) := by
  cases source <;> cases target <;> cases observation <;> rfl

/-- The original header view never depends on an executable CFG, including
    the genuine-function fallback used by manually constructed contexts. -/
theorem lookupFunctionHeader_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (id : FuncId) :
    (mapFunctionCFGs transform ctx).lookupFunctionHeader id = ctx.lookupFunctionHeader id := by
  cases hHeader : ctx.functionHeaders id with
  | some result => simp only [EvalContext.lookupFunctionHeader, mapFunctionCFGs, hHeader]
  | none =>
    cases hFunction : ctx.functions id <;>
      simp only [EvalContext.lookupFunctionHeader, mapFunctionCFGs, hHeader, hFunction,
        Option.map, EvalFunction.header]

theorem functionHeader_matches_mapCFG (transform : CFG → CFG)
    (header : FunctionHeader) (function : EvalFunction) :
    header.matches { function with cfg := transform function.cfg } = header.matches function := rfl

theorem functionErrors_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).functionErrors = ctx.functionErrors := rfl

theorem checkSeqMapElement_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (inst : Inst) (element : Ty) (value : Value) :
    (mapFunctionCFGs transform ctx).checkSeqMapElement inst element value =
      ctx.checkSeqMapElement inst element value := rfl

theorem memoryLayout_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (ty : Ty) :
    (mapFunctionCFGs transform ctx).memoryLayout ty = ctx.memoryLayout ty := rfl

theorem loadMemoryValue_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (ty : Ty) (pointer : Value) (strict : Bool) :
    (mapFunctionCFGs transform ctx).loadMemoryValue ty pointer strict =
      ctx.loadMemoryValue ty pointer strict := rfl

theorem storeMemoryValue_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (ty : Ty) (pointer value : Value) (strict : Bool) :
    (mapFunctionCFGs transform ctx).storeMemoryValue ty pointer value strict =
      ctx.storeMemoryValue ty pointer value strict := rfl

/-- Function-local declarations are original source data, not reconstructed
    from a rewritten CFG. -/
theorem localTypes_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).localTypes = ctx.localTypes := rfl

/-- Installing a callee's declarations commutes with rewriting the function
    table. A copied callee's unchanged localTypes project to the same data. -/
theorem forFunction_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (function : EvalFunction) :
    (mapFunctionCFGs transform ctx).forFunction function =
      mapFunctionCFGs transform (ctx.forFunction function) := rfl

/-- Typed reads preserve every refusal under a function-body rewrite. -/
theorem integerOperand_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (id : ValueId) :
    (mapFunctionCFGs transform ctx).integerOperand id = ctx.integerOperand id := rfl

/-- Element-index interpretation uses the current original declarations. -/
theorem elementIndex_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (id : ValueId) :
    (mapFunctionCFGs transform ctx).elementIndex id = ctx.elementIndex id := rfl

/-- Result declarations use original metadata and actual header fields, which
    a function-body rewrite preserves even for the manual-context fallback. -/
theorem resultTypeHeaders_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).resultTypeHeaders = ctx.resultTypeHeaders := by
  funext id
  cases h : ctx.functions id <;>
    simp [EvalContext.resultTypeHeaders, mapFunctionCFGs, h]

theorem instructionResultTypes_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).instructionResultTypes = ctx.instructionResultTypes := by
  funext inst dests produced
  unfold EvalContext.instructionResultTypes
  rw [resultTypeHeaders_mapFunctionCFGs]
  rfl

theorem checkInstructionResults_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).checkInstructionResults = ctx.checkInstructionResults := by
  funext inst dests values
  simp only [EvalContext.checkInstructionResults, instructionResultTypes_mapFunctionCFGs]

theorem bindCallResults_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).bindCallResults = ctx.bindCallResults := by
  funext inst dests values
  simp only [EvalContext.bindCallResults, checkInstructionResults_mapFunctionCFGs]

theorem bindInstructionResults_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).bindInstructionResults = ctx.bindInstructionResults := by
  funext inst result dests
  cases result with
  | value result =>
    cases result <;> cases dests with
    | nil => simp only [EvalContext.bindInstructionResults, checkInstructionResults_mapFunctionCFGs]
    | cons dest rest =>
      cases rest <;>
        simp only [EvalContext.bindInstructionResults, checkInstructionResults_mapFunctionCFGs]
  | values results =>
    simp only [EvalContext.bindInstructionResults, checkInstructionResults_mapFunctionCFGs]
  | terminator result => rfl

/-- CFG rewrites preserve the complete source order, including table entries
    that have no executable body. Identity sets alone do not preserve bytes. -/
theorem functionOrder_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext) :
    (mapFunctionCFGs transform ctx).functionOrder = ctx.functionOrder := rfl

theorem encodeMemoryWithFunctions_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (ty : Ty) (value : Value) :
    encodeMemoryWithFunctions (mapFunctionCFGs transform ctx).byteModel
        (mapFunctionCFGs transform ctx).functionOrder ty value =
      encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty value := rfl

theorem decodeMemoryWithFunctions_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (memory : Memory) (ty : Ty) (bytes : List UInt8) :
    decodeMemoryWithFunctions (mapFunctionCFGs transform ctx).byteModel
        (mapFunctionCFGs transform ctx).functionOrder memory ty bytes =
      decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes := rfl

/-- A function value resolves identically after rewriting target CFGs. The
    signature id, actual callee header, ABI checks and missing-target errors
    are all preserved, not inferred from the rewritten body's success. -/
theorem functionCall_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (held : FuncTyId) (target : FuncId) (sig : FuncTyId) :
    functionCall (mapFunctionCFGs transform ctx) held target sig =
      functionCall ctx held target sig := by
  cases hTarget : ctx.functions target <;>
    simp [functionCall, mapFunctionCFGs, hTarget,
      Except.bind, Except.pure, Bind.bind, Pure.pure]

/-- CFG rewriting retains both logical resolution and the actual convention
    inspected by ordinary indirect application. -/
theorem functionCallWithConvention_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (held : FuncTyId) (target : FuncId) (sig : FuncTyId) (convention : CallingConv) :
    functionCallWithConvention (mapFunctionCFGs transform ctx) held target sig convention =
      functionCallWithConvention ctx held target sig convention := by
  unfold functionCallWithConvention
  rw [functionCall_mapFunctionCFGs transform ctx held target sig]
  cases checked : functionCall ctx held target sig with
  | error error => rfl
  | ok resolved =>
    cases found : ctx.functions resolved <;> simp only [mapFunctionCFGs, found, Option.map]

/-- A function-table CFG rewrite cannot perturb constant evaluation. This
    removes the former opaque-constant obstruction to proving whole-program
    refinement; call and control-flow preservation are separate obligations. -/
theorem constValueAtWithDefs_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (ty : Ty) (c : Constant) :
    constValueAtWithDefs (mapFunctionCFGs transform ctx) ty c =
      constValueAtWithDefs ctx ty c := by
  rfl

-- =================================================================
-- Header-sensitive closure operations under function-table CFG rewrites
-- =================================================================

set_option smartUnfolding false in
set_option maxHeartbeats 2000000 in
/-- Capture value checking reads data layouts and nominal capture types, never
    function bodies. Equality includes every structural-budget, poison and
    type refusal for arbitrary values. -/
theorem checkClosureValueAt_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (fuel : Nat) (ty : Ty) (v : Value) :
    checkClosureValueAt { ctx with functions := functions } fuel ty v =
      checkClosureValueAt ctx fuel ty v := by
  induction fuel generalizing ty v with
  | zero => rfl
  | succ fuel ih =>
    have hRec : checkClosureValueAt { ctx with functions := functions } fuel =
        checkClosureValueAt ctx fuel := funext (fun t => funext (fun x => ih t x))
    trustIrCompilerProof {
      rw [checkClosureValueAt.eq_2, checkClosureValueAt.eq_2]
      simp only [hRec, EvalContext.closures, EvalContext.enums, EvalContext.structs,
        EvalContext.records, EvalContext.types, EvalContext.functionItems, functionItemDeclaration]
    } {
      conv =>
        lhs
        unfold checkClosureValueAt
      conv =>
        rhs
        unfold checkClosureValueAt
      simp only [hRec, EvalContext.closures, EvalContext.enums, EvalContext.structs,
        EvalContext.records, EvalContext.types, EvalContext.functionItems, functionItemDeclaration]
    }

/-- The value-derived structural budget is unchanged by function-body rewrites. -/
theorem checkClosureValue_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (ty : Ty) (v : Value) :
    checkClosureValue { ctx with functions := functions } ty v =
      checkClosureValue ctx ty v := by
  exact checkClosureValueAt_withFunctions ctx functions _ ty v

/-- Contextual enum/record construction uses declaration tables and lane
    value checks, never executable function bodies. This includes all table,
    variant, arity and type refusals, as well as the complete constructed value. -/
theorem makeAggregateValueWithContext_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (ty : Ty) (variant : Option Nat)
    (lanes : List Value) :
    makeAggregateValueWithContext { ctx with functions := functions } ty variant lanes =
      makeAggregateValueWithContext ctx ty variant lanes := by
  rfl

/-- The CFG-only form retains the exact enum tag or record field names,
    original lanes, and every refusal of contextual aggregate construction. -/
theorem makeAggregateValueWithContext_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (ty : Ty) (variant : Option Nat) (lanes : List Value) :
    makeAggregateValueWithContext (mapFunctionCFGs transform ctx) ty variant lanes =
      makeAggregateValueWithContext ctx ty variant lanes :=
  makeAggregateValueWithContext_withFunctions ctx _ ty variant lanes

/-- Capture projection cannot execute or inspect a closure's code. -/
theorem checkedClosureCaptures_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (cid : ClosureTyId) (captures : List Value) :
    checkedClosureCaptures { ctx with functions := functions } cid captures =
      checkedClosureCaptures ctx cid captures := by
  simp only [checkedClosureCaptures, EvalContext.closures, checkClosureValue_withFunctions]

/-- Extracting a capture preserves its exact value and every refusal after an
    arbitrary executable-function-table replacement. -/
theorem closureExtract_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (ty : Ty) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) :
    closureExtract { ctx with functions := functions } ty cid fn captures field =
      closureExtract ctx ty cid fn captures field := by
  simp only [closureExtract, checkedClosureCaptures_withFunctions]

/-- Updating capture data does not use the executable function table either. -/
theorem closureInsert_withFunctions (ctx : EvalContext)
    (functions : FuncId → Option EvalFunction) (ty : Ty) (cid : ClosureTyId)
    (fn : FuncId) (captures : List Value) (field : Nat) (value : Value) :
    closureInsert { ctx with functions := functions } ty cid fn captures field value =
      closureInsert ctx ty cid fn captures field value := by
  simp only [closureInsert, checkedClosureCaptures_withFunctions,
    checkClosureValue_withFunctions]

/-- The CFG-only form of capture extraction has the same result and errors. -/
theorem closureExtract_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (ty : Ty) (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (field : Nat) :
    closureExtract (mapFunctionCFGs transform ctx) ty cid fn captures field =
      closureExtract ctx ty cid fn captures field :=
  closureExtract_withFunctions ctx _ ty cid fn captures field

/-- The CFG-only form of capture updates preserves the entire checked value. -/
theorem closureInsert_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (ty : Ty) (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (field : Nat)
    (value : Value) :
    closureInsert (mapFunctionCFGs transform ctx) ty cid fn captures field value =
      closureInsert ctx ty cid fn captures field value :=
  closureInsert_withFunctions ctx _ ty cid fn captures field value

/-- Closure construction inspects the actual target header, but a CFG rewrite
    leaves that complete header intact. Every capture and its provenance is
    preserved; missing-target, signature, ABI, arity and value errors agree. -/
theorem makeClosureValue_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (cid : ClosureTyId) (fn : FuncId) (captures : List Value) :
    makeClosureValue (mapFunctionCFGs transform ctx) cid fn captures =
      makeClosureValue ctx cid fn captures := by
  cases hDefinition : ctx.valueSource.closureTy cid with
  | none => simp [makeClosureValue, closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, Except.bind, Except.pure, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw]
  | some definition =>
    cases hSignature : ctx.funcTys definition.func with
    | none => simp [makeClosureValue, closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, hSignature, Except.bind, Except.pure, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw]
    | some signature =>
      cases hTarget : ctx.functions fn with
      | none =>
        cases hDeclared : ctx.declared fn <;>
          simp [makeClosureValue, closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, hSignature, hTarget, hDeclared,
          Except.bind, Except.pure, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw]
      | some target =>
        cases hAbi : (signature.abi.isSome || target.body.abi.isSome) <;>
          cases hShape : (signature.isVararg || target.body.isVararg ||
            !(closureTyListEq target.body.paramTys (definition.captures ++ signature.params)) ||
            !(closureTyListEq target.body.returnTys signature.returns) ||
            target.body.abi != signature.abi) <;>
          simp [makeClosureValue, closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, hSignature, hTarget, hAbi, hShape,
            checkClosureValue_withFunctions, Except.bind, Except.pure, Bind.bind, Pure.pure,
            throw, throwThe, MonadExceptOf.throw]

/-- Resolving the nominal closure call preserves signature and calling-convention
    checks as well as captures and arguments after replacing only target CFGs. -/
theorem closureCall_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (sig : FuncTyId)
    (args : List Value) (conv : CallingConv) :
    closureCall (mapFunctionCFGs transform ctx) cid fn captures sig args conv =
      closureCall ctx cid fn captures sig args conv := by
  unfold closureCall
  simp only [makeClosureValue_mapFunctionCFGs]
  cases hDefinition : ctx.valueSource.closureTy cid with
  | none => simp [closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, Except.bind, Except.pure, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw]
  | some definition =>
    cases hSignature : ctx.funcTys definition.func with
    | none => simp [closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, hSignature, Except.bind, Except.pure, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw]
    | some signature =>
      cases hTarget : ctx.functions fn with
      | none =>
        cases hDeclared : ctx.declared fn <;>
          simp [closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, hSignature, hTarget, hDeclared,
          Except.bind, Except.pure, Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw]
      | some target =>
        cases hAbi : (signature.abi.isSome || target.body.abi.isSome) <;>
          cases hShape : (signature.isVararg || target.body.isVararg ||
            !(closureTyListEq target.body.paramTys (definition.captures ++ signature.params)) ||
            !(closureTyListEq target.body.returnTys signature.returns) ||
            target.body.abi != signature.abi) <;>
          simp [closureContract, mapFunctionCFGs, EvalContext.closures, hDefinition, hSignature, hTarget, hAbi, hShape,
            checkClosureValue_withFunctions, Except.bind, Except.pure, Bind.bind, Pure.pure,
            throw, throwThe, MonadExceptOf.throw]

/-- The exact contextual Cast dispatcher, separated from unrelated instruction
    cases. This exposes the operational branches without reducing pure header
    queries or recursive byte codecs during context-congruence proofs. -/
theorem stepInstWithContext_cast_eq (ctx : EvalContext) (op : CastOp)
    (source destination : Ty) (operand : ValueId) :
    stepInstWithContext ctx (.Cast op source destination operand) =
      (match op, source, destination with
      | .ReifyFnPointer, .FnItem held, .Func signature => do
        let value ← Sem.lookupValue operand
        Sem.rejectPartial value "ReifyFnPointer"
        match value with
        | .fnItem actual =>
          if actual != held then
            Sem.throwTypeError "ReifyFnPointer: item identity differs from source type"
          let declaration ← Sem.fromMemoryExcept (functionItemDeclaration ctx held)
          if declaration.signatureId != signature then
            Sem.throwTypeError "ReifyFnPointer: destination signature differs from item declaration"
          pure (.value (some (← Sem.bindFresh (.fnDef signature held))))
        | _ => Sem.throwTypeError "ReifyFnPointer: source is not a nominal function item"
      | _, _, _ =>
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
        else stepInst (.Cast op source destination operand) ctx.byteModel) := by
  cases op <;> first
    | rfl
    | cases source <;> first
      | rfl
      | cases destination <;> rfl

/-- Every contextual instruction keeps its complete state transition under a
    function-table CFG rewrite. This includes closure construction and capture
    access, not just scalar instructions or successful runs. Calls execute in
    `stepNWithContext`; this local result does not assert their body refinement. -/
theorem stepInstWithContext_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (inst : Inst) :
    stepInstWithContext (mapFunctionCFGs transform ctx) inst =
      stepInstWithContext ctx inst := by
  have frameTypes (value : Value) :
      bindingFrameTypes (mapFunctionCFGs transform ctx) value = bindingFrameTypes ctx value := rfl
  have itemLanes (fuel : Nat) (ty : Ty) (value : Value) :
      checkFunctionItemLanes (mapFunctionCFGs transform ctx) fuel ty value =
        checkFunctionItemLanes ctx fuel ty value :=
    checkFunctionItemLanes_withFunctions ctx _ fuel ty value
  cases inst
  case Const ty c =>
    exact stepInstWithContext_const_withFunctions ctx _ ty c
  case BinOp op ty lhs rhs =>
    cases ty <;> rfl
  case Undef ty =>
    cases ty <;> rfl
  case Cast op source destination operand =>
    rw [stepInstWithContext_cast_eq, stepInstWithContext_cast_eq]
    rfl
  case BindSlot frame slot value =>
    simp only [stepInstWithContext, frameTypes, itemLanes] <;> rfl
  case LoadSlot frame slot ty =>
    simp only [stepInstWithContext, frameTypes, itemLanes] <;> rfl
  case CloseFrame frame =>
    simp only [stepInstWithContext, frameTypes] <;> rfl
  case ExtractElement ty array index =>
    simp only [stepInstWithContext, elementIndex_mapFunctionCFGs] <;> rfl
  case InsertElement ty array index value =>
    simp only [stepInstWithContext, elementIndex_mapFunctionCFGs] <;> rfl
  case MakeClosure cid fn captures =>
    simp only [stepInstWithContext, makeClosureValue_mapFunctionCFGs] <;> rfl
  case MakeAggregate ty variant fields =>
    cases ty <;>
      simp only [stepInstWithContext, makeAggregateValueWithContext_mapFunctionCFGs]
    all_goals rfl
  case ExtractField ty aggregateId field =>
    simp only [stepInstWithContext, closureExtract_mapFunctionCFGs] <;> rfl
  case InsertField ty aggregateId field valueId =>
    simp only [stepInstWithContext, closureInsert_mapFunctionCFGs] <;> rfl
  all_goals rfl

-- =================================================================
-- Terminator and exception wrappers under function-table CFG rewrites
-- =================================================================

/-- Nominal function/closure resolution produces the identical call request
    after rewriting only callee CFGs. The statement retains argument lookup,
    depth exhaustion, target/header refusals and the supplied fallback. It does
    not execute the requested callee. -/
theorem closureTermWithContext_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (depth : Nat) (term : Inst) (fallback : Sem InstrResult) :
    closureTermWithContext (mapFunctionCFGs transform ctx) depth term fallback =
      closureTermWithContext ctx depth term fallback := by
  have bodyChecks (function : FuncId) (next : Sem InstrResult) :
      (do
        let _ ← Sem.fromMemoryExcept
          (resolveFunctionItemBody (mapFunctionCFGs transform ctx) function)
        next) =
      (do let _ ← Sem.fromMemoryExcept (resolveFunctionItemBody ctx function); next) :=
    ignoreMemoryExcept_congr _ _
      (resolveFunctionItemBody_mapUnit_mapFunctionCFGs transform ctx function) next
  cases term <;>
    simp only [closureTermWithContext, functionCallWithConvention_mapFunctionCFGs,
      closureCall_mapFunctionCFGs, checkFunctionItemCalleeType_mapFunctionCFGs,
      functionItemCall_mapFunctionCFGs, bodyChecks]

/-- With the same current CFG, contextual terminator resolution is independent
    of rewritten callee bodies under both panic strategies. Unwind pad lookup
    still uses that actual current CFG; this fact does not identify different
    pad/control-flow layouts or execute any returned call request. -/
theorem stepTermWithContext_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (depth : Nat) (cfg : CFG) (term : Inst) (strat : PanicStrategy) :
    stepTermWithContext (mapFunctionCFGs transform ctx) depth cfg term strat =
      stepTermWithContext ctx depth cfg term strat := by
  cases strat <;>
    simp only [stepTermWithContext, closureTermWithContext_mapFunctionCFGs]
  all_goals rfl

/-- Raising a local failed assertion under unwind retains its complete outcome
    and exception allocation when executable function bodies are rewritten. -/
theorem raiseIfUnwind_stepInst_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (strat : PanicStrategy) (inst : Inst) :
    raiseIfUnwind strat (stepInstWithContext (mapFunctionCFGs transform ctx) inst)
        (mapFunctionCFGs transform ctx).byteModel =
      raiseIfUnwind strat (stepInstWithContext ctx inst) ctx.byteModel := by
  rw [stepInstWithContext_mapFunctionCFGs]
  rfl

/-- Landing-pad result binding and its abort/missing-hand fallbacks keep all
    state changes and errors after rewriting function bodies. -/
theorem semLandingPadWith_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (strat : PanicStrategy) (pad : Inst) (dests : List ValueId) :
    semLandingPadWith strat (mapFunctionCFGs transform ctx) pad dests =
      semLandingPadWith strat ctx pad dests := by
  cases strat <;>
    simp only [semLandingPadWith, stepInstWithContext_mapFunctionCFGs,
      bindInstructionResults_mapFunctionCFGs, bindCallResults_mapFunctionCFGs]

/-- Drop resolution uses the actual glue table, which a CFG-only function
    rewrite preserves. This does not authenticate a glue table or execute it. -/
theorem resolveDrop_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (inst : Inst) :
    (mapFunctionCFGs transform ctx).resolveDrop inst = ctx.resolveDrop inst := by
  cases inst <;> rfl

/-- Resolving a block's drops preserves its whole body and terminator. -/
theorem resolveBlock_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (block : BasicBlock) :
    (mapFunctionCFGs transform ctx).resolveBlock block = ctx.resolveBlock block := by
  have hDrop : (mapFunctionCFGs transform ctx).resolveDrop = ctx.resolveDrop :=
    funext (resolveDrop_mapFunctionCFGs transform ctx)
  simp only [EvalContext.resolveBlock, hDrop]

/-- The resolved current CFG retains its exact block lookup after only the
    context's executable function bodies are rewritten. -/
theorem resolveCfg_mapFunctionCFGs (transform : CFG → CFG) (ctx : EvalContext)
    (cfg : CFG) :
    (mapFunctionCFGs transform ctx).resolveCfg cfg = ctx.resolveCfg cfg := by
  have hBlock : (mapFunctionCFGs transform ctx).resolveBlock = ctx.resolveBlock :=
    funext (resolveBlock_mapFunctionCFGs transform ctx)
  exact congrArg (fun resolve : BasicBlock → BasicBlock =>
    fun pc => (cfg pc).map resolve) hBlock

/-- Direct callee lookup preserves missing/declaration errors and returns the
    actual rewritten callee on success. The transformed CFG is retained in
    the result; equating it with the old callee would erase the obligation
    that the whole-program proof still has to discharge. -/
theorem lookupDirectCallee_mapFunctionCFGs (transform : CFG → CFG)
    (ctx : EvalContext) (id : FuncId) (declaredMessage missingMessage : String) :
    (mapFunctionCFGs transform ctx).lookupDirectCallee id declaredMessage missingMessage = (do
      let callee ← ctx.lookupDirectCallee id declaredMessage missingMessage
      pure { callee with cfg := transform callee.cfg }) := by
  cases hTarget : ctx.functions id with
  | some function =>
    simp [EvalContext.lookupDirectCallee, mapFunctionCFGs, hTarget, pure_bind]
  | none =>
    cases hDeclared : ctx.declared id <;>
      simp [EvalContext.lookupDirectCallee, mapFunctionCFGs, hTarget, hDeclared,
        Sem.throwUnsupported, Sem.throwTypeError, pure_bind]
    all_goals rfl

/-- Pad entry reads only block existence and the leading landing-pad clauses.
    The nested Option retains the difference between a missing block and a
    present block with no landing pad, so distinct malformed-input refusals
    cannot collapse into one successful header comparison. -/
theorem semEnterPad_of_same_headers (source target : CFG) (exn : Addr) (dest : BlockId)
    (hHeader : (target dest).map (fun b => b.body.head?.bind Inst.padClauses) =
      (source dest).map (fun b => b.body.head?.bind Inst.padClauses)) :
    semEnterPad target exn dest = semEnterPad source exn dest := by
  cases hSource : source dest <;> cases hTarget : target dest <;>
    simp only [hSource, hTarget, Option.map, Option.some.injEq] at hHeader
  all_goals try contradiction
  · simp only [semEnterPad, hSource, hTarget]
  · simp only [semEnterPad, hSource, hTarget, hHeader]

/-- Rewriting the current CFG preserves unwind terminator resolution whenever
    each actual landing-pad header is retained. Returns and every exception,
    malformed-pad and typed-catch refusal keep their full state transitions. -/
theorem stepTermUnwind_of_same_headers (source target : CFG) (term : Inst)
    (model : ByteModel)
    (hHeaders : ∀ dest, (target dest).map (fun b => b.body.head?.bind Inst.padClauses) =
      (source dest).map (fun b => b.body.head?.bind Inst.padClauses)) :
    stepTermUnwind target term model = stepTermUnwind source term model := by
  cases term <;>
    simp only [stepTermUnwind, semEnterPad_of_same_headers source target _ _ (hHeaders _)]

/-- Contextual terminator resolution combines the CFG-only function-table
    rewrite with the static pad-header condition on the current CFG. This
    reaches both panic strategies and all indirect-call request/error paths;
    the recursive bodies requested by those calls still need their own lift. -/
theorem stepTermWithContext_mapFunctionCFGs_of_same_headers
    (transform : CFG → CFG) (ctx : EvalContext) (depth : Nat)
    (source target : CFG) (term : Inst) (strat : PanicStrategy)
    (hHeaders : ∀ dest, (target dest).map (fun b => b.body.head?.bind Inst.padClauses) =
      (source dest).map (fun b => b.body.head?.bind Inst.padClauses)) :
    stepTermWithContext (mapFunctionCFGs transform ctx) depth target term strat =
      stepTermWithContext ctx depth source term strat := by
  rw [stepTermWithContext_mapFunctionCFGs]
  cases strat <;> simp only [stepTermWithContext]
  all_goals rw [stepTermUnwind_of_same_headers source target term ctx.byteModel hHeaders]

-- =================================================================
-- Definitions
-- =================================================================

/-- `o` is a behaviour of the function body `cfg`, entered at `pc` with
    `args` from state `s`, under the interprocedural evaluator in the module
    context `ctx` with panic strategy `strat`. Fuel and call depth are both
    quantified, so `diverges` means `outOfFuel` at every pair. -/
def BehavesIn (ctx : EvalContext) (strat : PanicStrategy) (cfg : CFG) (pc : BlockId)
    (args : List Value) (s : MachineState) (o : Outcome) : Prop :=
  (∃ fuel depth, Outcome.ofRun
      (Sem.run (stepNWithContext ctx fuel depth cfg pc args strat) s) = some o) ∨
  (o = .diverges ∧ ∀ fuel depth,
      Sem.run (stepNWithContext ctx fuel depth cfg pc args strat) s = .error .outOfFuel)

/-- **Behaviour refinement with calls executed.** In every module context,
    for every source run that is UB-free at every fuel and depth, every
    behaviour of the transformed body is a behaviour of the source body. -/
def behaviour_refines_in (strat : PanicStrategy) (transform : CFG → CFG) : Prop :=
  ∀ ctx cfg pc args s, ¬ BehavesIn ctx strat cfg pc args s .ub →
    ∀ o, BehavesIn ctx strat (transform cfg) pc args s o → BehavesIn ctx strat cfg pc args s o

-- =================================================================
-- Basic facts
-- =================================================================

/-- Every body has a behaviour from every input in every context. -/
theorem behavesIn_nonempty (ctx : EvalContext) (strat : PanicStrategy) (cfg : CFG)
    (pc : BlockId) (args : List Value) (s : MachineState) :
    ∃ o, BehavesIn ctx strat cfg pc args s o := by
  by_cases hDiv : ∀ fuel depth,
      Sem.run (stepNWithContext ctx fuel depth cfg pc args strat) s = .error .outOfFuel
  · exact ⟨.diverges, Or.inr ⟨rfl, hDiv⟩⟩
  · have ⟨fuel, hFuel⟩ := Classical.not_forall.mp hDiv
    have ⟨depth, hDepth⟩ := Classical.not_forall.mp hFuel
    cases hO : Outcome.ofRun (Sem.run (stepNWithContext ctx fuel depth cfg pc args strat) s) with
    | none => exact absurd ((Outcome.ofRun_eq_none_iff _).mp hO) hDepth
    | some o => exact ⟨o, Or.inl ⟨fuel, depth, hO⟩⟩

/-- A single run exhibits `ub` exactly when it is a UB error. -/
theorem Outcome.ofRun_eq_some_ub (r : Except SemError (List Value × MachineState)) :
    Outcome.ofRun r = some .ub ↔ ∃ msg, r = .error (.ub msg) := by
  constructor
  · intro h
    cases r with
    | ok v => simp [Outcome.ofRun] at h
    | error e => cases e <;> simp_all [Outcome.ofRun]
  · rintro ⟨msg, rfl⟩
    rfl

/-- The UB-freeness premise of `behaviour_refines_in`, spelled out: no fuel
    and no depth gives the source `.error (.ub _)`. -/
theorem not_behavesIn_ub_iff (ctx : EvalContext) (strat : PanicStrategy) (cfg : CFG)
    (pc : BlockId) (args : List Value) (s : MachineState) :
    ¬ BehavesIn ctx strat cfg pc args s .ub ↔
      ∀ fuel depth msg,
        Sem.run (stepNWithContext ctx fuel depth cfg pc args strat) s ≠ .error (.ub msg) := by
  constructor
  · intro h fuel depth msg hRun
    exact h (Or.inl ⟨fuel, depth, (Outcome.ofRun_eq_some_ub _).mpr ⟨msg, hRun⟩⟩)
  · intro h hB
    rcases hB with ⟨fuel, depth, hO⟩ | ⟨hEq, _⟩
    · obtain ⟨msg, hRun⟩ := (Outcome.ofRun_eq_some_ub _).mp hO
      exact h fuel depth msg hRun
    · cases hEq

/-- Bodies whose runs agree at every fuel and depth have the same
    behaviours. -/
theorem behavesIn_congr (ctx : EvalContext) (strat : PanicStrategy) (cfg1 cfg2 : CFG)
    (pc : BlockId) (args : List Value) (s : MachineState)
    (hEq : ∀ fuel depth, Sem.run (stepNWithContext ctx fuel depth cfg1 pc args strat) s
      = Sem.run (stepNWithContext ctx fuel depth cfg2 pc args strat) s) (o : Outcome) :
    BehavesIn ctx strat cfg1 pc args s o → BehavesIn ctx strat cfg2 pc args s o := by
  intro h
  rcases h with ⟨fuel, depth, hO⟩ | ⟨hO, hDiv⟩
  · exact Or.inl ⟨fuel, depth, by rw [← hEq]; exact hO⟩
  · exact Or.inr ⟨hO, fun fuel depth => by rw [← hEq]; exact hDiv fuel depth⟩

/-- The identity transform refines with calls executed. -/
theorem id_refines_in (strat : PanicStrategy) :
    behaviour_refines_in strat (fun cfg => cfg) := by
  intro _ _ _ _ _ _ o h
  exact h

/-- Refinement with calls executed composes; the intermediate body is UB-free
    because a UB behaviour of it would be one of the UB-free source. -/
theorem compose_refines_in (strat : PanicStrategy) (t1 t2 : CFG → CFG)
    (h1 : behaviour_refines_in strat t1) (h2 : behaviour_refines_in strat t2) :
    behaviour_refines_in strat (fun cfg => t2 (t1 cfg)) := by
  intro ctx cfg pc args s hNoUB o h
  have hNoUB1 : ¬ BehavesIn ctx strat (t1 cfg) pc args s .ub :=
    fun hUB => hNoUB (h1 ctx cfg pc args s hNoUB .ub hUB)
  exact h1 ctx cfg pc args s hNoUB o (h2 ctx (t1 cfg) pc args s hNoUB1 o h)

-- =================================================================
-- Positive: the UB-exploiting rewrite, calls executed
-- =================================================================

/-- `m1` runs exactly like `m2` from every state, except from a state where
    `m2` is UB (where anything goes). -/
def RunsLikeUnlessUB {α : Type} (m1 m2 : Sem α) : Prop :=
  ∀ s, Sem.run m1 s = Sem.run m2 s ∨ ∃ msg, Sem.run m2 s = .error (.ub msg)

theorem RunsLikeUnlessUB.refl {α : Type} (m : Sem α) : RunsLikeUnlessUB m m :=
  fun _ => Or.inl rfl

/-- The relation is a congruence for bind: a UB prefix makes the whole
    source UB, an equal prefix hands the related continuations the same
    value and state. -/
theorem RunsLikeUnlessUB.bind {α β : Type} {m1 m2 : Sem α} {k1 k2 : α → Sem β}
    (hm : RunsLikeUnlessUB m1 m2) (hk : ∀ a, RunsLikeUnlessUB (k1 a) (k2 a)) :
    RunsLikeUnlessUB (m1 >>= k1) (m2 >>= k2) := by
  intro s
  rw [Sem.run_bind, Sem.run_bind]
  rcases hm s with h | ⟨msg, h⟩
  · rw [h]
    cases h2 : Sem.run m2 s with
    | error e => exact Or.inl rfl
    | ok v =>
      obtain ⟨a, s'⟩ := v
      exact hk a s'
  · exact Or.inr ⟨msg, by rw [h]; rfl⟩

/-- A source that is UB from every state is related to anything. -/
theorem RunsLikeUnlessUB.of_ub {α : Type} {m1 m2 : Sem α}
    (h : ∀ s, ∃ msg, Sem.run m2 s = .error (.ub msg)) : RunsLikeUnlessUB m1 m2 :=
  fun s => Or.inr (h s)

/-- Close a `RunsLikeUnlessUB` goal whose two sides are the same program
    except for recursive evaluator calls on the two CFGs, which `ih` relates:
    walk binds, `match`es and `if`s in lockstep. -/
local macro "invoke_congr " ih:term : tactic =>
  `(tactic| repeat (first
    | exact $ih _ _ _
    | refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
    | split
    | exact RunsLikeUnlessUB.refl _))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- At every fuel and depth, under panic=abort and with calls executed, the
    `unreachableToReturn` body runs exactly like the source body unless the
    source is UB. A rewritten block's `Return []` replaces an `Unreachable`
    the source reaches only to be UB; every other step, the calls included
    (they run the context's unchanged callees), is the same. -/
theorem stepNWithContext_unreachableToReturn (ctx : EvalContext) (cfg : CFG) :
    ∀ fuel depth pc args,
      RunsLikeUnlessUB
        (stepNWithContext ctx fuel depth (unreachableToReturn cfg) pc args .abort)
        (stepNWithContext ctx fuel depth cfg pc args .abort) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _
    simp only [stepNWithContext]
    exact RunsLikeUnlessUB.refl _
  | succ n ih =>
    intro depth pc args
    simp only [stepNWithContext, unreachableToReturn]
    cases cfg pc with
    | none => exact RunsLikeUnlessUB.refl _
    | some blk =>
      simp only [Option.map]
      unfold unreachableToReturnBlock
      split
      · rename_i hT
        refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        apply RunsLikeUnlessUB.of_ub
        intro s
        have hRT : (ctx.resolveBlock blk).terminator = .Unreachable := by
          simp [EvalContext.resolveBlock, EvalContext.resolveDrop, hT]
        simp only [hRT]
        exact ⟨_, rfl⟩
      · refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        refine RunsLikeUnlessUB.bind (RunsLikeUnlessUB.refl _) (fun _ => ?_)
        rename_i termResult
        cases termResult with
        | terminator sr =>
          simp only [pure_bind]
          cases sr with
          | Continue nextPc nextArgs => exact ih depth nextPc nextArgs
          | InvokeReq calleeId callArgs normalDest normalArgIds unwindDest =>
            cases depth with
            | zero => exact RunsLikeUnlessUB.refl _
            | succ d =>
              simp only [invokeCatch, bind_assoc, pure_bind]
              invoke_congr ih
          | InvokeIndirectReq addr sig callArgs normalDest normalArgIds unwindDest =>
            cases depth with
            | zero => exact RunsLikeUnlessUB.refl _
            | succ d =>
              simp only [invokeCatch, bind_assoc, pure_bind]
              invoke_congr ih
          | _ => exact RunsLikeUnlessUB.refl _
        | _ => exact RunsLikeUnlessUB.refl _

/-- A relation that holds at every fuel and depth transfers behaviours from
    the target to a UB-free source. -/
theorem behavesIn_of_runsLike (ctx : EvalContext) (strat : PanicStrategy) (cfg1 cfg2 : CFG)
    (pc : BlockId) (args : List Value) (s : MachineState)
    (hRel : ∀ fuel depth, RunsLikeUnlessUB
      (stepNWithContext ctx fuel depth cfg1 pc args strat)
      (stepNWithContext ctx fuel depth cfg2 pc args strat))
    (hNoUB : ¬ BehavesIn ctx strat cfg2 pc args s .ub) (o : Outcome)
    (h : BehavesIn ctx strat cfg1 pc args s o) : BehavesIn ctx strat cfg2 pc args s o := by
  have hNoUB' := (not_behavesIn_ub_iff ctx strat cfg2 pc args s).mp hNoUB
  have hEq : ∀ fuel depth, Sem.run (stepNWithContext ctx fuel depth cfg1 pc args strat) s
      = Sem.run (stepNWithContext ctx fuel depth cfg2 pc args strat) s := by
    intro fuel depth
    rcases hRel fuel depth s with h' | ⟨msg, h'⟩
    · exact h'
    · exact absurd h' (hNoUB' fuel depth msg)
  exact behavesIn_congr ctx strat cfg1 cfg2 pc args s hEq o h

/-- **Positive, calls executed: UB is top.** Under panic=abort, in every
    module context, rewriting `Unreachable` into `Return []` is a behaviour
    refinement of a body that calls: the rewrite changes only runs that are
    UB, and the callees it reaches run unchanged. The in-context analogue of
    `unreachableToReturn_refines`. -/
theorem unreachableToReturn_refines_in : behaviour_refines_in .abort unreachableToReturn := by
  intro ctx cfg pc args s hNoUB o h
  exact behavesIn_of_runsLike ctx .abort _ cfg pc args s
    (fun fuel depth => stepNWithContext_unreachableToReturn ctx cfg fuel depth pc args) hNoUB o h

private theorem checkFunctionItemValues_nil (ctx : EvalContext) (types : List Ty) :
    checkFunctionItemValues ctx types [] = .ok () := by
  simp only [checkFunctionItemValues, List.zip_nil_right]
  rfl

/-- Non-vacuity: in any context the UB source `unreachableCFG` becomes a
    returning body. -/
theorem unreachableToReturn_unreachableCFG_returns_in (ctx : EvalContext) :
    ∃ r, Sem.run (stepNWithContext ctx 1 0 (unreachableToReturn unreachableCFG) ⟨0⟩ [] .abort)
      MachineState.empty = .ok r := by
  change ∃ r, Sem.run (do
    if let some expected := ctx.functionReturnTypes then
      let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected [])
      pure []
    else pure []) MachineState.empty = .ok r
  cases ctx.functionReturnTypes <;> simp only [checkFunctionItemValues_nil] <;> exact ⟨_, rfl⟩

-- =================================================================
-- Inlining, frame-discipline form, at the behaviour level
-- =================================================================

/-- The boundary a resolved `Call` puts around its callee body's run
    (`runCallReq`): a return is checked for its arity (a type error) and for
    poison (UB, roadmap WS2.10) and is given the caller's frame back; every
    other behaviour (a trap, UB, an unsupported construct, divergence) passes
    through verbatim. -/
def callBoundary (returnTys : List Ty) (frame : StackFrame) : Outcome → Outcome
  | .returns (retVals, sEnd) =>
    if retVals.length = returnTys.length then
      if retVals.any Value.isPoison then .ub
      else .returns (retVals, restoreFrame sEnd frame [])
    else .typeError
  | o => o

/-- **Inlining, per run.** For a resolved callee and well-formed, poison-free
    arguments, the outcome of the `Call` at a fuel and depth is the outcome of
    the callee body run inline (on the fresh frame the call discipline
    prescribes) at the same fuel and depth, mapped through `callBoundary`. In
    particular the Call runs out of fuel exactly when the inline run does. -/
theorem inlining_outcome
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value) (s : MachineState)
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hArgsClean : callArgs.any Value.isPoison = false) :
    Outcome.ofRun (Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s)
      = (Outcome.ofRun (Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
            callee.cfg callee.entryBlock callArgs)
          { s with locals := ValueMap.empty, nextValueId := 0 })).map
          (callBoundary callee.body.returnTys (saveFrame s none)) := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) :=
    fun _ => rfl
  have hset : ∀ st st' : MachineState, Sem.run (Sem.setState st') st = .ok ((), st') :=
    fun _ _ => rfl
  cases hIn : Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock callArgs)
      { s with locals := ValueMap.empty, nextValueId := 0 } with
  | error e =>
    rw [inlining_error_transfer ctx fuel callDepth calleeId callee callArgs s e hFn hAbi hArity
      hArgsClean hIn]
    cases e <;> rfl
  | ok v =>
    obtain ⟨retVals, sE⟩ := v
    by_cases hRet : retVals.length = callee.body.returnTys.length
    · cases hp : retVals.any Value.isPoison with
      | false =>
        rw [runCallReq_ok_of_inline ctx fuel callDepth calleeId callee callArgs s sE retVals hFn
          hAbi hArity hRet hArgsClean hp hIn]
        simp [Outcome.ofRun, callBoundary, hRet, hp]
      | true =>
        unfold runCallReq
        simp only [hFn, hAbi, requireUntypedAbi_none, checkCallArity_ok callArgs callee.body.paramTys hArity,
          Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
          Sem.rejectPoisonValues_run_ok callArgs _ s hArgsClean, hIn,
          checkReturnArity_ok retVals callee.body.returnTys hRet]
        rw [show (Outcome.ofRun (.ok (retVals, sE) : Except SemError (List Value × MachineState))).map
            (callBoundary callee.body.returnTys (saveFrame s none)) = some .ub by
          simp [Outcome.ofRun, callBoundary, hRet, hp]]
        simp only [Sem.rejectPoisonValues, hp, if_true]
        rfl
    · have hBad : checkReturnArity retVals callee.body.returnTys = .error "return arity mismatch" := by
        simp [checkReturnArity]
        omega
      unfold runCallReq
      simp only [hFn, hAbi, requireUntypedAbi_none, checkCallArity_ok callArgs callee.body.paramTys hArity,
        Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
        Sem.rejectPoisonValues_run_ok callArgs _ s hArgsClean, hIn, hBad]
      rw [show (Outcome.ofRun (.ok (retVals, sE) : Except SemError (List Value × MachineState))).map
          (callBoundary callee.body.returnTys (saveFrame s none)) = some .typeError by
        simp [Outcome.ofRun, callBoundary, hRet]]
      rfl

/-- The behaviours of a resolved `Call` of `calleeId` on `callArgs` from
    the caller state `s` (`runCallReq`, which IS the evaluator's call
    handling by the B5 bridge theorems in `CallProps.lean`), with fuel and
    depth quantified as in `BehavesIn`. -/
def BehavesCall (ctx : EvalContext) (calleeId : FuncId) (callArgs : List Value)
    (s : MachineState) (o : Outcome) : Prop :=
  (∃ fuel depth, Outcome.ofRun
      (Sem.run (runCallReq ctx fuel depth calleeId callArgs) s) = some o) ∨
  (o = .diverges ∧ ∀ fuel depth,
      Sem.run (runCallReq ctx fuel depth calleeId callArgs) s = .error .outOfFuel)

/-- **Inlining, frame-discipline form, behaviour level.** Under panic=abort,
    for a resolved callee and well-formed, poison-free arguments, `o` is a
    behaviour of the `Call` exactly when it is the `callBoundary` image of a
    behaviour of the callee body run inline on the fresh frame. So the call
    diverges exactly when the inline body does, traps exactly as it does,
    and returns what it returns (arity- and poison-checked, with the caller's
    frame restored). -/
theorem inlining_behaves_iff
    (ctx : EvalContext) (calleeId : FuncId) (callee : EvalFunction)
    (callArgs : List Value) (s : MachineState)
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hArgsClean : callArgs.any Value.isPoison = false) (o : Outcome) :
    BehavesCall ctx calleeId callArgs s o ↔
      ∃ o', BehavesIn (ctx.forFunction callee) .abort callee.cfg callee.entryBlock callArgs
          { s with locals := ValueMap.empty, nextValueId := 0 } o' ∧
        callBoundary callee.body.returnTys (saveFrame s none) o' = o := by
  have hOut := fun fuel depth =>
    inlining_outcome ctx fuel depth calleeId callee callArgs s hFn hAbi hArity hArgsClean
  constructor
  · rintro (⟨fuel, depth, hO⟩ | ⟨rfl, hDiv⟩)
    · rw [hOut fuel depth] at hO
      cases hIn : Outcome.ofRun (Sem.run (stepNWithContext (ctx.forFunction callee) fuel depth callee.cfg
          callee.entryBlock callArgs) { s with locals := ValueMap.empty, nextValueId := 0 }) with
      | none => rw [hIn] at hO; cases hO
      | some o' =>
        rw [hIn] at hO
        exact ⟨o', Or.inl ⟨fuel, depth, hIn⟩, Option.some.inj hO⟩
    · refine ⟨.diverges, Or.inr ⟨rfl, fun fuel depth => ?_⟩, rfl⟩
      have h1 := hOut fuel depth
      rw [hDiv fuel depth] at h1
      apply (Outcome.ofRun_eq_none_iff _).mp
      cases hIn : Outcome.ofRun (Sem.run (stepNWithContext (ctx.forFunction callee) fuel depth callee.cfg
          callee.entryBlock callArgs) { s with locals := ValueMap.empty, nextValueId := 0 }) with
      | none => rfl
      | some o' => rw [hIn] at h1; cases h1
  · rintro ⟨o', (⟨fuel, depth, hO⟩ | ⟨rfl, hDiv⟩), rfl⟩
    · exact Or.inl ⟨fuel, depth, by rw [hOut fuel depth, hO]; rfl⟩
    · refine Or.inr ⟨rfl, fun fuel depth => ?_⟩
      apply (Outcome.ofRun_eq_none_iff _).mp
      rw [hOut fuel depth, hDiv fuel depth]
      rfl

-- =================================================================
-- Negative twin and mutation controls, calls executed
-- =================================================================

/-- In any context, `failingAssertCFG` panics at every positive fuel and
    every depth: the body `Assert` runs `stepInst` under panic=abort. -/
theorem failingAssertCFG_panics_in (ctx : EvalContext) (n depth : Nat) (s : MachineState) :
    Sem.run (stepNWithContext ctx (n + 1) depth failingAssertCFG ⟨0⟩ [.bool false] .abort) s
      = .error (.panic "assertion failed" none) := by trustIrReduce

/-- In any context, the asserts-deleted target returns. -/
theorem assertElim_failingAssertCFG_returns_in (ctx : EvalContext) :
    ∃ r, Sem.run (stepNWithContext ctx 1 0 (assertElim failingAssertCFG) ⟨0⟩ [.bool false] .abort)
      MachineState.empty = .ok r := by
  trustIrCompilerProof {
    change ∃ r, Sem.run (do
      bindBlockParamsChecked [(⟨0⟩, .Bool)] [.bool false]
      if let some expected := ctx.functionReturnTypes then
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected [])
        pure []
      else pure []) MachineState.empty = .ok r
    cases ctx.functionReturnTypes <;> simp only [checkFunctionItemValues_nil] <;> exact ⟨_, rfl⟩
  } {
    let bound : MachineState :=
      { MachineState.empty with locals := ValueMap.empty.set ⟨0⟩ (.bool false), nextValueId := 1 }
    refine ⟨([], bound), ?_⟩
    rw [GenericCoro.Prefix.stepNWithContext_succ_layer]
    trustIrReduce
    all_goals
      cases returns : ctx.functionReturnTypes <;>
        simp only [returns, checkFunctionItemValues_nil] <;> rfl
  }

/-- Zero fuel is `outOfFuel`, at every depth. -/
theorem stepNWithContext_zero_run (ctx : EvalContext) (depth : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (strat : PanicStrategy) (s : MachineState) :
    Sem.run (stepNWithContext ctx 0 depth cfg pc args strat) s = .error .outOfFuel := rfl

/-- A body that panics at every positive fuel and every depth has exactly
    one behaviour in the context, that panic. -/
theorem behavesIn_of_always_panics (ctx : EvalContext) (strat : PanicStrategy) (cfg : CFG)
    (pc : BlockId) (args : List Value) (s : MachineState) (msg : String)
    (site : Option PanicOutcomeSite)
    (hPanic : ∀ n depth, Sem.run (stepNWithContext ctx (n + 1) depth cfg pc args strat) s
      = .error (.panic msg site))
    (o : Outcome) (h : BehavesIn ctx strat cfg pc args s o) : o = .panics msg site := by
  rcases h with ⟨fuel, depth, hO⟩ | ⟨_, hDiv⟩
  · cases fuel with
    | zero => rw [stepNWithContext_zero_run] at hO; cases hO
    | succ n => rw [hPanic n depth] at hO; simp [Outcome.ofRun] at hO; exact hO.symm
  · have := hDiv 1 0
    rw [hPanic 0 0] at this
    cases this

/-- **Negative twin, calls executed: assertion deletion is NOT a refinement**
    in any context. The source `failingAssertCFG` panics; the target
    returns. -/
theorem assertElim_not_refines_in : ¬ behaviour_refines_in .abort assertElim := by
  intro h
  have hPanic := fun n depth =>
    failingAssertCFG_panics_in EvalContext.empty n depth MachineState.empty
  have hNoUB : ¬ BehavesIn EvalContext.empty .abort failingAssertCFG ⟨0⟩ [.bool false]
      MachineState.empty .ub := by
    intro hB
    cases behavesIn_of_always_panics _ _ _ _ _ _ _ _ hPanic _ hB
  obtain ⟨r, hr⟩ := assertElim_failingAssertCFG_returns_in EvalContext.empty
  have hSrc := h EvalContext.empty failingAssertCFG ⟨0⟩ [.bool false] MachineState.empty hNoUB
    (.returns r) (Or.inl ⟨1, 0, by rw [hr]; rfl⟩)
  cases behavesIn_of_always_panics _ _ _ _ _ _ _ _ hPanic _ hSrc

-- -----------------------------------------------------------------
-- Mutation control: a retargeted call (the intraprocedural notion is blind
-- to it)
-- -----------------------------------------------------------------

/-- A body whose one block calls `callee` with no arguments and returns its
    results. -/
def callCFG (callee : FuncId) : CFG := fun bid =>
  if bid = ⟨0⟩ then some { params := [], body := [], terminator := .Call callee [] } else none

/-- Retarget the call of `callCFG ⟨1⟩` to `⟨2⟩`; every other body is left
    alone. (Noncomputable: it decides equality of CFGs classically.) -/
noncomputable def callRetarget (cfg : CFG) : CFG :=
  @ite _ (cfg = callCFG ⟨1⟩) (Classical.propDecidable _) (callCFG ⟨2⟩) cfg

/-- Under `stepN` a call is `unsupported` whatever it calls: the runs of
    `callCFG f` and `callCFG g` agree at every fuel, block, argument list and
    state. -/
theorem stepN_callCFG_indep (f g : FuncId) (fuel : Nat) (pc : BlockId) (args : List Value)
    (s : MachineState) :
    Sem.run (stepN fuel (callCFG f) pc args) s = Sem.run (stepN fuel (callCFG g) pc args) s := by
  cases fuel with
  | zero => rfl
  | succ n =>
    by_cases hpc : pc = ⟨0⟩
    · subst hpc
      simp only [stepN, callCFG, if_pos (rfl : (⟨0⟩ : BlockId) = ⟨0⟩), if_true]
      rw [Sem.run_bind, Sem.run_bind]
      unfold stepBlock
      rw [Sem.run_bind, Sem.run_bind]
      cases Sem.run (bindBlockParams [] args) s with
      | error e => rfl
      | ok v => rfl
    · simp only [stepN, callCFG, if_neg hpc]

/-- **The intraprocedural notion admits the retarget**: `callRetarget` is a
    `behaviour_refines` transform, because under `stepN` the source and the
    target both stop at their call as `unsupported`. -/
theorem callRetarget_refines : behaviour_refines callRetarget := by
  intro cfg pc args s _ o h
  unfold callRetarget at h
  by_cases hc : cfg = callCFG ⟨1⟩
  · rw [if_pos hc] at h
    subst hc
    exact behaves_congr _ _ pc args s
      (fun fuel => stepN_callCFG_indep ⟨2⟩ ⟨1⟩ fuel pc args s) o h
  · rw [if_neg hc] at h
    exact h

/-- A callee body that panics: `const false`, then a failing `Assert`. -/
def panicCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then
    some { params := [], body := [.Const .Bool (.bool false), .Assert ⟨0⟩ .Unspecified none],
           terminator := .Return [] }
  else none

/-- The module of the retarget counter-model: function 1 returns at once,
    function 2 panics. Both take and return nothing. -/
def retargetCtx : EvalContext :=
  { EvalContext.empty with
    functions := fun f =>
      if f = ⟨1⟩ then
        some { body := { paramTys := [], returnTys := [] }, cfg := returnCFG, entryBlock := ⟨0⟩ }
      else if f = ⟨2⟩ then
        some { body := { paramTys := [], returnTys := [] }, cfg := panicCFG, entryBlock := ⟨0⟩ }
      else none }

/-- With calls executed, the source `callCFG ⟨1⟩` only ever returns or runs
    out of a resource. -/
theorem callCFG_one_returns_or_runs_out (fuel depth : Nat) (s : MachineState) :
    Sem.run (stepNWithContext retargetCtx fuel depth (callCFG ⟨1⟩) ⟨0⟩ [] .abort) s
        = .error .outOfFuel ∨
      ∃ r, Sem.run (stepNWithContext retargetCtx fuel depth (callCFG ⟨1⟩) ⟨0⟩ [] .abort) s
        = .ok r := by
  cases fuel with
  | zero => exact Or.inl rfl
  | succ n =>
    cases depth with
    | zero => exact Or.inl rfl
    | succ d =>
      cases n with
      | zero => exact Or.inl rfl
      | succ m => exact Or.inr ⟨_, rfl⟩

/-- With calls executed, the target `callCFG ⟨2⟩` panics. -/
theorem callCFG_two_panics (s : MachineState) :
    Sem.run (stepNWithContext retargetCtx 2 1 (callCFG ⟨2⟩) ⟨0⟩ [] .abort) s
      = .error (.panic "assertion failed" none) := by trustIrReduce

/-- **Mutation control: once calls are executed the retarget is refused.**
    The source returns (or runs out of a resource); the target panics. -/
theorem callRetarget_not_refines_in : ¬ behaviour_refines_in .abort callRetarget := by
  intro h
  have hSrc : ∀ o, BehavesIn retargetCtx .abort (callCFG ⟨1⟩) ⟨0⟩ [] MachineState.empty o →
      o = .diverges ∨ ∃ r, o = .returns r := by
    intro o hB
    rcases hB with ⟨fuel, depth, hO⟩ | ⟨hEq, _⟩
    · rcases callCFG_one_returns_or_runs_out fuel depth MachineState.empty with hR | ⟨r, hR⟩
      · rw [hR] at hO; cases hO
      · rw [hR] at hO; simp only [Outcome.ofRun] at hO
        exact Or.inr ⟨r, (Option.some.inj hO).symm⟩
    · exact Or.inl hEq
  have hNoUB : ¬ BehavesIn retargetCtx .abort (callCFG ⟨1⟩) ⟨0⟩ [] MachineState.empty .ub := by
    intro hB
    rcases hSrc _ hB with hE | ⟨_, hE⟩ <;> cases hE
  have hTgt : BehavesIn retargetCtx .abort (callRetarget (callCFG ⟨1⟩)) ⟨0⟩ [] MachineState.empty
      (.panics "assertion failed" none) := by
    unfold callRetarget
    rw [if_pos rfl]
    exact Or.inl ⟨2, 1, by rw [callCFG_two_panics]; rfl⟩
  rcases hSrc _ (h retargetCtx (callCFG ⟨1⟩) ⟨0⟩ [] MachineState.empty hNoUB _ hTgt)
    with hE | ⟨_, hE⟩ <;> cases hE

/-- **`behaviour_refines` does not imply `behaviour_refines_in`.** A
    refinement proved over the intraprocedural `stepN` says nothing about a
    body whose calls are executed. -/
theorem behaviour_refines_not_imp_refines_in :
    ¬ (∀ t, behaviour_refines t → behaviour_refines_in .abort t) :=
  fun h => callRetarget_not_refines_in (h callRetarget callRetarget_refines)

-- =================================================================
-- Whole-program behaviour refinement
-- =================================================================

/-- `o` is a behaviour of the program `ctx` entered at function `f` with
    `args` (`evalFunctionInContext`), with fuel AND the context's call-depth
    budget quantified: the budget is a resource, so the program's behaviour
    does not depend on the `maxCallDepth` it happens to carry. -/
def BehavesFn (ctx : EvalContext) (strat : PanicStrategy) (f : FuncId) (args : List Value)
    (s : MachineState) (o : Outcome) : Prop :=
  (∃ fuel depth, Outcome.ofRun (Sem.run
      (evalFunctionInContext { ctx with maxCallDepth := depth } f args fuel strat) s) = some o) ∨
  (o = .diverges ∧ ∀ fuel depth, Sem.run
      (evalFunctionInContext { ctx with maxCallDepth := depth } f args fuel strat) s
        = .error .outOfFuel)

/-- **Whole-program behaviour refinement** of a context transform: for every
    entry function, arguments and state whose source run is UB-free, every
    behaviour of the transformed program is one of the source. -/
def program_refines (strat : PanicStrategy) (transform : EvalContext → EvalContext) : Prop :=
  ∀ ctx f args s, ¬ BehavesFn ctx strat f args s .ub →
    ∀ o, BehavesFn (transform ctx) strat f args s o → BehavesFn ctx strat f args s o

/-- Every program has a behaviour from every entry. -/
theorem behavesFn_nonempty (ctx : EvalContext) (strat : PanicStrategy) (f : FuncId)
    (args : List Value) (s : MachineState) : ∃ o, BehavesFn ctx strat f args s o := by
  by_cases hDiv : ∀ fuel depth, Sem.run
      (evalFunctionInContext { ctx with maxCallDepth := depth } f args fuel strat) s
        = .error .outOfFuel
  · exact ⟨.diverges, Or.inr ⟨rfl, hDiv⟩⟩
  · have ⟨fuel, hFuel⟩ := Classical.not_forall.mp hDiv
    have ⟨depth, hDepth⟩ := Classical.not_forall.mp hFuel
    cases hO : Outcome.ofRun (Sem.run
        (evalFunctionInContext { ctx with maxCallDepth := depth } f args fuel strat) s) with
    | none => exact absurd ((Outcome.ofRun_eq_none_iff _).mp hO) hDepth
    | some o => exact ⟨o, Or.inl ⟨fuel, depth, hO⟩⟩

/-- The identity context transform is a whole-program refinement. -/
theorem id_program_refines (strat : PanicStrategy) : program_refines strat (fun ctx => ctx) := by
  intro _ _ _ _ _ o h
  exact h

/-- Whole-program refinement composes. -/
theorem compose_program_refines (strat : PanicStrategy) (t1 t2 : EvalContext → EvalContext)
    (h1 : program_refines strat t1) (h2 : program_refines strat t2) :
    program_refines strat (fun ctx => t2 (t1 ctx)) := by
  intro ctx f args s hNoUB o h
  have hNoUB1 : ¬ BehavesFn (t1 ctx) strat f args s .ub :=
    fun hUB => hNoUB (h1 ctx f args s hNoUB .ub hUB)
  exact h1 ctx f args s hNoUB o (h2 (t1 ctx) f args s hNoUB1 o h)

/-- **Mutation control: the call-depth budget is a resource.** Changing a
    context's `maxCallDepth` is a whole-program refinement (both ways), so a
    transform that changes how deep a program calls (inlining, outlining) is
    not refused merely for that. A definition that read the depth from the
    context, as `evalFunctionInContext` alone does, would refuse it: at
    budget 0 every call runs out (`callProgram_zero_budget_runs_out`), so a
    returning program (`callProgram_returns`) would appear to diverge
    (`withMaxCallDepth_not_fixedDepth_refines`). -/
theorem withMaxCallDepth_program_refines (strat : PanicStrategy) (n : Nat) :
    program_refines strat (fun ctx => { ctx with maxCallDepth := n }) := by
  intro _ _ _ _ _ o h
  exact h

/-- The program of the depth control: `retargetCtx` extended with function
    0, the body `callCFG ⟨1⟩`, which calls function 1. -/
def callProgramCtx (depth : Nat) : EvalContext :=
  { retargetCtx with
    maxCallDepth := depth
    functions := fun f =>
      if f = ⟨0⟩ then
        some { body := { paramTys := [], returnTys := [] }, cfg := callCFG ⟨1⟩, entryBlock := ⟨0⟩ }
      else retargetCtx.functions f }

/-- With a call-depth budget of 1 the program returns. -/
theorem callProgram_returns :
    ∃ r, Sem.run (evalFunctionInContext (callProgramCtx 1) ⟨0⟩ [] 2 .abort) MachineState.empty
      = .ok r := ⟨_, rfl⟩

/-- With a call-depth budget of 0 it runs out at every fuel. -/
theorem callProgram_zero_budget_runs_out (fuel : Nat) (s : MachineState) :
    Sem.run (evalFunctionInContext (callProgramCtx 0) ⟨0⟩ [] fuel .abort) s
      = .error .outOfFuel := by
  cases fuel with
  | zero => rfl
  | succ n => rfl

-- =================================================================
-- Review: divergence is observable with calls executed
-- =================================================================

/-- `returnCFG` returns at every positive fuel and every depth, in every
    context. -/
theorem returnCFG_returns_in (ctx : EvalContext) (n depth : Nat) (s : MachineState) :
    ∃ r, Sem.run (stepNWithContext ctx (n + 1) depth returnCFG ⟨0⟩ [] .abort) s = .ok r := by
  change ∃ r, Sem.run (do
    if let some expected := ctx.functionReturnTypes then
      let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected [])
      pure []
    else pure []) s = .ok r
  cases ctx.functionReturnTypes <;> simp only [checkFunctionItemValues_nil] <;> exact ⟨_, rfl⟩

/-- Every behaviour of `returnCFG` in a context is a return: it never traps,
    is never UB and never diverges. -/
theorem returnCFG_behavesIn_returns (ctx : EvalContext) (s : MachineState) (o : Outcome)
    (h : BehavesIn ctx .abort returnCFG ⟨0⟩ [] s o) : ∃ r, o = .returns r := by
  rcases h with ⟨fuel, depth, hO⟩ | ⟨_, hDiv⟩
  · cases fuel with
    | zero => rw [stepNWithContext_zero_run] at hO; cases hO
    | succ n =>
      obtain ⟨r, hr⟩ := returnCFG_returns_in ctx n depth s
      rw [hr] at hO
      simp only [Outcome.ofRun] at hO
      exact ⟨r, (Option.some.inj hO).symm⟩
  · obtain ⟨r, hr⟩ := returnCFG_returns_in ctx 0 0 s
    rw [hDiv 1 0] at hr
    cases hr

/-- A transform into `target` is refused once `target` diverges (at every
    fuel and depth) in a context where the terminating `returnCFG` runs. -/
theorem diverging_target_not_refines_in (ctx : EvalContext) (target : CFG)
    (hDiv : ∀ fuel depth, Sem.run (stepNWithContext ctx fuel depth target ⟨0⟩ [] .abort)
      MachineState.empty = .error .outOfFuel) :
    ¬ behaviour_refines_in .abort (fun _ => target) := by
  intro h
  have hNoUB : ¬ BehavesIn ctx .abort returnCFG ⟨0⟩ [] MachineState.empty .ub := by
    intro hB
    obtain ⟨_, hE⟩ := returnCFG_behavesIn_returns ctx _ _ hB
    cases hE
  obtain ⟨_, hE⟩ := returnCFG_behavesIn_returns ctx _ _
    (h ctx returnCFG ⟨0⟩ [] MachineState.empty hNoUB .diverges (Or.inr ⟨rfl, hDiv⟩))
  cases hE

/-- `loopCFG` runs out at every fuel and every depth, in every context. -/
theorem loopCFG_diverges_in (ctx : EvalContext) (fuel depth : Nat) (s : MachineState) :
    Sem.run (stepNWithContext ctx fuel depth loopCFG ⟨0⟩ [] .abort) s = .error .outOfFuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    have hStep : ∃ s', Sem.run (stepNWithContext ctx (n + 1) depth loopCFG ⟨0⟩ [] .abort) s
        = Sem.run (stepNWithContext ctx n depth loopCFG ⟨0⟩ [] .abort) s' := ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ := hStep
    rw [hs']
    exact ih s'

/-- **Review control: a loop is refused with calls executed.** The in-context
    twin of `loop_not_refines`: a definition weakened to terminating target
    outcomes would admit replacing every body by a self-loop. -/
theorem loop_not_refines_in : ¬ behaviour_refines_in .abort (fun _ => loopCFG) :=
  diverging_target_not_refines_in EvalContext.empty loopCFG
    (fun fuel depth => loopCFG_diverges_in _ fuel depth _)

/-- A module whose function 0 is the body `callCFG ⟨0⟩`: it calls itself,
    unboundedly. -/
def selfCallCtx : EvalContext :=
  { EvalContext.empty with
    functions := fun f =>
      if f = ⟨0⟩ then
        some { body := { paramTys := [], returnTys := [] }, cfg := callCFG ⟨0⟩, entryBlock := ⟨0⟩ }
      else none }

/-- Unbounded recursion runs out of a resource at every fuel and every call
    depth: each call spends one level of depth and one block of fuel, so the
    run never terminates whatever budget it is given. -/
theorem selfCall_runs_out (fuel depth : Nat) (s : MachineState) :
    Sem.run (stepNWithContext selfCallCtx fuel depth (callCFG ⟨0⟩) ⟨0⟩ [] .abort) s
      = .error .outOfFuel := by
  have runs (fuel : Nat) : ∀ depth returns s,
      Sem.run (stepNWithContext { selfCallCtx with functionReturnTypes := returns }
        fuel depth (callCFG ⟨0⟩) ⟨0⟩ [] .abort) s = .error .outOfFuel := by
    induction fuel with
    | zero => intro _ _ _; rfl
    | succ n ih =>
      intro depth returns s
      cases depth with
      | zero => rfl
      | succ d =>
        rw [stepNWithContext_callReq_eq_runCallReq
          { selfCallCtx with functionReturnTypes := returns } n d (callCFG ⟨0⟩) ⟨0⟩ [] []
          ⟨0⟩ [] rfl]
        exact inlining_error_transfer { selfCallCtx with functionReturnTypes := returns }
          n d ⟨0⟩ _ [] s .outOfFuel rfl rfl rfl rfl (ih d (some []) _)
  exact runs fuel depth none s

/-- **Review control: unbounded recursion is divergence.** Replacing a
    returning body by a call that recurses forever is refused: call depth is
    quantified like fuel, so running out of depth at every budget is the
    `diverges` behaviour, not the absence of one. A definition that read only
    terminating outcomes, or that treated a depth-exhausted run as no
    behaviour, would admit this transform vacuously. -/
theorem recursion_not_refines_in : ¬ behaviour_refines_in .abort (fun _ => callCFG ⟨0⟩) :=
  diverging_target_not_refines_in selfCallCtx (callCFG ⟨0⟩)
    (fun fuel depth => selfCall_runs_out fuel depth _)

/-- The `panicToLoop` target diverges with calls executed. -/
theorem panicToLoop_failingAssertBrCFG_diverges_in (fuel depth : Nat) (s : MachineState) :
    Sem.run (stepNWithContext EvalContext.empty fuel depth (panicToLoop failingAssertBrCFG)
      ⟨0⟩ [.bool false] .abort) s = .error .outOfFuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    have hStep : ∃ s', Sem.run (stepNWithContext EvalContext.empty (n + 1) depth
          (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false] .abort) s
        = Sem.run (stepNWithContext EvalContext.empty n depth
          (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false] .abort) s' := by
      trustIrCompilerProof { exact ⟨_, rfl⟩ } {
        let bound : MachineState :=
          { s with
            locals := s.locals.set ⟨0⟩ (.bool false)
            nextValueId := if s.nextValueId ≤ 1 then 1 else s.nextValueId }
        have one (recurse : GenericCoro.Prefix.Recurse) :
            Sem.run (GenericCoro.Prefix.evalLayer recurse EvalContext.empty depth
              (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false] .abort) s =
              Sem.run (recurse EvalContext.empty depth
                (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false] .abort) bound := by
          dsimp only [bound]
          trustIrReduce
          congr 1 <;> trustIrReduce
        refine ⟨bound, ?_⟩
        rw [GenericCoro.Prefix.stepNWithContext_succ_layer]
        exact one _
      }
    obtain ⟨s', hs'⟩ := hStep
    rw [hs']
    exact ih s'

/-- **Review control: trap-to-divergence is refused with calls executed.** The
    in-context twin of `panicToLoop_not_refines`: the source panics, the
    target loops. It pins the divergence clause on its own, since the source
    never returns. -/
theorem panicToLoop_not_refines_in : ¬ behaviour_refines_in .abort panicToLoop := by
  intro h
  have hPanic : ∀ n depth, Sem.run (stepNWithContext EvalContext.empty (n + 1) depth
      failingAssertBrCFG ⟨0⟩ [.bool false] .abort) MachineState.empty
        = .error (.panic "assertion failed" none) := by
    trustIrCompilerProof { exact fun _ _ => rfl } { exact fun _ _ => by trustIrReduce }
  have hNoUB : ¬ BehavesIn EvalContext.empty .abort failingAssertBrCFG ⟨0⟩ [.bool false]
      MachineState.empty .ub := by
    intro hB
    cases behavesIn_of_always_panics _ _ _ _ _ _ _ _ hPanic _ hB
  have hSrc := h EvalContext.empty failingAssertBrCFG ⟨0⟩ [.bool false] MachineState.empty hNoUB
    .diverges (Or.inr ⟨rfl, fun fuel depth =>
      panicToLoop_failingAssertBrCFG_diverges_in fuel depth _⟩)
  cases behavesIn_of_always_panics _ _ _ _ _ _ _ _ hPanic _ hSrc

-- -----------------------------------------------------------------
-- Review: the depth-budget control, as a theorem
-- -----------------------------------------------------------------

/-- The MUTANT of `BehavesFn`: fuel quantified, but the call-depth budget READ
    from the context (`evalFunctionInContext` alone). Kept only to refute it. -/
def BehavesFnFixedDepth (ctx : EvalContext) (strat : PanicStrategy) (f : FuncId)
    (args : List Value) (s : MachineState) (o : Outcome) : Prop :=
  (∃ fuel, Outcome.ofRun (Sem.run (evalFunctionInContext ctx f args fuel strat) s) = some o) ∨
  (o = .diverges ∧ ∀ fuel,
    Sem.run (evalFunctionInContext ctx f args fuel strat) s = .error .outOfFuel)

/-- `program_refines` over the mutant `BehavesFnFixedDepth`. -/
def program_refines_fixedDepth (strat : PanicStrategy)
    (transform : EvalContext → EvalContext) : Prop :=
  ∀ ctx f args s, ¬ BehavesFnFixedDepth ctx strat f args s .ub →
    ∀ o, BehavesFnFixedDepth (transform ctx) strat f args s o →
      BehavesFnFixedDepth ctx strat f args s o

/-- With a call-depth budget of 1 the depth-control program only returns or
    runs out of fuel. -/
theorem callProgram_one_returns_or_runs_out (fuel : Nat) (s : MachineState) :
    Sem.run (evalFunctionInContext (callProgramCtx 1) ⟨0⟩ [] fuel .abort) s = .error .outOfFuel ∨
      ∃ r, Sem.run (evalFunctionInContext (callProgramCtx 1) ⟨0⟩ [] fuel .abort) s = .ok r := by
  cases fuel with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inl rfl
    | succ m => exact Or.inr ⟨_, rfl⟩

/-- **Review control: reading the depth budget from the context refuses a
    depth-only change.** Under the mutant definition, lowering the budget of a
    program that returns makes it diverge, so the transform that
    `withMaxCallDepth_program_refines` admits is refused. This is the
    refutation that docstring describes, as a theorem. -/
theorem withMaxCallDepth_not_fixedDepth_refines :
    ¬ program_refines_fixedDepth .abort (fun ctx => { ctx with maxCallDepth := 0 }) := by
  intro h
  have hSrc : ∀ o, BehavesFnFixedDepth (callProgramCtx 1) .abort ⟨0⟩ [] MachineState.empty o →
      ∃ r, o = .returns r := by
    intro o hB
    rcases hB with ⟨fuel, hO⟩ | ⟨_, hDiv⟩
    · rcases callProgram_one_returns_or_runs_out fuel MachineState.empty with hR | ⟨r, hR⟩
      · rw [hR] at hO; cases hO
      · rw [hR] at hO; simp only [Outcome.ofRun] at hO
        exact ⟨r, (Option.some.inj hO).symm⟩
    · obtain ⟨r, hr⟩ := callProgram_returns
      rw [hDiv 2] at hr
      cases hr
  have hNoUB : ¬ BehavesFnFixedDepth (callProgramCtx 1) .abort ⟨0⟩ [] MachineState.empty .ub :=
    fun hB => by obtain ⟨_, hE⟩ := hSrc _ hB; cases hE
  have hTgt : BehavesFnFixedDepth { callProgramCtx 1 with maxCallDepth := 0 } .abort ⟨0⟩ []
      MachineState.empty .diverges :=
    Or.inr ⟨rfl, fun fuel => callProgram_zero_budget_runs_out fuel MachineState.empty⟩
  obtain ⟨_, hE⟩ := hSrc _ (h (callProgramCtx 1) ⟨0⟩ [] MachineState.empty hNoUB _ hTgt)
  cases hE

-- Drop resolution retains its original constructive footprint on both pins.
#trustIrAxiomsExact resolveDrop_mapFunctionCFGs == []

end TrustIr
