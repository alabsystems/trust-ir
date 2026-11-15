-- Copyright 2026 Andrew Yates | Apache-2.0
-- Source-only phase observer for actual decoded CFG construction and lookup.
-- No proof, execution-equivalence, native-authority, or performance claim.
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval

private structure CFGMeasurement where
  elapsedNs : Nat
  checksum : Nat
  retainedChecksum : Nat := 0

private def requireDecoded {α : Type} (label : String) (result : D α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {repr error}")

private def readJSON (path : String) : IO Lean.Json := do
  let text ← IO.FS.readFile path
  match Lean.Json.parse text with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: {error}")

/-- Consume returned metadata from the actual converted function's CFG. -/
@[noinline] private def cfgSample (function : EvalFunction) (query : Nat) : Nat :=
  match function.cfg ⟨query⟩ with
  | none => 0
  | some block =>
    1 + block.params.length + block.body.length + block.bodyResultDests.length +
      block.terminatorResultDests.length

/-- The lifecycle includes the original ID-0 function/error/declaration probe. -/
@[noinline] private def mixedContextSample (ctx : EvalContext) : Nat :=
  (match ctx.functions ⟨0⟩ with | some function => function.entryBlock.index + 1 | none => 0) +
  (match ctx.functionErrors ⟨0⟩ with | some _ => 1 | none => 0) +
  (if ctx.declared ⟨0⟩ then 1 else 0)

private def decodedSample (source : TrustIrEval.Module) : Nat :=
  source.functions.foldl (fun sum function =>
    sum + function.id.index + function.entry.index + 1 +
      (match function.blocks with | .ok blocks => blocks.length | .error _ => 0)) 0

private def warmCFG (function : EvalFunction) (queries : Array Nat) (repetitions : Nat) :
    IO CFGMeasurement := do
  let keeper ← IO.mkRef function
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:repetitions] do
    for query in queries do
      checksum := checksum + cfgSample function query
  let stop ← IO.monoNanosNow
  -- Retain the whole converted function, including its real CFG closure,
  -- through STOP. The post-STOP opaque read has a separately reported marker.
  let retained ← keeper.get
  pure
    { elapsedNs := stop - start
      checksum := checksum
      retainedChecksum := retained.entryBlock.index + retained.body.returnTys.length + 1 }

private def decodeRetained (moduleJSON : Lean.Json) (count : Nat) : IO CFGMeasurement := do
  let input ← IO.mkRef moduleJSON
  let keeper ← IO.mkRef (#[] : Array TrustIrEval.Module)
  let start ← IO.monoNanosNow
  let mut modules := #[]
  for _ in [:count] do
    -- Each actual decode consumes a fresh opaque IO read of the fixed input.
    -- JSON parsing and request-file I/O are outside this phase.
    let currentJSON ← input.get
    let source ← requireDecoded "retained module decode" (TrustIrEval.module currentJSON)
    modules := modules.push source
  keeper.set modules
  let stop ← IO.monoNanosNow
  let retained ← keeper.get
  pure
    { elapsedNs := stop - start
      checksum := retained.foldl (fun sum source => sum + decodedSample source) 0
      retainedChecksum := retained.size }

/-- Actual complete contexts, with no lookup probe in the construction loop.
    The caller retains the Array and releases it after its STOP timestamp. -/
@[noinline] private def preparedCFGContexts (source : TrustIrEval.Module) (count : Nat) :
    IO (Array EvalContext) := do
  let mut contexts := #[]
  for i in [:count] do
    let context ← requireDecoded "retained context preparation" (contextOf source (8 + i % 2))
    contexts := contexts.push context
  pure contexts

private def contextRetained (source : TrustIrEval.Module) (count : Nat) : IO CFGMeasurement := do
  let keeper ← IO.mkRef (#[] : Array EvalContext)
  let start ← IO.monoNanosNow
  let contexts ← preparedCFGContexts source count
  keeper.set contexts
  let stop ← IO.monoNanosNow
  let retained ← keeper.get
  pure
    { elapsedNs := stop - start
      checksum := retained.foldl (fun sum context => sum + context.maxCallDepth) 0
      retainedChecksum := retained.size }

private def contextLifecycle (source : TrustIrEval.Module) (count : Nat) : IO CFGMeasurement := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for i in [:count] do
    let context ← requireDecoded "context lifecycle" (contextOf source (8 + i % 2))
    checksum := checksum + context.maxCallDepth + mixedContextSample context
  let stop ← IO.monoNanosNow
  pure { elapsedNs := stop - start, checksum }

private def phaseJSON (phase : CFGMeasurement) : Lean.Json :=
  obj [("nanoseconds", jnat phase.elapsedNs), ("checksum", jnat phase.checksum),
    ("retained_checksum", jnat phase.retainedChecksum)]

private def caseMetadata (inventory : Lean.Json) (caseKey : String) : IO Lean.Json := do
  let cases ← requireDecoded "inventory cases" (listField inventory "cases")
  let matchingRows := cases.filter (fun row =>
    match strField row "path" with | .ok key => key == caseKey | .error _ => false)
  let [metadata] := matchingRows | throw (IO.userError "expected exactly one inventory case key")
  pure metadata

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [path, inventoryPath, caseKey, repetitionsText, coldCountText] =>
    let some repetitions := repetitionsText.toNat? | throw (IO.userError "warm repetitions")
    let some coldCount := coldCountText.toNat? | throw (IO.userError "cold count")
    if repetitions == 0 || coldCount == 0 then
      throw (IO.userError "phase counts must be positive")
    let request ← readJSON path
    let inventory ← readJSON inventoryPath
    let metadata ← caseMetadata inventory caseKey
    let queryList ← requireDecoded "metadata queries" (do
      (← listField metadata "queries").mapM (nat "query"))
    let [lastKey, missingKey, firstKey] := queryList
      | throw (IO.userError "expected metadata [last, missing, first]")
    let queries := queryList.toArray
    let fuel ← requireDecoded "request fuel" (natField request "fuel")
    let depth ← requireDecoded "request depth" (natField request "call_depth")
    if fuel != 20000 || depth != 8 then
      throw (IO.userError "observer requires the frozen V2 fuel20000/depth8 requests")
    let [batch] ← requireDecoded "request batches" (listField request "batches")
      | throw (IO.userError "expected one batch")
    let [run] ← requireDecoded "batch runs" (listField batch "runs")
      | throw (IO.userError "expected one run")
    let entry ← requireDecoded "run entry" (natField run "function")
    let args ← requireDecoded "run arguments" (listField run "args")
    let choices ← requireDecoded "run choices" (listField run "float_zero_choices")
    if entry != 0 || !args.isEmpty || !choices.isEmpty then
      throw (IO.userError "expected argument-free function0 and empty choice tape")
    let moduleJSON ← requireDecoded "module field" (field batch "module")
    let source ← requireDecoded "module decode" (TrustIrEval.module moduleJSON)
    let [rawFunction] := source.functions | throw (IO.userError "expected one source function")
    if rawFunction.id.index != 0 || rawFunction.isDeclaration then
      throw (IO.userError "expected source definition0")
    let blocks ← requireDecoded "source blocks" rawFunction.blocks
    let some first := blocks.head? | throw (IO.userError "empty source blocks")
    let some last := blocks.getLast? | throw (IO.userError "empty source blocks")
    let blockCount ← requireDecoded "metadata block count" (natField metadata "blocks")
    if blockCount != blocks.length || firstKey != first.fst.index || lastKey != last.fst.index ||
        missingKey != 4294967294 || blocks.any (fun row => row.fst.index == missingKey) then
      throw (IO.userError "metadata query IDs/count do not match the actual source rows")
    let ctx ← requireDecoded "context preparation" (contextOf source 8)
    let pointerBits := match ctx.byteModel with | .le32 => 32 | .le64 => 64
    let metadataBits ← requireDecoded "metadata pointer width" (natField metadata "bits")
    if pointerBits != metadataBits then
      throw (IO.userError "metadata pointer width does not match the actual context")
    -- Force actual conversion and metadata inference once before warm timing.
    let some function := ctx.functions ⟨0⟩
      | throw (IO.userError "actual converted function0 is absent")
    if (function.cfg ⟨lastKey⟩).isNone || (function.cfg ⟨firstKey⟩).isNone ||
        (function.cfg ⟨missingKey⟩).isSome then
      throw (IO.userError "actual converted CFG does not match presence metadata")
    let decode ← decodeRetained moduleJSON coldCount
    let constructor ← contextRetained source coldCount
    let lifecycle ← contextLifecycle source coldCount
    let warm ← warmCFG function queries repetitions
    IO.println (Lean.Json.compress (obj [
      ("observer_version", .str "decoded-cfg-phases-v1"), ("case", .str caseKey),
      ("source_blocks", jnat blockCount), ("function_id", jnat entry),
      ("pointer_bits", jnat pointerBits),
      ("request_fuel", jnat fuel), ("request_depth", jnat depth),
      ("warm_loop_repetitions", jnat repetitions),
      ("warm_query_count", jnat (repetitions * queries.size)),
      ("cold_preparations", jnat coldCount),
      ("constructor_depth_base", jnat 8), ("constructor_depth_modulus", jnat 2),
      ("query_ids", .arr (queries.map jnat)),
      ("decode_retained", phaseJSON decode), ("context_retained", phaseJSON constructor),
      ("context_lifecycle", phaseJSON lifecycle), ("warm_cfg", phaseJSON warm),
      ("request_json_parse_timed", .bool false),
      ("program_execution_or_native_authority_claim", .bool false)]))
    pure 0
  | _ =>
    IO.eprintln "usage: trustir_cfg_bench REQUEST.json INVENTORY.json CASE_KEY WARM_REPETITION_COUNT COLD_PREPARATION_COUNT"
    pure 2
