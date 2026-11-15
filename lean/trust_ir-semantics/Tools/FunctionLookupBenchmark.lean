-- Copyright 2026 Andrew Yates | Apache-2.0
-- Native timing observer for actual decoded-context preparation and lookup.
-- No proof authority; source/request identities are retained by the driver.
import TrustIrRuntime
import TrustIrEval.Run

open TrustIr TrustIrEval

@[noinline] private def sample (ctx : EvalContext) (mode query : Nat) : Nat :=
  let id : FuncId := ⟨query⟩
  if mode == 0 then
    match ctx.functions id with | some f => f.entryBlock.index + 1 | none => 0
  else if mode == 1 then
    match ctx.functionErrors id with | some _ => 1 | none => 0
  else if mode == 2 then
    if ctx.declared id then 1 else 0
  else
    (match ctx.functions id with | some f => f.entryBlock.index + 1 | none => 0) +
    (match ctx.functionErrors id with | some _ => 1 | none => 0) +
    (if ctx.declared id then 1 else 0)

private def warm (ctx : EvalContext) (mode count : Nat) (queries : Array Nat) : IO (Nat × Nat) := do
  -- The external reference survives the stop timestamp, including the last
  -- warm mode. A post-timestamp opaque IO read makes retention explicit.
  let keeper ← IO.mkRef ctx
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for i in [:count] do
    checksum := checksum + sample ctx mode (queries[i % queries.size]!)
  let stop ← IO.monoNanosNow
  let retained ← keeper.get
  pure (stop - start, checksum + retained.maxCallDepth)

private def lifecycle (source : TrustIrEval.Module) (count : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for i in [:count] do
    -- Vary the actual scalar context field to keep preparation dependent on
    -- each iteration. The source AST and all lookup results remain fixed.
    match contextOf source (8 + i % 2) with
    | .error _ => throw (IO.userError "context preparation refused benchmark source")
    | .ok ctx => checksum := checksum + ctx.maxCallDepth + sample ctx 3 0
  let stop ← IO.monoNanosNow
  pure (stop - start, checksum)

/-- Build the actual contexts and retain all of them. This helper has no
    lookup probe. The caller measures construction plus retention-container
    overhead, with release after its stopping timestamp. -/
@[noinline] private def preparedContexts (source : TrustIrEval.Module) (count : Nat) :
    IO (Array EvalContext) := do
  let mut contexts := #[]
  for i in [:count] do
    match contextOf source (8 + i % 2) with
    | .error _ => throw (IO.userError "context preparation refused benchmark source")
    | .ok context => contexts := contexts.push context
  pure contexts

private def constructor (source : TrustIrEval.Module) (count : Nat) : IO (Nat × Nat) := do
  let keeper ← IO.mkRef (#[] : Array EvalContext)
  let start ← IO.monoNanosNow
  let contexts ← preparedContexts source count
  keeper.set contexts
  let stop ← IO.monoNanosNow
  let retained ← keeper.get
  let checksum := retained.foldl (fun sum context => sum + context.maxCallDepth) 0
  pure (stop - start, checksum)

def main (argv : List String) : IO UInt32 := do
  match argv with
  | [path, queryCountText, coldCountText] =>
    let some queryCount := queryCountText.toNat? | throw (IO.userError "query count")
    let some coldCount := coldCountText.toNat? | throw (IO.userError "cold count")
    let text ← IO.FS.readFile path
    let .ok json := Lean.Json.parse text | throw (IO.userError "request JSON")
    let .ok batches := listField json "batches" | throw (IO.userError "batches")
    let some first := batches.head? | throw (IO.userError "empty batches")
    let .ok moduleJson := field first "module" | throw (IO.userError "module field")
    let .ok source := TrustIrEval.module moduleJson | throw (IO.userError "module decode")
    let .ok ctx := contextOf source 8 | throw (IO.userError "context decode")
    let some last := source.functions.getLast? | throw (IO.userError "empty function table")
    let queries := #[last.id.index, 4294967294, 0]
    let (constructorNs, constructorChecksum) ← constructor source coldCount
    let (lifecycleNs, lifecycleChecksum) ← lifecycle source coldCount
    let (functionsNs, functionsChecksum) ← warm ctx 0 queryCount queries
    let (errorsNs, errorsChecksum) ← warm ctx 1 queryCount queries
    let (declaredNs, declaredChecksum) ← warm ctx 2 queryCount queries
    let (mixedNs, mixedChecksum) ← warm ctx 3 queryCount queries
    IO.println (Lean.Json.compress (obj [
      ("source_functions", jnat source.functions.length), ("queries", jnat queryCount),
      ("cold_preparations", jnat coldCount),
      ("query_ids", .arr (queries.map jnat)),
      ("constructor_retained_ns", jnat constructorNs),
      ("lifecycle_ns", jnat lifecycleNs),
      ("functions_ns", jnat functionsNs), ("errors_ns", jnat errorsNs),
      ("declared_ns", jnat declaredNs), ("mixed_ns", jnat mixedNs),
      ("checksum", jnat (constructorChecksum + lifecycleChecksum + functionsChecksum + errorsChecksum +
        declaredChecksum + mixedChecksum))]))
    pure 0
  | _ =>
    IO.eprintln "usage: trustir_lookup_bench REQUEST.json WARM_QUERY_COUNT COLD_PREPARATION_COUNT"
    pure 2
