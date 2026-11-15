-- Copyright 2026 Andrew Yates | Apache-2.0
-- Metadata checks only; no runtime correspondence or proof-promotion verdict.
import Lean
import TrustIr.Semantics.AggregateImages
import TrustIr.Semantics.Compare
import TrustIr.Semantics.Cast
import TrustIr.Semantics.Step
import TrustIr.Semantics.Eval
import TrustIr.Proofs.ByteMemory

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for module in env.header.moduleNames do
    if module.toString.startsWith "TrustIrRuntime" then
      throwError "runtime module leaked into logical import closure: {module}"
  let original : List String := [
  "TrustIr.AggregateMemory.ArrayEncodingRuntime.encodeTree",
  "TrustIr.AggregateMemory.ArrayEncodingRuntime.encodeTreeWithStats",
  "TrustIr.ByteImage.ImageMapRuntime.map",
  "TrustIr.ByteImage.WindowRuntime.checkBlocks",
  "TrustIr.ByteImage.WindowRuntime.checkBlocksWithStats",
  "TrustIr.ByteImage.WindowRuntime.firstWhere",
  "TrustIr.ByteImage.WindowRuntime.firstWhereWithStats",
  "TrustIr.ByteImage.WindowRuntime.mapBlocks",
  "TrustIr.ByteImage.WindowRuntime.mapBlocksWithStats",
  "TrustIr.CompactArray.EqualityRuntime.tree",
  "TrustIr.CompactArray.EqualityRuntime.treeWithStats",
  "TrustIr.CompactArray.StoredCheckRuntime.leaf",
  "TrustIr.CompactArray.StoredCheckRuntime.leafRange",
  "TrustIr.CompactArray.StoredCheckRuntime.range",
  "TrustIr.CompactArray.StoredCheckRuntime.rangeWithStats",
  "TrustIr.CompactArray.StoredCheckRuntime.tree",
  "TrustIr.CompactArray.StoredCheckRuntime.treeWithStats",
  "TrustIr.ValueDepthRuntime.depthWithStats",
  "TrustIr.ValueDepthRuntime.fieldDepth",
  "TrustIr.ValueDepthRuntime.leafDepth",
  "TrustIr.ValueDepthRuntime.listDepth",
  "TrustIr.ValueDepthRuntime.treeDepth",
  "TrustIr.ValueDepthRuntime.valueDepth",
  "_private.TrustIr.Semantics.AggregateImages.0.TrustIr.AggregateMemory.ArrayEncodingRuntime.key",
  "_private.TrustIr.Semantics.AggregateImages.0.TrustIr.AggregateMemory.ArrayEncodingRuntime.visit",
  "_private.TrustIr.State.ByteImage.0.TrustIr.ByteImage.ImageMapRuntime.uncached",
  "_private.TrustIr.State.ByteImage.0.TrustIr.ByteImage.ImageMapRuntime.visit",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.Window.key",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.checkBody",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.checkVisit",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.mapBody",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.mapVisit",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.search",
  "_private.TrustIr.State.ByteImageTraversal.0.TrustIr.ByteImage.WindowRuntime.searchBody",
  "_private.TrustIr.State.CompactArray.0.TrustIr.CompactArray.EqualityRuntime.key",
  "_private.TrustIr.State.CompactArray.0.TrustIr.CompactArray.EqualityRuntime.visit",
  "_private.TrustIr.State.CompactArray.0.TrustIr.CompactArray.StoredCheckRuntime.key",
  "_private.TrustIr.State.CompactArray.0.TrustIr.CompactArray.StoredCheckRuntime.visit",
  "_private.TrustIr.State.ValueMap.0.TrustIr.ValueDepthRuntime.key",
  "_private.TrustIr.State.ValueMap.0.TrustIr.ValueDepthRuntime.run",
  "_private.TrustIr.State.ValueMap.0.TrustIr.ValueDepthRuntime.visit"
]
  for text in original do
    if env.constants.toList.any (fun pair => pair.1.toString == text) then
      throwError "original unsafe runtime declaration still enters logical environment: {text}"
  logInfo "RUNTIME_LOGICAL_IMPORT_BOUNDARY_PASS original_unsafe_absent=41"
