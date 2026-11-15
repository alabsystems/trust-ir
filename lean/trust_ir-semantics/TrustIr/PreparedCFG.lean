-- Copyright 2026 Andrew Yates | Apache-2.0
-- Shared computational CFG preparation. No proof-stack or decoder import.
import TrustIr.Semantics.Eval

namespace TrustIr.GenericCoro.IndexedCFG

/-- Insert only on the first occurrence. Later duplicates keep the already
    stored block; construction uses the native index without a tree view. -/
def insertFirst (index : NatIndex BasicBlock) (key : Nat) (block : BasicBlock) :
    NatIndex BasicBlock :=
  match index.find? key with
  | some _ => index
  | none => index.insert key block

/-- Tail-recursive single forward traversal. The retained index is passed
    directly to the next row; no reverse list or repeated source scan occurs. -/
def prepareFrom : List (BlockId × BasicBlock) → NatIndex BasicBlock → NatIndex BasicBlock
  | [], index => index
  | (id, block) :: rest, index => prepareFrom rest (insertFirst index id.index block)

def prepare (blocks : List (BlockId × BasicBlock)) : NatIndex BasicBlock :=
  prepareFrom blocks NatIndex.empty

/-- A data result is deliberate: a CFG-valued builder is eta-expanded by
    Lean4.8 and would rebuild on each query. This carrier retains the computed
    index and its closure before callers extract the actual CFG. -/
structure PreparedCFG where
  index : NatIndex BasicBlock
  cfg : CFG

/-- Build once, then capture only the prepared native index in the query
    closure. Consumers retain this data result and use its cfg field. -/
def indexedCFG (blocks : List (BlockId × BasicBlock)) : PreparedCFG :=
  let index := prepare blocks
  { index := index, cfg := fun query => index.find? query.index }

end TrustIr.GenericCoro.IndexedCFG
