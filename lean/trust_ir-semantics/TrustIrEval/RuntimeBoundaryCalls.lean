-- Copyright 2026 Andrew Yates | Apache-2.0
-- These callers compile without importing the runtime provider library.
import TrustIr.Semantics.AggregateImages

namespace TrustIrEval.RuntimeBoundaryCalls
open TrustIr

@[noinline] def leafStored {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (leaf : CompactArray.Leaf α size) := leaf.checkStored check
@[noinline] def treeStored {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : CompactArray.Tree α size) := tree.checkStored check
@[noinline] def leafRange {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (leaf : CompactArray.Leaf α size) (offset count : Nat) := leaf.checkRange check offset count
@[noinline] def treeRange {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : CompactArray.Tree α size) (offset count : Nat) := tree.checkRange check offset count
@[noinline] def treeEqual {α β ε : Type} (eq : α → β → Except ε Bool) {size : Nat}
    (left : CompactArray.Tree α size) (right : CompactArray.Tree β size) := left.eqByM eq right
@[noinline] def valueDepth (value : Value) := value.depth
@[noinline] def listDepth (values : List Value) := valueListDepth values
@[noinline] def fieldDepth (fields : List (String × Value)) := valueFieldDepth fields
@[noinline] def treeDepth {size : Nat} (tree : CompactArray.Tree Value size) := arrayTreeDepth tree
@[noinline] def leafDepth {size : Nat} (leaf : CompactArray.Leaf Value size) := arrayLeafDepth leaf
@[noinline] def byteMap (f : Option UInt8 → Option UInt8) (image : ByteImage) := image.map f
@[noinline] def firstWhere (test : Option UInt8 → Bool) (image : ByteImage) := image.firstWhere test
@[noinline] def mapBlocks {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) := image.mapBlocks decode width count
@[noinline] def checkBlocks {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) := image.checkBlocks check width count
-- The array encoding interface is private; the actual public encoder must call it.
@[noinline] def arrayEncode (plan : AggregateMemory.Plan) (value : Value) :=
  AggregateMemory.encode .le64 none plan value

@[noinline, nospecialize] def keepRange (range : Nat → Nat → Except Nat Unit) := range
@[noinline] def heldTreeRange (check : Nat → Except Nat Unit) {size : Nat}
    (tree : CompactArray.Tree Nat size) := keepRange (tree.checkRange check)

end TrustIrEval.RuntimeBoundaryCalls
