-- Copyright 2026 Andrew Yates | Apache-2.0
-- Runtime implementation and representation; correspondence is UNPROVED.
import TrustIr.State.ByteImage

namespace TrustIr.ByteImage.ImageMapRuntime

private abbrev Cache := MapCache

mutual
  private unsafe def visit (f : Option UInt8 → Option UInt8) {size : Nat} (tree : Tree size) :
      StateM Cache (Tree size) :=
    Tree.mapCacheStep (size, ptrAddrUnsafe tree) (fun _ => uncached f tree) tree
  private unsafe def uncached (f : Option UInt8 → Option UInt8) {size : Nat}
      (tree : Tree size) : StateM Cache (Tree size) :=
    Tree.mapStep f (fun {_} child => visit f child) tree

end

/-- The function and retained input arena are local to one map operation.
    External source functions stay external; no period is inferred from them. -/
@[export l_TrustIr_ByteImage_map]
unsafe def map (f : Option UInt8 → Option UInt8) (image : ByteImage) : ByteImage :=
  ⟨image.size, ((visit f image.tree).run ∅).1⟩

end TrustIr.ByteImage.ImageMapRuntime
