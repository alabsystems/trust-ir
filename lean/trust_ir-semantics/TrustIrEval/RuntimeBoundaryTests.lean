-- Copyright 2026 Andrew Yates | Apache-2.0
-- Native ABI observations only. None is a runtime correspondence proof.
import TrustIr.Semantics.Eval
import TrustIrRuntime
import TrustIrEval.RuntimeBoundaryCalls
import TrustIrEval.ImageMapStepBinding
import TrustIrEval.ImageMapCacheChecks

run_cmd TrustIrEval.ImageMapStepBinding.checkSourceBodies

open TrustIr TrustIrEval.RuntimeBoundaryCalls

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {α ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected callback error {repr error}")

unsafe def main (args : List String) : IO Unit := do
  TrustIrEval.ImageMapCacheChecks.checkMapCacheThunks
  unless args.isEmpty do
    require "Lake/native caller preserves literal program arguments"
      (args == ["--check-argv", "two words", "--literal", "", "--"])
    IO.println "RUNTIME_ARGV_PASS"
  let leaf : CompactArray.Leaf Nat 2 := .cons 1 (.cons 2 .nil)
  let tree : CompactArray.Tree Nat 2 := .dense (by decide) leaf
  let reject : Nat → Except Nat Unit := fun value => if value == 2 then .error 2 else .ok ()
  require "imported leaf check preserves callback failure" (match leafStored reject leaf with | .error 2 => true | _ => false)
  require "imported tree check preserves callback failure" (match treeStored reject tree with | .error 2 => true | _ => false)
  require "imported leaf range omits hidden failure" ((leafRange reject leaf 0 1).isOk)
  require "imported tree range preserves visible failure" (match treeRange reject tree 1 1 with | .error 2 => true | _ => false)
  require "imported equality does not treat aliases as true"
    (!(← expect (treeEqual (ε := Nat) (fun _ _ => .ok false) tree tree)))
  require "imported partial range retains callback failure"
    (match (heldTreeRange reject tree) 1 1 with | .error 2 => true | _ => false)
  let scalarLeaf : CompactArray.Leaf UInt8 2 := .cons 1 (.cons 2 .nil)
  require "generic scalar callback/value boxing"
    (match leafStored (fun value : UInt8 => if value == 2 then Except.error (2 : UInt8) else .ok ()) scalarLeaf with
     | .error 2 => true | _ => false)
  let value := Value.aggregate [.int 8 1]
  let values : CompactArray.Leaf Value 1 := .cons value .nil
  let valueTree : CompactArray.Tree Value 1 := .dense (by decide) values
  require "imported value depth" (valueDepth value == 2)
  require "imported list depth" (listDepth [value] == 2)
  require "imported field depth" (fieldDepth [("field", value)] == 2)
  require "imported tree depth" (treeDepth valueTree == 2)
  require "imported leaf depth" (leafDepth values == 2)
  let image := ByteImage.ofList [some 1, none]
  require "imported byte map" ((byteMap (fun byte => some (byte.getD 0)) image).toList == [some 1, some 0])
  require "imported byte search" (firstWhere Option.isNone image == some 1)
  let mapped ← expect (mapBlocks (ε := Nat) (fun bytes => .ok bytes.size) image 1 2)
  require "imported block map" (mapped.get? 0 == some 1 && mapped.get? 1 == some 1)
  let missing ← expect (checkBlocks (ε := Nat) (fun bytes =>
    .ok (if (bytes.get 0).isNone then some 0 else none)) image 1 2)
  require "imported block coverage" (missing == some 1)
  let plan : AggregateMemory.Plan := .array (.Array ⟨0⟩ 2) ⟨2, 1⟩ 2 (.leaf .U8 ⟨1, 1⟩)
  let encoded ← expect (arrayEncode plan (.array (CompactArray.Packed.uniform 2 (.int 8 7))))
  require "imported actual array encoder" (encoded.bytes.toList == [some 7, some 7])
  IO.println "RUNTIME_ABI_IMPORTED_CALLERS_PASS interfaces=15"
