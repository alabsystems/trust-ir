-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.Semantics.AggregateAccess
import TrustIrEval.Observation

open TrustIr TrustIr.AggregateMemory

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)
private def mark (label : String) : IO Unit := do
  let handle ← IO.getStderr
  handle.putStrLn label
  handle.flush

private def expect {α : Type} (result : Except SemError α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected semantic error: {repr error}")

private def outerViews {size : Nat} : ByteImage.Tree size → Nat
  | .view source _ _ _ => outerViews source + 1
  | _ => 0

private def callbackShape (image : ByteImage) : Except SemError (Nat × Nat) :=
  .ok (image.size, outerViews image.tree)

private def callbackPeriod (image : ByteImage) : Except SemError (Nat × Nat × Nat) :=
  match image.tree with
  | .periodic (period := period) _ _ phase count => .ok (period, phase, count)
  | _ => .ok (0, 0, image.size)

private def expectTypeError {α : Type} (label message : String)
    (result : Except SemError α) : IO Unit :=
  match result with
  | .error (.typeError actual) => require label (actual == message)
  | _ => throw (IO.userError label)

/-- These callbacks deliberately observe the retained constructors. The pure
    specification is executed directly, separately from both the implemented
    public wrapper and the explicit operation-local runtime. -/
private unsafe def canonicalCallbacks : IO Unit := do
  let literal := ByteImage.ofList [some 1, some 2]
  let nested := (literal.slice 0 2).slice 0 2
  let rawNested : ByteImage := ⟨2, .view (.view literal.tree 0 2 (by decide)) 0 2 (by decide)⟩
  let shared := literal.append literal
  let clipped : ByteImage := ⟨3, .periodic literal.tree (by decide) 1 3⟩
  let images := [literal, nested, rawNested, shared, (shared.slice 0 4).slice 0 4,
    ByteImage.source 2 (fun i => some (UInt8.ofNat (i + 1))),
    literal.tile 3, (literal.tile 3).tile 5, clipped.tile 5]
  for image in images do
    for count in [0, 1, image.size] do
      let spec ← expect (ByteImage.mapBlocksSpec callbackShape image 1 count)
      let runtime ← expect (ByteImage.WindowRuntime.mapBlocks callbackShape image 1 count)
      let publicResult ← expect (image.mapBlocks callbackShape 1 count)
      let observed := (List.range count).map spec.get?
      require "constructor-aware map matches pure spec"
        (observed == (List.range count).map runtime.get? &&
         observed == (List.range count).map publicResult.get?)
      let specPeriod ← expect (ByteImage.mapBlocksSpec callbackPeriod image 1 count)
      let runtimePeriod ← expect (ByteImage.WindowRuntime.mapBlocks callbackPeriod image 1 count)
      let publicPeriod ← expect (image.mapBlocks callbackPeriod 1 count)
      let expectedPeriods := (List.range count).map specPeriod.get?
      require "period metadata callbacks match the actual canonical producer"
        (expectedPeriods == (List.range count).map runtimePeriod.get? &&
         expectedPeriods == (List.range count).map publicPeriod.get?)
  let witness ← expect (ByteImage.mapBlocksSpec callbackShape literal 1 1)
  require "literal callback receives one composed canonical view"
    (witness.get? 0 == some (1, 1))
  let rejectShape := fun (image : ByteImage) =>
    if outerViews image.tree == 1 then
      Except.error (SemError.typeError "constructor-aware decode rejection")
    else Except.ok (0 : Nat)
  for result in [ByteImage.mapBlocksSpec rejectShape literal 1 1,
      ByteImage.WindowRuntime.mapBlocks rejectShape literal 1 1,
      literal.mapBlocks rejectShape 1 1] do
    expectTypeError "constructor-aware map preserves callback error"
      "constructor-aware decode rejection" result
  let check := fun (image : ByteImage) =>
    if outerViews image.tree != 1 then
      Except.error (SemError.typeError "unexpected callback representation")
    else if image.get 0 == some 255 then
      Except.error (SemError.typeError "late constructor-aware error")
    else Except.ok (if (image.get 0).isNone then some 0 else none)
  let holed := ByteImage.ofList [some 1, none]
  for image in [holed, (holed.slice 0 2).slice 0 2, holed.append holed] do
    for result in [ByteImage.checkBlocksSpec check image 1 image.size,
        ByteImage.WindowRuntime.checkBlocks check image 1 image.size,
        image.checkBlocks check 1 image.size] do
      require "constructor-aware coverage retains the first hole"
        ((← expect result) == some 1)
  let laterError := ByteImage.ofList [none, some 255]
  for result in [ByteImage.checkBlocksSpec check laterError 1 2,
      ByteImage.WindowRuntime.checkBlocks check laterError 1 2,
      laterError.checkBlocks check 1 2] do
    expectTypeError "later semantic error precedes earlier coverage hole"
      "late constructor-aware error" result
  for result in [ByteImage.checkBlocksSpec check literal 1 1,
      ByteImage.WindowRuntime.checkBlocks check literal 1 1,
      literal.checkBlocks check 1 1] do
    require "constructor-aware coverage succeeds" ((← expect result).isNone)
  let reject := fun (_ : ByteImage) => Except.error (SemError.typeError "empty callback")
  require "empty map never calls its callback"
    ((ByteImage.mapBlocksSpec (α := Nat) reject literal 1 0).isOk &&
     (ByteImage.WindowRuntime.mapBlocks (α := Nat) reject literal 1 0).isOk)
  let rejectCoverage := fun (_ : ByteImage) =>
    (Except.error (SemError.typeError "empty callback") : Except SemError (Option Nat))
  require "empty coverage never calls its callback"
    ((ByteImage.checkBlocksSpec rejectCoverage literal 1 0).isOk &&
     (ByteImage.WindowRuntime.checkBlocks rejectCoverage literal 1 0).isOk)
  IO.println "SHARED_CANONICAL_CALLBACKS_PASS"

private def sharedTree : (depth : Nat) → CompactArray.Tree Value (2 ^ depth)
  | 0 => .uniform 1 (.int 8 1)
  | depth + 1 =>
    have positive : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    have lower : 2 ^ (depth + 1) / 2 = 2 ^ depth := by rw [Nat.pow_succ]; omega
    have upper : 2 ^ (depth + 1) - 2 ^ (depth + 1) / 2 = 2 ^ depth := by rw [Nat.pow_succ]; omega
    let child := sharedTree depth
    .split (by rw [Nat.pow_succ]; omega) (lower.symm ▸ child) (upper.symm ▸ child)
private def sharedValue : Nat → Value
  | 0 => .int 8 1
  | depth + 1 => let child := sharedValue depth; .aggregate [child, child]

private def intEq (a b : Value) : Except SemError Bool :=
  match a, b with
  | .int wa a, .int wb b => .ok (wa == wb && a == b)
  | _, _ => .error (.typeError "expected integer")
private def checkInt (value : Value) : Except SemError Unit :=
  match value with
  | .int 8 1 => .ok ()
  | _ => .error (.typeError "stored payload rejected")

private def rangeError : Except Nat Unit → Option Nat
  | .ok () => none
  | .error value => some value

private unsafe def visibleStoredChecks : IO Unit := do
  let check := fun value : Nat => if value == 0 then Except.ok () else Except.error value
  for size in List.range 41 do
    let word := (List.range size).map (fun i => if i % 5 == 2 then i + 1 else 0)
    let tree := CompactArray.Tree.ofArray word.toArray
    for offset in List.range (size + 3) do
      for count in [0, 1, 2, 7, size, size + 5] do
        let expected := (word.drop offset |>.take count).find? (· != 0)
        for result in [tree.checkRangeSpec check offset count,
            CompactArray.StoredCheckRuntime.range check tree offset count,
            tree.checkRange check offset count] do
          require "visible stored validation matches independent first-error oracle"
            (rangeError result == expected)
  let hidden := CompactArray.Tree.ofArray
    #[Value.uninit, .float (0.0 / 0.0), .int 8 1, .int 8 1, .undef .U8]
  for result in [hidden.checkRangeSpec checkInt 2 2,
      CompactArray.StoredCheckRuntime.range checkInt hidden 2 2,
      hidden.checkRange checkInt 2 2] do
    require "hidden invalid retained values must not be inspected" result.isOk
  require "a visible invalid retained value must still fail" (!(hidden.checkRange checkInt 1 1).isOk)
  let child := CompactArray.Tree.ofArray #[7, 0]
  let repeated : CompactArray.Tree Nat 4 := .split (by decide) child child
  require "shared nodes at different visible offsets must not reuse success"
    (rangeError (repeated.checkRange check 1 2) == some 7)
  let huge := sharedTree 63
  let (checked, stats) := CompactArray.StoredCheckRuntime.rangeWithStats checkInt huge 1 (2^63-2)
  require "huge clipped stored range covers its visible values" checked.isOk
  require "huge clipped stored range reuses physical windows"
    (stats.visits < 400 && stats.hits > 40 && stats.payloads == 1)
  let (_, emptyStats) := CompactArray.StoredCheckRuntime.rangeWithStats checkInt hidden 0 0
  require "empty range never inspects retained payload" (emptyStats.payloads == 0)
  IO.println "VISIBLE_STORED_RANGE_PASS logical_values=9223372036854775806"

@[noinline] private unsafe def depthAndChecks (treeDepth valueDepth : Nat) : IO Unit := do
  let scalars : List Value := [.int 8 1, .float 1.25, .bool true, .nullPtr,
    .ptr 32 (some ⟨7⟩), .fnDef ⟨2⟩ ⟨3⟩, .partial [none, some 3], .undef .U8, .uninit]
  let containers := scalars ++ [.aggregate scalars, .vector scalars, .frame 0 scalars,
    .set scalars, .sequence scalars, .record [("a", .aggregate scalars)],
    .closure ⟨0⟩ scalars, .typedClosure ⟨0⟩ ⟨1⟩ scalars, .fatPtr 32 none (.aggregate scalars),
    .array (CompactArray.Packed.ofArray scalars.toArray)]
  for value in containers do require "every value constructor matches pure depth" (value.depth == value.depthSpec)
  for n in List.range 8 do
    let value := sharedValue n
    require "finite shared depth matches reference" (value.depth == value.depthSpec)
    let tree := sharedTree n
    require "finite stored check preserves reference membership" ((tree.checkStored checkInt).isOk)
    require "finite equality matches ordered pure reference"
      ((← expect (tree.eqByM intEq tree)) == (← expect (tree.eqByMSpec intEq tree)))
  mark "finite depth/check/equality passed"
  let value := sharedValue valueDepth
  let (depth, stats) := ValueDepthRuntime.depthWithStats value
  require "shared nested values retain actual nesting" (depth == valueDepth + 1 && value.depth == valueDepth + 1)
  require "depth visits physical values and lists" (stats.visits < 500 && stats.hits ≥ valueDepth - 1)
  mark "shared aggregate depth passed"
  let tree := sharedTree treeDepth
  let array := Value.array ⟨2 ^ treeDepth, tree⟩
  require "storage edges add no logical nesting" (array.depth == 2)
  mark "shared tree depth passed"
  let (checked, stats) := CompactArray.StoredCheckRuntime.treeWithStats checkInt tree
  require "shared stored check covers the actual payload" checked.isOk
  require "stored check visits no logical repetitions" (stats.visits < 150 && stats.hits ≥ treeDepth - 1 && stats.payloads == 1)
  mark "shared stored check passed"
  let (same, stats) := CompactArray.EqualityRuntime.treeWithStats intEq tree tree
  require "shared equality still compares actual values" (same.toOption == some true)
  mark s!"equality stats {repr stats}"
  require "equality visits physical pairs" (stats.visits < 150 && stats.hits ≥ treeDepth - 1)
  mark "shared equality passed"
  let flat := CompactArray.Tree.uniform (2 ^ treeDepth) (Value.int 8 1)
  let (same, stats) := CompactArray.EqualityRuntime.treeWithStats intEq flat tree
  require "uniform and split shapes compare every logical element" (same.toOption == some true)
  require "virtual uniforms retain memo identity" (stats.visits < 150 && stats.hits ≥ treeDepth - 1)
  require "aliasing never substitutes for comparator false"
    ((← expect (tree.eqByM (fun _ _ => .ok false) tree)) == false)
  match tree.eqByM (fun _ _ => Except.error (SemError.ub "inspect aliased input")) tree with
  | .error (.ub "inspect aliased input") => pure ()
  | _ => throw (IO.userError "aliasing must preserve callback errors")
  let empty := CompactArray.Tree.uniform 0 value
  require "empty uniform does not inspect retained payload" ((empty.checkStored (fun _ => Except.error (SemError.ub "unused"))).isOk)
  require "empty uniform depth ignores retained payload" ((Value.array ⟨0, empty⟩).depth == 1)
  IO.println s!"SHARED_VALUE_DEPTH_PASS depth={depth}"

private def doubledImage : Nat → ByteImage
  | 0 => ByteImage.ofList [some 1, none, some 3]
  | n + 1 => let child := doubledImage n; child.append child

@[noinline] private unsafe def byteWindows (imageDepth : Nat) : IO Unit := do
  for n in List.range 7 do
    let image := doubledImage n
    require "finite mapped bytes match complete dense reference"
      ((image.map (fun byte => some (byte.getD 0))).toList == image.toList.map (fun byte => some (byte.getD 0)))
    for offset in List.range (image.size + 2) do
      for count in [0, 1, 2, 5, image.size, image.size + 1] do
        let part := image.slice offset count
        require "finite source-window search matches pure constructor search"
          (part.firstWhere Option.isNone == part.tree.firstWhere Option.isNone 0 part.size)
  let image := doubledImage imageDepth
  let mapped := image.map (fun byte => some (byte.getD 0))
  let (missing, stats) := ByteImage.WindowRuntime.firstWhereWithStats Option.isNone mapped
  require "complete huge mapped DAG is initialized" missing.isNone
  require "byte search visits retained source windows" (stats.visits < 200 && stats.hits ≥ imageDepth - 1)
  for i in [0, 1, 2, mapped.size / 2, mapped.size - 2, mapped.size - 1] do
    require "mapped byte phase is exact" (mapped.get i == some (if i % 3 == 1 then 0 else UInt8.ofNat (i % 3 + 1)))

private def byteAt (value : Value) (index expected : Nat) : Bool :=
  match value with
  | .array values => match values.get? index with
    | some (.int 8 raw) => raw == Int.ofNat expected
    | _ => false
  | _ => false

@[noinline] private unsafe def periodicRoundtrip (count : Nat) : IO Unit := do
  let ty : Ty := .Array ⟨0⟩ count
  let service := prepare { hasTargetInfo := true, types := [some .U8] } [ty]
  let plan ← expect (service.query ty)
  let image := (ByteImage.ofList [some 1, some 2, some 3]).tile (count / 3)
  mark "periodic decode"
  let original ← expect (decode .le64 none Memory.empty plan image)
  require "period-three whole value has finite logical depth" (original.depth == 2)
  match original with
  | .array values =>
    let (result, stats) := ArrayEncodingRuntime.encodeTreeWithStats (fun value =>
      match value with
      | .int 8 raw => .ok (ByteImage.ofList [some (UInt8.ofNat raw.toNat)])
      | _ => .error (.typeError "expected U8")) values.tree
    require "encoder inspects physical array nodes" (result.isOk && stats.visits < 500 && stats.hits > 0)
  | _ => throw (IO.userError "expected periodic array")
  mark "periodic encode"
  let encoded ← expect (encode .le64 none plan original)
  require "shared re-encoding retains complete byte extent" (encoded.bytes.size == count)
  require "shared re-encoding inspects all initialization states" ((firstMissing encoded.bytes).isNone)
  mark "periodic reread"
  let reread ← expect (decode .le64 none Memory.empty plan encoded.bytes)
  require "shared re-read preserves typed equality" (← expect (equal .le64 plan original reread))
  mark "periodic equality passed"
  let last := count - 1
  let changed ← match reread with
    | .array values => match values.set? last (.int 8 99) with
      | some values => pure (Value.array values)
      | none => throw (IO.userError "last persistent update failed")
    | _ => throw (IO.userError "expected decoded array")
  require "late mismatch is observed after repeated equal regions" (!(← expect (equal .le64 plan original changed)))
  require "late update preserves original root" (byteAt original last 3 && byteAt changed last 99)
  mark "periodic late mismatch passed"
  let json := TrustIrEval.Observation.renderGraph [original, reread, changed]
  require "whole shared values reach actual observation" (json.compress.length > 0)
  mark "periodic observation passed"
  let (address, memory) := Memory.empty.alloc count 1 0 .rustStack
  let state := { MachineState.empty with memory, permissions := MachineState.empty.permissions.set ⟨0⟩ .owned }
  let (_, stored) ← expect ((storeValue service none ty (.ptr address (some ⟨0⟩)) original true).run state)
  let (loaded, _) ← expect ((loadValue service none ty (.ptr address (some ⟨0⟩)) true).run stored)
  require "actual typed store and load retain entire shared value" (← expect (equal .le64 plan original loaded))
  mark "periodic actual store/load passed"
  let holed := stored.memory.writeImage (address + last) (ByteImage.fill 1 none)
  require "late covered hole survives re-encoded source sharing"
    ((← expect (covered plan (holed.readImage address count))) == some last)
  let nan := Value.array (CompactArray.Packed.uniform count (.float (0.0 / 0.0)))
  let floatPlan : Plan := .array (.Array ⟨0⟩ count) ⟨4 * count, 4⟩ count (.leaf .F32 ⟨4, 4⟩)
  match equal .le64 floatPlan nan nan with
  | .error (.unsupported .float _) => pure ()
  | _ => throw (IO.userError "physical aliasing must not admit NaN equality")
  IO.println s!"SHARED_PERIODIC_CONSUMERS_PASS elements={count}"

/-- Exercise the public entrypoints whose erased ABI used to be supplied by
    `implemented_by`. The remaining map/search/equality/encoding entrypoints
    are exercised against independent observations in the existing groups. -/
private def runtimeEntryAbi : IO Unit := do
  let nested := Value.aggregate [.int 8 1]
  let values := [.int 8 1, nested]
  require "list-depth ABI" (valueListDepth values == valueListDepthSpec values)
  require "field-depth ABI"
    (valueFieldDepth [("a", .int 8 1), ("b", nested)] ==
      valueFieldDepthSpec [("a", .int 8 1), ("b", nested)])
  let leaf : CompactArray.Leaf Value 2 := .cons (.int 8 1) (.cons nested .nil)
  let tree : CompactArray.Tree Value 2 := .dense (by decide) leaf
  require "leaf-depth ABI" (arrayLeafDepth leaf == arrayLeafDepthSpec leaf)
  require "tree-depth ABI" (arrayTreeDepth tree == arrayTreeDepthSpec tree)
  let check := fun value : Value => match value with
    | .int _ _ => Except.ok ()
    | _ => Except.error (41 : Nat)
  require "leaf-check rejects the second payload" (rangeError (leaf.checkStored check) == some 41)
  require "leaf-range preserves offset and count"
    ((leaf.checkRange check 0 1).isOk && rangeError (leaf.checkRange check 1 1) == some 41)
  IO.println "RUNTIME_ENTRY_ABI_PASS"

unsafe def main (args : List String) : IO Unit := do
  runtimeEntryAbi
  let bounded := args.contains "--bounded"
  canonicalCallbacks
  visibleStoredChecks
  mark "starting depth and checks"
  depthAndChecks (if bounded then 12 else 63) (if bounded then 8 else 80)
  mark "starting byte windows"
  byteWindows (if bounded then 8 else 50)
  mark "starting periodic roundtrip"
  periodicRoundtrip (if bounded then 3 * (2 ^ 12 + 37) else 3 * (2 ^ 40 + 37))
  IO.println "Shared value-consumer checks passed"
