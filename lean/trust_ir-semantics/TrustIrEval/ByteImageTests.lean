-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIrRuntime
import TrustIr.Semantics.Memory

open TrustIr

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def modelWrite (old : Nat → Option UInt8) (start : Nat) (data : List (Option UInt8)) :
    Nat → Option UInt8 := fun address =>
  if start ≤ address && address < start + data.length then (data.get? (address - start)).getD none
  else old address

private def checkImage (image : ByteImage) (expected : List (Option UInt8)) : IO Unit := do
  require "image extent must match the complete finite oracle" (image.size == expected.length)
  require "all finite image bytes must match" (image.toList == expected)
  require "one-past image access is absent" ((image.get image.size).isNone)

private def finiteImages : IO Unit := do
  let unit : List (Option UInt8) := [some 3, none, some 5, some 8]
  let literal := ByteImage.ofList unit
  for count in List.range 9 do
    let repeated := literal.tile count
    let expected := (List.replicate count unit).join
    checkImage repeated expected
    for offset in List.range (expected.length + 2) do
      for size in [0, 1, 3, expected.length, expected.length + 1] do
        let image := repeated.slice offset size
        let oracle := expected.drop offset |>.take size
        checkImage image oracle
        checkImage (image.map (fun byte => some (byte.getD 0))) (oracle.map (fun byte => some (byte.getD 0)))
        checkImage (image.map (fun _ => none)) (oracle.map (fun _ => none))
  checkImage (literal.append (ByteImage.fill 3 none)) (unit ++ [none, none, none])
  checkImage (ByteImage.empty.tile (2^64-1)) []
  checkImage (ByteImage.source 16 (fun index => if index % 3 == 0 then none else some index.toUInt8))
    ((List.range 16).map (fun index => if index % 3 == 0 then none else some index.toUInt8))

private def croppedWindows : IO Unit := do
  let bytes : List (Option UInt8) := [none, some 2, some 3, none, some 5, some 6, some 7]
  let base := ByteImage.ofList bytes
  for start in List.range 9 do
    for count in List.range 10 do
      let first := base.slice start count
      let word := bytes.drop start |>.take count
      for offset in List.range 9 do
        for size in [0, 1, 4, 10] do
          let cropped := first.slice offset size
          checkImage cropped (word.drop offset |>.take size)
          require "adjacent crops must retain at most one view"
            (cropped.tree.storageHeight ≤ 2)
  let huge := (ByteImage.ofList [some 1, none, some 3]).tile (2^64-1)
  let mut image := huge
  for step in List.range 1024 do
    image := image.slice 1 (image.size - 2)
    require "crop history must not grow retained depth" (image.tree.storageHeight ≤ 3)
    require "composed crop extent must remain exact" (image.size == huge.size - 2*(step+1))
    require "composed crop phase and final byte must remain exact"
      (image.get 0 == huge.get (step+1) &&
       image.get (image.size-1) == huge.get (huge.size-step-2) &&
       (image.get image.size).isNone)
  IO.println "COMPOSED_VIEW_NORMALIZATION_PASS crop_steps=1024"

private def periodicWindows : IO Unit := do
  let bytes : List (Option UInt8) := [some 1, none, some 3, some 7]
  let base := ByteImage.ofList bytes
  for size in List.range 14 do
    for phase in List.range 10 do
      let window : ByteImage := ⟨size, .periodic base.tree (by decide) phase size⟩
      let word := (List.range size).map (fun i => (bytes.get? ((phase + i) % 4)).getD none)
      for copies in List.range 7 do
        let repeated := window.tile copies
        require "finite periodic template must retain its own restart boundary"
          (repeated.toList == (List.replicate copies word).join)
        require "periodic template extent and absence remain exact"
          (repeated.size == size * copies && (repeated.get repeated.size).isNone)
      if nonempty : 0 < size then
        for start in List.range 9 do
          let cycled : ByteImage := ⟨19, window.tree.repeatWindow nonempty start 19⟩
          let expected := (List.range 19).map (fun i => (word.get? ((start + i) % size)).getD none)
          require "composed periodic phases must preserve finite-window restart"
            (cycled.toList == expected)
  -- This arbitrary source carries no shorter-period certificate. Its finite
  -- five-byte boundary must survive, regardless of values outside that word.
  let externalUnit := ByteImage.source 5 (fun index => some index.toUInt8)
  checkImage (externalUnit.tile 3)
    [some 0, some 1, some 2, some 3, some 4,
     some 0, some 1, some 2, some 3, some 4,
     some 0, some 1, some 2, some 3, some 4]
  let mut image := base
  for _ in List.range 1024 do
    image := image.tile 2
    require "aligned retile must not grow retained depth" (image.tree.storageHeight ≤ 2)
    require "retile retains defined and absent bytes"
      (image.get 0 == some 1 && (image.get 1).isNone && image.get (image.size - 1) == some 7)
  IO.println "ALIGNED_PERIODIC_NORMALIZATION_PASS retile_steps=1024"

private def finiteStores : IO Unit := do
  let initial := fun address => if address % 5 == 0 then none else some (address % 17).toUInt8
  let mut memory := { Memory.empty with storage := ByteStore.source initial }
  let mut oracle := initial
  for (start, data) in [(4, [some 1, none, some 3, some 4]),
      (6, [none, some 7, some 8]), (0, [some 9]), (18, [none, none]), (8, [])] do
    memory := memory.writeBytesMaybeUninit start data
    oracle := modelWrite oracle start data
    for address in List.range 24 do
      require "authoritative store must match independent point lookup" (memory.bytes address == oracle address)
    for start in List.range 24 do
      for count in [0, 1, 3, 8, 24] do
        let image := memory.readImage start count
        let expected := (List.range count).map (fun index => oracle (start + index))
        checkImage image expected
  for src in List.range 12 do
    for dst in List.range 12 do
      for count in [0, 1, 2, 5, 12] do
        let copied := memory.writeImage dst (memory.readImage src count)
        let expected := modelWrite oracle dst ((List.range count).map (fun index => oracle (src + index)))
        for address in List.range 28 do
          require "overlap copy must use source before destination write"
            (copied.bytes address == expected address)

private def hugeImages : IO Unit := do
  let repetitions := 2^40 + 37
  let unit := ByteImage.ofList [some 3, some 7, none, some 11]
  let image := unit.tile repetitions
  let count := image.size
  let src := 1024
  let dst := src + count + 4096
  let stored := Memory.empty.writeImage src image
  let copied := stored.writeImage dst (stored.readImage src count)
  for index in [0, 1, 2, 3, count / 2, count - 4, count - 3, count - 2, count - 1] do
    let expected := unit.get (index % 4)
    require "huge periodic source byte must remain exact" (stored.bytes (src + index) == expected)
    require "huge copied byte and init state must remain exact" (copied.bytes (dst + index) == expected)
  require "source must survive copy" (copied.bytes src == some 3)
  require "outside destination must remain absent" ((copied.bytes (dst + count)).isNone)
  let moved := stored.writeImage (src + 1) (stored.readImage src (count - 1))
  for index in [0, 1, 2, 3, count / 2, count - 2] do
    require "huge overlapping move must retain its snapshot"
      (moved.bytes (src + 1 + index) == unit.get (index % 4))
  let filled := copied.writeImage dst (ByteImage.fill count (some 0xA5))
  for index in [0, count / 2, count - 1] do
    require "huge fill must initialize every queried boundary" (filled.bytes (dst + index) == some 0xA5)
  let holed := filled.writeImage (dst + count - 1) (ByteImage.fill 1 none)
  require "absent write must erase a previously initialized byte" ((holed.bytes (dst + count - 1)).isNone)
  require "absent write must leave its neighbor" (holed.bytes (dst + count - 2) == some 0xA5)
  let allocation : AllocId := ⟨0⟩
  let lanes := (Memory.empty.writeImage src (ByteImage.fill count none)).recordUnwritten allocation src [(0, count)]
  let transported := lanes.writeImage dst (lanes.readImage src count)
  require "source unwritten record must remain" (transported.isUnwritten allocation src)
  require "byte copy must not fabricate unwritten lane ownership" (!(transported.isUnwritten allocation dst))
  let (base, allocated) := Memory.empty.alloc count 8 13 .rustHeap
  require "large allocation must not initialize its requested region" ((allocated.bytes base).isNone)
  require "slack fill must retain defined bytes" (allocated.bytes (base + count + 12) == some slackFill)
  let nested := (unit.tile (2^20 + 37)).tile (2^20 + 17)
  require "huge nested producer retains one periodic layer" (nested.tree.storageHeight == 2)
  let nestedDst := src + nested.size + 8192
  let nestedStored := Memory.empty.writeImage src nested
  let nestedCopied := nestedStored.writeImage nestedDst (nestedStored.readImage src nested.size)
  for index in [0, 1, 2, 3, nested.size / 2, nested.size - 2, nested.size - 1] do
    require "actual nested snapshot store and copy keep bytes and initialization"
      (nestedCopied.bytes (nestedDst + index) == unit.get (index % 4))
  require "nested snapshot copy retains its end boundary"
    ((nestedCopied.bytes (nestedDst + nested.size)).isNone)
  IO.println s!"COMPACT_BYTE_IMAGES_PASS logical_bytes={count}"

def main : IO Unit := do
  croppedWindows
  finiteImages
  periodicWindows
  finiteStores
  hugeImages
  IO.println "Compact byte-image and snapshot checks passed"
