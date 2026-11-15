-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIrRuntime
import TrustIr.Semantics.AggregateAccess

open TrustIr
open TrustIr.AggregateMemory

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {α : Type} (result : Except SemError α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected semantic error: {repr error}")

private def intIs (width : Nat) (raw : Int) : Option Value → Bool
  | some (.int actual value) => actual == width && value == raw
  | _ => false

private def finiteTraversal : IO Unit := do
  let templates : List (List (Option UInt8)) := [[], [none], [some 3], [some 1, none, some 2], [some 4, some 5, some 6, some 7]]
  for template in templates do
    for repetitions in List.range 7 do
      let image := (ByteImage.ofList template).tile repetitions
      let dense := (List.replicate repetitions template).join
      for offset in List.range (dense.length + 2) do
        for count in [0, 1, 2, 5, dense.length, dense.length + 1] do
          let part := image.slice offset count
          let oracle := dense.drop offset |>.take count
          require "missing-byte search matches complete dense oracle"
            (part.firstWhere Option.isNone == (List.range oracle.length).find? (fun i => ((oracle.get? i).getD none).isNone))
          require "present-byte search matches complete dense oracle"
            (part.firstWhere Option.isSome == (List.range oracle.length).find? (fun i => ((oracle.get? i).getD none).isSome))
          for width in [0, 1, 2, 3, 4] do
            for lanes in [0, 1, 2, 3, 5] do
              let mapped ← expect (part.mapBlocks (fun bytes => .ok bytes.toList) width lanes)
              let checked ← expect (part.checkBlocks (fun bytes => .ok (firstMissing bytes)) width lanes)
              let expected := (List.range lanes).foldl (fun first i =>
                match first with
                | some index => some index
                | none => ((List.range (oracle.drop (i * width) |>.take width).length).find?
                    (fun j => ((((oracle.drop (i * width) |>.take width).get? j).getD none).isNone))).map (i * width + ·)) none
              require "every finite coverage summary matches dense slices" (checked == expected)
              for i in List.range lanes do
                require "every finite mapped block matches its independent slice"
                  (mapped.get? i == some (oracle.drop (i * width) |>.take width))
  let source := ByteImage.source 19 (fun i => if i == 17 then none else some 8)
  require "external sources are inspected, not inferred periodic" (source.firstWhere Option.isNone == some 17)
  let hugeSource := ByteImage.source (2 ^ 40) (fun i => if i == 0 then none else some 8)
  require "external-source search stops at the first actual witness" (hugeSource.firstWhere Option.isNone == some 0)
  let joined := (ByteImage.fill 5 (some 3)).append source
  require "append search preserves absolute offsets" (joined.firstWhere Option.isNone == some 22)

private def hugeTyped (model : ByteModel) (count : Nat) : IO Unit := do
  let words : Ty := .Array ⟨0⟩ count
  let bytesTy : Ty := .Array ⟨1⟩ (4 * count)
  let service := prepare { model, hasTargetInfo := true, types := [some .U32, some .U8] } [words, bytesTy]
  let plan ← expect (service.query words)
  let bytesPlan ← expect (service.query bytesTy)
  let value := Value.array (CompactArray.Packed.uniform count (.int 32 67305985))
  let encoded ← expect (encode model none plan value)
  require "huge typed encoder retains exact logical extent" (encoded.bytes.size == 4 * count)
  require "fully initialized encoded word array has no absent bytes" ((firstMissing encoded.bytes).isNone)
  let (address, memory) := Memory.empty.alloc (4 * count) 4 0 .rustStack
  let state := { MachineState.empty with memory, permissions := MachineState.empty.permissions.set ⟨0⟩ .owned }
  let (_, stored) ← expect ((storeValue service none words (.ptr address (some ⟨0⟩)) value true none model).run state)
  let (loaded, _) ← expect ((loadValue service none words (.ptr address (some ⟨0⟩)) true none model).run stored)
  match loaded with
  | .array values =>
    require "whole typed load preserves declared word count" (values.size == count)
    for i in [0, 1, count / 2, count - 1] do
      require "whole typed load preserves actual word image" (intIs 32 67305985 (values.get? i))
  | _ => throw (IO.userError "whole typed load must return an array")
  let (cross, _) ← expect ((loadValue service none bytesTy (.ptr address (some ⟨0⟩)) true none model).run stored)
  match cross with
  | .array values =>
    require "cross-width load preserves whole logical extent" (values.size == 4 * count)
    for i in [0, 1, 2, 3, 4, 4 * count / 2, 4 * count - 3, 4 * count - 2, 4 * count - 1] do
      require "cross-width periodic reinterpretation preserves byte phase" (intIs 8 (Int.ofNat (i % 4 + 1)) (values.get? i))
  | _ => throw (IO.userError "cross-width whole load must return an array")
  let erased := stored.memory.writeImage (address + 4 * count - 1) (ByteImage.fill 1 none)
  let snapshot := erased.readImage address (4 * count)
  require "late missing byte is covered at its exact whole-array offset"
    ((← expect (covered bytesPlan snapshot)) == some (4 * count - 1))
  let zeroed := ({ bytes := snapshot } : Image).zeroUninit
  require "global zeroing visits actual absent bytes structurally" ((firstMissing zeroed).isNone && zeroed.get (4 * count - 1) == some 0)
  IO.println s!"COMPACT_TYPED_IMAGES_PASS model={repr model} words={count}"

private def decodingContext : IO Unit := do
  let count := 2 ^ 40 + 37
  for model in [ByteModel.le32, .le64] do
    let width := model.pointerBytes
    let plan : Plan := .array (.Array ⟨0⟩ count) ⟨width * count, width⟩ count (.leaf .Ptr ⟨width, width⟩)
    let (address, memory) := Memory.empty.alloc 8 8 0 .rustStack
    let image := (ByteImage.ofList ((encodeIntBytes (Int.ofNat address) width).map some)).tile count
    let withAllocation ← expect (decode model none memory plan image)
    let withoutAllocation ← expect (decode model none Memory.empty plan image)
    match withAllocation, withoutAllocation with
    | .array actual, .array other =>
      match actual.get? (count - 1), other.get? (count - 1) with
      | some (.ptr a (some id)), some (.ptr b none) =>
        require "decoding recovers actual memory provenance" (a == address && b == address && id == ⟨0⟩)
      | _, _ => throw (IO.userError "pointer provenance must come from each actual decoding memory")
    | _, _ => throw (IO.userError "pointer arrays must decode")
    let functions : Plan := .array (.Array ⟨0⟩ count) ⟨width * count, width⟩ count (.leaf (.Func ⟨3⟩) ⟨width, width⟩)
    let word := (ByteImage.ofList ((encodeIntBytes 1 width).map some)).tile count
    let first ← expect (decode model (some [⟨7⟩]) Memory.empty functions word)
    let second ← expect (decode model (some [⟨11⟩]) Memory.empty functions word)
    match first, second with
    | .array a, .array b =>
      match a.get? (count - 1), b.get? (count - 1) with
      | some (.fnDef sa fa), some (.fnDef sb fb) =>
        require "function words use each actual namespace" (sa == ⟨3⟩ && sb == ⟨3⟩ && fa == ⟨7⟩ && fb == ⟨11⟩)
      | _, _ => throw (IO.userError "function identity must come from decoding namespace")
    | _, _ => throw (IO.userError "function arrays must decode")

private def unwrittenRecords : IO Unit := do
  let count := 2 ^ 40 + 37
  let arrayTy : Ty := .Array ⟨0⟩ count
  let root : Ty := .Struct ⟨0⟩
  let definition : StructDef := { id := ⟨0⟩, name := "HugeLane", fields := [{ name := "array", ty := arrayTy, offset := some 0 }], size := some count, align := some 1 }
  let service := prepare { hasTargetInfo := true, types := [some .U8], structs := [definition] } [root]
  let (address, memory) := Memory.empty.alloc count 1 0 .rustStack
  let state := { MachineState.empty with memory, permissions := MachineState.empty.permissions.set ⟨0⟩ .owned }
  let pointer := Value.ptr address (some ⟨0⟩)
  let (_, stored) ← expect ((storeValue service none root pointer (.aggregate [.uninit])).run state)
  let (loaded, _) ← expect ((loadValue service none root pointer).run stored)
  match loaded with
  | .aggregate [.uninit] => pure ()
  | _ => throw (IO.userError "actual whole unwritten lane must recover Uninit")
  let transported := { state with memory := state.memory.writeImage address (stored.memory.readImage address count) }
  match (loadValue service none root pointer).run transported with
  | .error (.ub _) => pure ()
  | _ => throw (IO.userError "copying absent bytes must not transport unwritten records")
  let clipped := { stored with memory := stored.memory.writeImage (address + count - 1) (ByteImage.fill 1 (some 9)) }
  match (loadValue service none root pointer).run clipped with
  | .error (.ub _) => pure ()
  | _ => throw (IO.userError "partially written array lane cannot recover Uninit")

private def errorOrder : IO Unit := do
  let element : Plan := .enumeration (.Enum ⟨0⟩) ⟨1, 1⟩
    { tag := .u8, discriminants := [0], encoding := .direct 0,
      variants := [[]], uninhabited := [false] } [some []]
  let count := 2 ^ 40 + 37
  let plan : Plan := .array (.Array ⟨0⟩ count) ⟨count, 1⟩ count element
  let image := Memory.empty.writeImage 0 (ByteImage.fill count (some 0))
    |>.writeImage 0 (ByteImage.fill 1 none)
    |>.writeImage (count - 1) (ByteImage.fill 1 (some 2))
  match covered plan (image.readImage 0 count) with
  | .error (.typeError "Load: enum tag does not name a variant") => pure ()
  | _ => throw (IO.userError "later invalid enum must retain precedence over earlier missing bytes")
  let emptyPlan : Plan := .array (.Array ⟨0⟩ 0) ⟨0, 1⟩ 0 element
  let encoded ← expect (encode .le64 none emptyPlan (.array (CompactArray.Packed.uniform 0 .uninit)))
  require "empty array never inspects unused payload" (encoded.bytes.size == 0)
  let zst : Plan := .array (.Array ⟨0⟩ count) ⟨0, 1⟩ count (.leaf .Unit ⟨0, 1⟩)
  match ← expect (decode .le64 none Memory.empty zst ByteImage.empty) with
  | .array values => require "ZST array retains huge count" (values.size == count)
  | _ => throw (IO.userError "ZST array must decode")

def main : IO Unit := do
  finiteTraversal
  hugeTyped .le32 (2 ^ 24 + 3)
  hugeTyped .le64 (2 ^ 40 + 37)
  decodingContext
  unwrittenRecords
  errorOrder
  IO.println "Compact typed-image checks passed"
