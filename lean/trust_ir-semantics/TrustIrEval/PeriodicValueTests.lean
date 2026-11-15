import TrustIrRuntime
import TrustIr.Semantics.AggregateAccess
import TrustIrEval.Observation

open TrustIr.CompactArray
open TrustIr TrustIr.AggregateMemory

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def outcome : Except Nat Bool → Nat × Nat
  | .ok true => (0, 0)
  | .ok false => (1, 0)
  | .error error => (2, error)

private def compareList (eq : Nat → Nat → Except Nat Bool) : List Nat → List Nat → Except Nat Bool
  | [], [] => .ok true
  | a :: as, b :: bs => do
    if ← eq a b then compareList eq as bs else pure false
  | _, _ => .ok false

private def word (bytes : List Nat) (phase count : Nat) : List Nat :=
  (List.range count).map (fun i => (trustIrListGet? bytes ((phase + i) % bytes.length)).getD 0)

private def expect {α : Type} : Except SemError α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"unexpected periodic value error: {repr error}")

private def nested : Nat → Value
  | 0 => .int 8 1
  | count + 1 => .aggregate [nested count]

private unsafe def typedVisibility : IO Unit := do
  let numbers := Tree.ofArray #[Value.int 8 1, .int 8 2, .int 8 3]
  let clipped : Tree Value 5 := .periodic numbers (by decide) 0 5
  for phase in List.range 7 do
    for count in List.range 11 do
      for nestedTemplate in [false, true] do
        let tree : Tree Value count := if nestedTemplate then
          .periodic clipped (by decide) phase count
          else .periodic numbers (by decide) phase count
        let expected := word (if nestedTemplate then [1, 2, 3, 1, 2] else [1, 2, 3]) phase count
        let plan : Plan := .array (.Array ⟨0⟩ count) ⟨count, 1⟩ count (.leaf .U8 ⟨1, 1⟩)
        let image ← expect (encode .le64 none plan (.array ⟨count, tree⟩))
        require "all finite periodic encoding phases and restart boundaries"
          (image.bytes.toList == expected.map (fun byte => some byte.toUInt8))
        let decoded ← expect (decode .le64 none Memory.empty plan image.bytes)
        require "finite periodic decode preserves every actual value"
          (← expect (equal .le64 plan (.array ⟨count, tree⟩) decoded))
  let hidden := nested 128
  let unit := Tree.ofArray #[hidden, Value.int 8 7, .int 8 9, .uninit]
  let tree : Tree Value 2 := .periodic unit (by decide) 1 2
  let value := Value.array ⟨2, tree⟩
  let empty : Value := .array ⟨0, .periodic unit (by decide) 0 0⟩
  let emptyPlan : Plan := .array (.Array ⟨0⟩ 0) ⟨0, 1⟩ 0 (.leaf .U8 ⟨1, 1⟩)
  require "empty periodic values do not inspect hidden invalid templates"
    (empty.depth == 1 && empty.depthSpec == 1 && (encode .le64 none emptyPlan empty).isOk)
  require "test template contains a hidden over-depth value" (hidden.depth > 64)
  let (depth, stats) := ValueDepthRuntime.depthWithStats value
  require "periodic depth excludes unused retained values"
    (depth == 2 && value.depthSpec == 2 && stats.visits < 20)
  let ty : Ty := .Array ⟨0⟩ 2
  let service := prepare { hasTargetInfo := true, types := [some .U8] } [ty]
  let plan ← expect (service.query ty)
  let encoded ← expect (encode .le64 none plan value)
  require "periodic encoder excludes hidden invalid retained values"
    (encoded.bytes.toList == [some 7, some 9])
  let (json, observed) := TrustIrEval.Observation.renderGraphWithStats [value]
  require "periodic observation excludes unused values"
    (observed.valueVisits == 3 && json == TrustIrEval.Observation.renderGraphSpec [value])
  let (address, memory) := Memory.empty.alloc 2 1 0 .rustStack
  let state := { MachineState.empty with memory, permissions := MachineState.empty.permissions.set ⟨0⟩ .owned }
  let (_, stored) ← expect ((storeValue service none ty (.ptr address (some ⟨0⟩)) value true).run state)
  let (loaded, _) ← expect ((loadValue service none ty (.ptr address (some ⟨0⟩)) true).run stored)
  require "actual typed periodic store/load preserves visible values" (← expect (equal .le64 plan value loaded))
  let invalid : Value := .array ⟨2, .periodic unit (by decide) 2 2⟩
  require "visible retained Uninit is still rejected" (!(encode .le64 none plan invalid).isOk)
  let count := 3 * (2^40 + 37)
  let largePlan : Plan := .array (.Array ⟨0⟩ count) ⟨count, 1⟩ count (.leaf .U8 ⟨1, 1⟩)
  let source := (ByteImage.ofList [some 1, some 2, some 3]).tile (count / 3)
  let decoded ← expect (decode .le64 none Memory.empty largePlan source)
  match decoded with
  | .array values =>
    match values.tree with
    | .periodic _ _ _ _ => pure ()
    | _ => throw (IO.userError "actual periodic decoder must produce the value carrier")
  | _ => throw (IO.userError "actual periodic decoder must produce an array")
  let reencoded ← expect (encode .le64 none largePlan decoded)
  require "actual periodic producer retains complete byte extent" (reencoded.bytes.size == count)
  require "actual periodic producer retains final byte" (reencoded.bytes.get (count - 1) == some 3)
  IO.println "PERIODIC_VALUE_TYPED_VISIBILITY_PASS"

private def shared : (depth : Nat) → Tree Nat (2 ^ depth)
  | 0 => .uniform 1 1
  | depth + 1 =>
    have positive : 0 < 2 ^ depth := Nat.pow_pos (by decide)
    have lower : 2 ^ (depth + 1) / 2 = 2 ^ depth := by rw [Nat.pow_succ]; omega
    have upper : 2 ^ (depth + 1) - 2 ^ (depth + 1) / 2 = 2 ^ depth := by rw [Nat.pow_succ]; omega
    let child := shared depth
    .split (by rw [Nat.pow_succ]; omega) (lower.symm ▸ child) (upper.symm ▸ child)

private def finiteUpdates : IO Unit := do
  let unit := Tree.ofArray #[1, 0, 7]
  for phase in List.range 7 do
    for count in List.range 18 do
      let tree : Tree Nat count := .periodic unit (by decide) phase count
      let expected := word [1, 0, 7] phase count
      for index in List.range (count + 2) do
        require "periodic lookup matches finite independent word" (tree.get? index == (trustIrListGet? expected index))
        match tree.set? index 99 with
        | none => require "only outside periodic writes refuse" (count ≤ index)
        | some updated =>
          require "inside periodic write succeeds" (index < count)
          for probe in List.range (count + 2) do
            let wanted := if probe == index then some 99 else (trustIrListGet? expected probe)
            require "periodic update changes only its actual lane" (updated.get? probe == wanted)
            require "periodic update retains its original snapshot" (tree.get? probe == (trustIrListGet? expected probe))
  let clipped : Tree Nat 5 := .periodic unit (by decide) 0 5
  let repeated : Tree Nat 40 := .periodic clipped (by decide) 1 40
  let expected := word (word [1, 0, 7] 0 5) 1 40
  for index in List.range 42 do
    require "finite periodic templates retain their own restart boundary" (repeated.get? index == (trustIrListGet? expected index))
  IO.println "PERIODIC_VALUE_UPDATES_PASS"

private unsafe def finiteEquality : IO Unit := do
  let ua := Tree.ofArray #[1, 0, 7]
  let ub := Tree.ofArray #[1, 2, 3, 7, 8]
  let callbacks := [fun a b : Nat => Except.ok (a == b),
    fun a b : Nat => if a == 7 && b == 8 then .error (a * 100 + b)
      else .ok ((a + b) % 7 != 0),
    fun _ _ : Nat => Except.ok false,
    fun a b : Nat => Except.error (a * 100 + b)]
  for phaseA in List.range 6 do
    for phaseB in List.range 6 do
      for count in List.range 25 do
        let left : Tree Nat count := .periodic ua (by decide) phaseA count
        let right : Tree Nat count := .periodic ub (by decide) phaseB count
        for eq in callbacks do
          let expected := outcome (compareList eq (word [1, 0, 7] phaseA count) (word [1, 2, 3, 7, 8] phaseB count))
          require "periodic equality specification preserves ordered callbacks"
            (outcome (left.eqByMSpec eq right) == expected)
          require "periodic equality runtime preserves ordered callbacks"
            (outcome (EqualityRuntime.tree eq left right) == expected)
          require "periodic equality public wrapper preserves ordered callbacks"
            (outcome (left.eqByM eq right) == expected)
  let clipped : Tree Nat 5 := .periodic ua (by decide) 1 5
  let left : Tree Nat 40 := .periodic clipped (by decide) 0 40
  let right : Tree Nat 40 := .periodic ua (by decide) 1 40
  require "equality must not flatten an unaligned finite restart"
    (outcome (left.eqByM (fun a b => .ok (a == b)) right) == (1, 0))
  IO.println "PERIODIC_VALUE_EQUALITY_PASS"

private unsafe def huge (depth : Nat) : IO Unit := do
  let source := shared depth
  let (same, stats) := EqualityRuntime.treeWithStats (fun a b => .ok (a == b) : Nat → Nat → Except Nat Bool) source source
  require "shared equality retains actual comparator results" (outcome same == (0, 0))
  require "shared equality retains source identity" (stats.visits < 150 && stats.hits + 1 ≥ depth)
  let unit := Tree.ofArray #[1, 1, 1]
  let periodic : Tree Nat (2 ^ depth) := .periodic unit (by decide) 1 (2 ^ depth)
  let (same, stats) := EqualityRuntime.treeWithStats (fun a b => .ok (a == b) : Nat → Nat → Except Nat Bool) periodic source
  require "periodic and shared shapes compare their actual lanes" (outcome same == (0, 0))
  require "periodic equality bounds physical window work" (stats.visits < 500)
  require "aliasing does not substitute for comparator false"
    (outcome (periodic.eqByM (fun _ _ => .ok false) periodic) == (1, 0))
  require "aliasing does not hide comparator errors"
    (outcome (periodic.eqByM (fun _ _ => .error 42) periodic) == (2, 42))
  let mut updated := periodic
  for k in List.range 1024 do
    let index := if k % 2 == 0 then k % (2 ^ depth) else 2 ^ depth - 1 - k % (2 ^ depth)
    match updated.set? index (100 + k) with
    | none => throw (IO.userError "huge periodic update refused")
    | some next =>
      updated := next
      require "huge periodic update hits exact lane" (updated.get? index == some (100 + k))
      require "periodic update history does not grow stored depth" (updated.height ≤ depth + 3)
      require "periodic updates do not nest retained templates" (updated.periodDepth ≤ 1)
      require "periodic updates retain their original snapshot" (periodic.get? index == some 1)
  IO.println s!"PERIODIC_VALUE_HUGE_PASS depth={depth}"

unsafe def main (args : List String) : IO Unit := do
  finiteUpdates
  finiteEquality
  typedVisibility
  huge (if args.contains "--bounded" then 12 else 63)
