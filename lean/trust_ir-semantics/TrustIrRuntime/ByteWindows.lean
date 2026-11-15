-- Copyright 2026 Andrew Yates | Apache-2.0
-- Runtime implementation and representation; correspondence is UNPROVED.
import TrustIr.State.ByteImageTraversal

namespace TrustIr.ByteImage.WindowRuntime

private structure Window where
  original : ByteImage
  offset : Nat
  count : Nat

/-- Drop view wrappers and descend concatenations only when the complete
    bounded window belongs to one child. No observed bytes justify a period. -/
private def normalize {size : Nat} (tree : Tree size) (offset count : Nat) : Window :=
  let count := min count (size - offset)
  if count == 0 then ⟨⟨_, tree⟩, offset, count⟩ else
  match tree with
  | .view original start _ _ => normalize original (start + offset) count
  | .append (leftSize := leftSize) left right =>
    if offset + count ≤ leftSize then normalize left offset count
    else if leftSize ≤ offset then normalize right (offset - leftSize) count
    else ⟨⟨_, tree⟩, offset, count⟩
  | _ => ⟨⟨_, tree⟩, offset, count⟩

private def Window.image (window : Window) : ByteImage :=
  window.original.slice window.offset window.count

/-- The callback representation is part of the logical operation: strip
    enclosing views and wholly containing append branches, then retain exactly
    one bounded view. Constructor-observing callbacks receive this same
    canonical window in the specification and compiled traversal. -/
private def canonicalImage (image : ByteImage) : ByteImage :=
  (normalize image.tree 0 image.size).image
private abbrev Key := Nat × USize × Nat × Nat
private unsafe def Window.key (window : Window) : Key :=
  (window.original.size, ptrAddrUnsafe window.original.tree, window.offset, window.count)
private structure SearchCache where
  memo : trustIrHashMap Key (Option Nat × Window) := ∅
  stats : Stats := {}

mutual
  private unsafe def search (test : Option UInt8 → Bool) (image : ByteImage)
      (offset count : Nat) : StateM SearchCache (Option Nat) := do
    let window := normalize image.tree offset count
    if window.count == 0 then return none
    let identity := window.key
    let state ← getThe SearchCache
    if let some (result, _) := trustIrHashMapFind? state.memo identity then
      modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
      return result
    modify fun state => { state with stats := { state.stats with visits := state.stats.visits + 1 } }
    let result ← searchBody test window.original.tree window.offset window.count
    modify fun state => { state with memo := state.memo.insert identity (result, window) }
    return result
  private unsafe def searchBody (test : Option UInt8 → Bool) {size : Nat} :
      Tree size → Nat → Nat → StateM SearchCache (Option Nat)
    | .fill _ byte, _, _ => pure (if test byte then some 0 else none)
    | .literal data, offset, count => pure (runtimeScanWhere test (fun i => (data[i]?).getD none) offset count 0)
    | .source _ read, offset, count => pure (runtimeScanWhere test read offset count 0)
    | .view original start _ _, offset, count => search test ⟨_, original⟩ (start + offset) count
    | .append (leftSize := leftSize) left right, offset, count => do
      let before := min count (leftSize - offset)
      match ← search test ⟨_, left⟩ offset before with
      | some index => pure (some index)
      | none => return (← search test ⟨_, right⟩ (offset + before - leftSize) (count - before)).map (before + ·)
    | .periodic (period := period) unit _ phase _, offset, count => do
      let start := (phase + offset) % period
      let before := min count (period - start)
      match ← search test ⟨_, unit⟩ start before with
      | some index => pure (some index)
      | none => return (← search test ⟨_, unit⟩ 0 (min period (count - before))).map (before + ·)
end

unsafe def firstWhereWithStats (test : Option UInt8 → Bool) (image : ByteImage) : Option Nat × Stats :=
  let (result, state) := (search test image 0 image.size).run {}
  (result, state.stats)
@[export l_TrustIr_ByteImage_firstWhere]
unsafe def firstWhere (test : Option UInt8 → Bool) (image : ByteImage) : Option Nat :=
  (firstWhereWithStats test image).1


private abbrev BlockKey := Key × Nat × Nat
private structure MapEntry (α ε : Type) where
  result : Except ε (CompactArray.Packed α)
  window : Window
private structure MapCache (α ε : Type) where
  memo : trustIrHashMap BlockKey (MapEntry α ε) := ∅
  stats : Stats := {}

mutual
  private unsafe def mapVisit {α ε : Type} (decode : ByteImage → Except ε α)
      (image : ByteImage) (width count : Nat) :
      StateM (MapCache α ε) (Except ε (CompactArray.Tree α count)) := do
    let window := normalize image.tree 0 image.size
    let identity := (window.key, width, count)
    let state ← getThe (MapCache α ε)
    if let some entry := trustIrHashMapFind? state.memo identity then
      match entry.result with
      | .error error => return .error error
      | .ok values =>
        if same : values.size = count then
          modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
          return .ok (same ▸ values.tree)
    modify fun state => { state with stats := { state.stats with visits := state.stats.visits + 1 } }
    let result ← mapBody decode window.image width count
    modify fun state => { state with memo := state.memo.insert identity ({ result := result.map (fun tree => ⟨count, tree⟩), window } : MapEntry α ε) }
    return result
  private unsafe def mapBody {α ε : Type} (decode : ByteImage → Except ε α)
      (image : ByteImage) (width count : Nat) :
      StateM (MapCache α ε) (Except ε (CompactArray.Tree α count)) := do
    if zero : count = 0 then return .ok (zero ▸ CompactArray.Tree.dense (by omega) .nil)
    if width == 0 then return (decode empty).map (CompactArray.Tree.uniform count)
    if image.size == width * count then
      if let some (unit, phase) := image.periodicWindow then
        if positive : 0 < unit.size then
          return ((runtimePeriodicBlocks decode unit positive width phase count).run []).map (·.1)
    if large : 2 ≤ count then
      match ← mapVisit decode (image.slice 0 ((count / 2) * width)) width (count / 2) with
      | .error error => return .error error
      | .ok left =>
        match ← mapVisit decode (image.slice ((count / 2) * width) ((count - count / 2) * width)) width (count - count / 2) with
        | .error error => return .error error
        | .ok right => return .ok (.split large left right)
    else if one : count = 1 then
      return (decode (image.slice 0 width)).map (fun value => one ▸ CompactArray.Tree.uniform 1 value)
    else
      have zero : count = 0 := by omega
      return .ok (zero ▸ CompactArray.Tree.dense (by omega) .nil)
end

unsafe def mapBlocksWithStats {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) : Except ε (CompactArray.Tree α count) × Stats :=
  let (result, state) := (mapVisit decode image width count).run {}
  (result, state.stats)
@[export l_TrustIr_ByteImage_mapBlocks]
unsafe def mapBlocks {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) : Except ε (CompactArray.Tree α count) :=
  (mapBlocksWithStats decode image width count).1

private structure CheckEntry (ε : Type) where
  result : Except ε (Option Nat)
  window : Window
private structure CheckCache (ε : Type) where
  memo : trustIrHashMap BlockKey (CheckEntry ε) := ∅
  stats : Stats := {}

mutual
  private unsafe def checkVisit {ε : Type} (check : ByteImage → Except ε (Option Nat))
      (image : ByteImage) (width count : Nat) : StateM (CheckCache ε) (Except ε (Option Nat)) := do
    let window := normalize image.tree 0 image.size
    let identity := (window.key, width, count)
    let state ← getThe (CheckCache ε)
    if let some entry := trustIrHashMapFind? state.memo identity then
      modify fun state => { state with stats := { state.stats with hits := state.stats.hits + 1 } }
      return entry.result
    modify fun state => { state with stats := { state.stats with visits := state.stats.visits + 1 } }
    let result ← checkBody check window.image width count
    modify fun state => { state with memo := state.memo.insert identity ({ result, window } : CheckEntry ε) }
    return result
  private unsafe def checkBody {ε : Type} (check : ByteImage → Except ε (Option Nat))
      (image : ByteImage) (width count : Nat) : StateM (CheckCache ε) (Except ε (Option Nat)) := do
    if count == 0 then return .ok none
    if width == 0 then return check empty
    if image.size == width * count then
      if let some (unit, phase) := image.periodicWindow then
        if positive : 0 < unit.size then
          return ((runtimePeriodicCheck check unit positive width phase count).run []).map (·.1)
    if large : 2 ≤ count then
      match ← checkVisit check (image.slice 0 ((count / 2) * width)) width (count / 2) with
      | .error error => return .error error
      | .ok left =>
        -- Missing bytes do not short-circuit later semantic errors.
        match ← checkVisit check (image.slice ((count / 2) * width) ((count - count / 2) * width)) width (count - count / 2) with
        | .error error => return .error error
        | .ok right => return .ok (runtimeCombineMissing ((count / 2) * width) left right)
    else return check (image.slice 0 width)
end

unsafe def checkBlocksWithStats {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) : Except ε (Option Nat) × Stats :=
  let (result, state) := (checkVisit check image width count).run {}
  (result, state.stats)
@[export l_TrustIr_ByteImage_checkBlocks]
unsafe def checkBlocks {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) : Except ε (Option Nat) :=
  (checkBlocksWithStats check image width count).1

end TrustIr.ByteImage.WindowRuntime
