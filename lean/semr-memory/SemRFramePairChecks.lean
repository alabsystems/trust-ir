-- Copyright 2026 Andrew Yates | Apache-2.0
import SemRFramePair
import SemRFrameCaller

namespace SemR.MemoryEmbedding.FramePair.Checks

open TrustIr (Memory Allocation AllocId)

private def ids : Nat → AllocId := fun n => ⟨n⟩
private def frameMemory : Memory := (Memory.empty.alloc 16 16 0 .rustStack).snd
private def frame : Allocation := Memory.empty.allocRecord 16 16 0 .rustStack
private def source : Mem := sourceAllocated Mem.empty 8 8
private def target : Memory := (frameMemory.alloc 8 8 0 .rustStack).snd
private def sourceIds : Nat → AllocId := extendIds Mem.empty frameMemory ids

private theorem placed : PlacedFrameInput source target sourceIds frame 1040 16 := by
  refine ⟨⟨((empty_embeds ids).allocate_private 16 16).allocate_source 8 8 (by decide) (by decide),
    rfl, ?_, rfl, rfl⟩, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro index allocation present
  cases index with
  | zero => decide
  | succ index =>
    change nth? [] index = some allocation at present
    simp [nth?] at present

private def raw : RawMemory := fun _ => 0

private theorem represented : RawRepresents target raw := by
  intro address byte _ defined
  cases defined

/-- Baseline allocation model with uninitialized live source storage. -/
theorem uninitialized_pair (fp lr : Word) :
    let saved := rawWriteBytes (rawWriteBytes raw frame.base (wordBytes fp))
      (frame.base + 8) (wordBytes lr)
    Embeds source (saveMemory target frame.base fp lr) sourceIds ∧
    rawReadWord saved frame.base = fp ∧ rawReadWord saved (frame.base + 8) = lr :=
  placed_pair_raw_readback placed rfl represented fp lr

-- Initialize two actual source bytes through SemR's existing byte writer,
-- and the same target bytes through canonical Memory.writeBytes. The other
-- six source bytes stay uninitialized; both cases remain in full Embeds.
private def initializedAllocation : Alloc :=
  { base := 1024, size := 8, align := 8, live := true,
    data := writeBytes [] 0 [.init 0x5a, .init 0xc3] }
private def initializedSource : Mem :=
  { source with allocs := setNth source.allocs 0 initializedAllocation }
private def sourceRecord : Allocation :=
  { id := ⟨1⟩, base := 1040, size := 8, alive := true, origin := .rustStack, requested := 8 }
private def initializedTarget : Memory := target.writeBytes 1040 [0x5a, 0xc3]
private def initializedRaw : RawMemory := rawWriteBytes raw 1040 [0x5a, 0xc3]

private theorem initialized_embeds : Embeds initializedSource initializedTarget sourceIds := by
  refine ⟨placed.embedding.layout,
    write_preserves_fresh target 1040 [0x5a, 0xc3] placed.embedding.fresh (by decide),
    ?_, ?_, ?_⟩
  · intro index allocation present
    cases index with
    | zero =>
      change some initializedAllocation = some allocation at present
      cases present
      exact ⟨sourceRecord, rfl, ⟨rfl, rfl, rfl, ⟨by decide, by decide⟩, by decide⟩⟩
    | succ index =>
      change nth? [] index = some allocation at present
      simp [nth?] at present
  · intro index allocation record present found _ offset bounded
    cases index with
    | zero =>
      change some initializedAllocation = some allocation at present
      cases present
      change some sourceRecord = some record at found
      cases found
      change offset < 8 at bounded
      have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
          offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
      rcases positions with h | h | h | h | h | h | h | h
      all_goals subst offset; first | rfl | exact True.intro
    | succ index =>
      change nth? [] index = some allocation at present
      simp [nth?] at present
  · intro first allocation present second other another _
    cases first with
    | zero =>
      cases second with
      | zero => rfl
      | succ second =>
        change nth? [] second = some other at another
        simp [nth?] at another
    | succ first =>
      change nth? [] first = some allocation at present
      simp [nth?] at present

private theorem initialized_placed :
    PlacedFrameInput initializedSource initializedTarget sourceIds frame 1040 16 := by
  refine ⟨⟨initialized_embeds, rfl, ?_, rfl, rfl⟩,
    rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro index allocation present
  cases index with
  | zero => decide
  | succ index =>
    change nth? [] index = some allocation at present
    simp [nth?] at present

private theorem initialized_represents : RawRepresents initializedTarget initializedRaw :=
  raw_represents_write represented 1040 [0x5a, 0xc3] (by decide)

/-- Actual inhabited source storage discharges separation for every byte of
the eight-byte allocation above the frame, including the boundary byte. The
conclusion retains complete function-array equality, with arbitrary FP/LR. -/
theorem initialized_source_store_agreement (fp lr : Word) (byte : BitVec 8)
    (offset : Nat) (inside : offset < 8) :
    FrameCaller.ActualCallAgreement
      (FrameStep.arrayStore
        (FrameStep.saveMemoryEffect initializedRaw (BitVec.ofNat 64 1040) fp lr)
        (BitVec.ofNat 64 (1040 + offset)) byte)
      (FrameStep.saveMemoryEffect
        (FrameStep.arrayStore initializedRaw (BitVec.ofNat 64 (1040 + offset)) byte)
        (BitVec.ofNat 64 1040) fp lr)
      ((BitVec.ofNat 64 1040) + BitVec.ofInt 64 (-16))
      ((BitVec.ofNat 64 1040) + BitVec.ofInt 64 (-16)) :=
  FrameCaller.source_store_agreement initializedRaw (BitVec.ofNat 64 1040) fp lr
    initialized_placed rfl 0 initializedAllocation sourceRecord rfl rfl offset
    (by change offset + 1 ≤ 8; omega) byte

/-- Even this legal fresh-frame fixture falsifies the historical bare-source
raw equation. Restore reads the saved bytes; it does not undo these stores. -/
theorem saved_frame_differs_from_bare_source :
    FrameStep.saveMemoryEffect initializedRaw (BitVec.ofNat 64 1040)
      (BitVec.ofNat 64 1) (BitVec.ofNat 64 0) (BitVec.ofNat 64 1024) ≠
      initializedRaw (BitVec.ofNat 64 1024) := by decide

/-- An inhabited initialized-source fixture: both initialized bytes, all six
uninitialized bytes, full raw/canonical representation, and all128 saved bits
survive the actual frame pair operations for arbitrary FP/LR values. -/
theorem initialized_pair (fp lr : Word) :
    let memory := saveMemory initializedTarget frame.base fp lr
    let saved := rawWriteBytes (rawWriteBytes initializedRaw frame.base (wordBytes fp))
      (frame.base + 8) (wordBytes lr)
    Embeds initializedSource memory sourceIds ∧ RawRepresents memory saved ∧
    memory.readBytes 1040 2 = some [0x5a, 0xc3] ∧
    rawReadWord saved frame.base = fp ∧ rawReadWord saved (frame.base + 8) = lr := by
  have image := placed_pair_raw_memory initialized_placed rfl initialized_represents fp lr
  have values := placed_pair_raw_readback initialized_placed rfl initialized_represents fp lr
  refine ⟨image.1, image.2.1, ?_, values.2.1, values.2.2⟩
  change ((initializedTarget.writeBytes 1024 (wordBytes fp)).writeBytes 1032 (wordBytes lr)).readBytes
    1040 2 = some [0x5a, 0xc3]
  rw [TrustIr.writeBytes_non_aliasing _ 1040 1032 2 (wordBytes lr)
    (Or.inr (by rw [wordBytes_length]; decide))]
  rw [TrustIr.writeBytes_non_aliasing _ 1040 1024 2 (wordBytes fp)
    (Or.inr (by rw [wordBytes_length]; decide))]
  rfl

example : ((BitVec.ofNat 64 1040) - (BitVec.ofNat 64 16)).toNat = 1024 :=
  pre_index_address placed rfl

example : ((BitVec.ofNat 64 1024) + (BitVec.ofNat 64 16)).toNat = 1040 :=
  post_index_sp placed rfl

example : (BitVec.ofNat 64 8 - BitVec.ofNat 64 16).toNat ≠ 1024 := by decide

example : TrustIr.decodeIntBytes (wordBytes (BitVec.ofNat 64 18446744073709551615)) =
    18446744073709551615 := wordBytes_decode _

/-- Wrong byte order changes the value; it is not an admitted codec. -/
example : TrustIr.decodeIntBytes (wordBytes (BitVec.ofNat 64 0x0123456789abcdef)).reverse ≠
    0x0123456789abcdef := by decide

private def saved : RawMemory :=
  rawWriteBytes (rawWriteBytes raw 1024 (wordBytes 0x0123456789abcdef))
    1032 (wordBytes 0xfedcba9876543210)

/-- A raw alias into saved LR cannot acquire the required callee frame rely. -/
example : ¬ KeepsFrame saved (rawStore saved (BitVec.ofNat 64 1032) 0xaa) 1024 := by
  intro keeps
  have bad := keeps 8 (by decide)
  change (0xaa : BitVec 8) = (0x10 : BitVec 8) at bad
  exact (by decide : (0xaa : BitVec 8) ≠ 0x10) bad

example : rawReadWord (rawStore saved (BitVec.ofNat 64 1032) 0xaa) 1032 ≠
    (0xfedcba9876543210 : Word) := by decide

-- A second actual source allocation has a distinct initialized byte. Source
-- addresses and target addresses deliberately differ through the existing ids.
private def twoSource : Mem := sourceAllocated initializedSource 8 8
private def twoTarget : Memory := (initializedTarget.alloc 8 8 0 .rustStack).snd
private def twoIds : Nat → AllocId := extendIds initializedSource initializedTarget sourceIds
private def otherAllocation : Alloc :=
  { base := 1032, size := 8, align := 8, live := true, data := [] }
private def otherRecord : Allocation :=
  { id := ⟨2⟩, base := 1048, size := 8, alive := true, origin := .rustStack, requested := 8 }
private theorem two_embeds : Embeds twoSource twoTarget twoIds :=
  initialized_embeds.allocate_source 8 8 (by decide) (by decide)
private def readySource : Mem := written twoSource 1 0 otherAllocation [.init 0x44]
private def readyTarget : Memory := twoTarget.writeBytes 1048 [0x44]
private def initialR0 : RawMemory := rawWriteBytes initializedRaw 1048 [0x44]
private theorem ready_embeds : Embeds readySource readyTarget twoIds :=
  two_embeds.written_u8 1 0 otherAllocation otherRecord rfl rfl rfl (by decide) 0x44
private theorem ready_represents : RawRepresents readyTarget initialR0 := by
  have prior : RawRepresents twoTarget initializedRaw := initialized_represents
  exact raw_represents_write prior 1048 [0x44] (by decide)

private def u8Node : Node :=
  { inst := .store (.int .u8) 0 1 false none, results := [] }
private def u8Block : Block :=
  { id := 0, params := [(0, .ptr), (1, .int .u8)],
    body := [u8Node, { inst := .ret [], results := [] }] }
private def u8Signature : FuncTy := { params := [.ptr, .int .u8], returns := [], vararg := false }
private def u8Function : Func := { id := 0, ty := 0, entry := 0, blocks := [u8Block] }
private def u8Module : Module := { funcTys := [u8Signature], enums := [], functions := [u8Function] }
private def u8Before : Core :=
  { fn := u8Function, sig := u8Signature, block := u8Block, pc := 0,
    env := [(0, .ptr 0 1), (1, .int .u8 0x7f)], depth := 1, stack := [],
    openFrames := [], nextFrame := 0, mem := readySource }
private def u8After : Core :=
  { next u8Before with mem := written readySource 0 1 initializedAllocation [.init 0x7f] }

/-- This is the current source computation on an initialized allocation, not
an assumed post heap or a detached raw memory write. -/
theorem initialized_u8_store_executes :
    storeStep 64 u8Before u8Node (.int .u8) 0 1 false none = .ok u8After :=
  storeStep_u8 64 u8Before 0 1 0 1 initializedAllocation 0x7f
    rfl rfl rfl rfl (by decide) (by decide)

/-- Every typed byte uses the same checked source Store, with no assumed
execution equation. The updated Core retains cells and caller lineages. -/
theorem arbitrary_u8_store_executes (byte : UInt8) :
    let before := { u8Before with env := [(0, .ptr 0 1), (1, .int .u8 byte.toNat)] }
    storeStep 64 before u8Node (.int .u8) 0 1 false none =
      .ok { next before with mem := written readySource 0 1 initializedAllocation [.init byte.toNat] } :=
  storeStep_u8 64 _ 0 1 0 1 initializedAllocation byte
    rfl rfl rfl rfl (by decide) (by decide)

/-- Initialized source loads derive their actual SSA result for either load
mode. The caller/cell/frame state remains the original source state. -/
theorem initialized_u8_load_executes (volatile : Bool) :
    loadStep 64 u8Before
      { inst := .load (.int .u8) 0 volatile none, results := [2] }
      (.int .u8) 0 volatile none =
      .ok { next u8Before with env := (2, .int .u8 0xc3) :: u8Before.env } :=
  loadStep_u8 64 u8Before 0 2 0 1 initializedAllocation 0xc3 volatile
    rfl rfl rfl (by decide) (by decide) rfl

private def u8LoadBlock (volatile : Bool) : Block :=
  { id := 0, params := [(0, .ptr)], body := [
    { inst := .load (.int .u8) 0 volatile none, results := [2] },
    { inst := .ret [2], results := [] }] }
private def u8LoadSignature : FuncTy :=
  { params := [.ptr], returns := [.int .u8], vararg := false }
private def u8LoadFunction (volatile : Bool) : Func :=
  { id := 0, ty := 0, entry := 0, blocks := [u8LoadBlock volatile] }
private def u8LoadModule (volatile : Bool) : Module :=
  { funcTys := [u8LoadSignature], enums := [], functions := [u8LoadFunction volatile] }
private def u8LoadBefore (volatile : Bool) : Core :=
  { u8Before with
    fn := u8LoadFunction volatile, sig := u8LoadSignature,
    block := u8LoadBlock volatile, env := [(0, .ptr 0 1)] }

/-- The loaded source byte and the raw select agree even though the source
allocation starts at 1024 and the target allocation at 1040. Both load modes
use the derived access; successful source execution is not assumed. -/
theorem initialized_u8_load_source_raw (volatile : Bool) :
    let before := u8LoadBefore volatile
    let after := { next before with env := (2, .int .u8 0xc3) :: before.env }
    Step (u8LoadModule volatile) before (.cont after) ∧
    getV after 2 = .ok (.int .u8 0xc3) ∧
    Embeds after.mem readyTarget twoIds ∧ RawRepresents readyTarget initialR0 ∧
    initialR0 (BitVec.ofNat 64 1041) = FrameStep.byteBits 0xc3 :=
  FrameCaller.source_u8_load_derived_raw (u8LoadModule volatile) (u8LoadBefore volatile)
    0 2 0 1 initializedAllocation sourceRecord 0xc3 initialR0 volatile
    rfl rfl rfl ready_embeds rfl rfl (by decide) (by decide) rfl ready_represents

/-- The fetched original source node has the same checked transition; the
terminal Core and actual final Return remain part of the source witness. -/
theorem initialized_u8_store_reaches_terminal :
    Reaches u8Module u8Before u8After ∧ Step u8Module u8After (.done (.ret [])) := by
  have step := step_u8_of_storeStep u8Module u8Before u8After 0 1 rfl
    initialized_u8_store_executes
  refine ⟨Reaches.step _ _ _ step (Reaches.refl _), ?_⟩
  have terminal : stepCore u8Module u8After = .done (.ret []) := rfl
  rw [← terminal]
  exact step_complete u8Module u8After

/-- The exact source-owned raw exit starts at initialR0 and retains every
other function-array byte. Its destination is the injected SOURCE pointer. -/
theorem initialized_u8_source_raw :
    Step u8Module u8Before (.cont u8After) ∧
    Embeds u8After.mem (readyTarget.writeBytes 1041 [0x7f]) twoIds ∧
    RawRepresents (readyTarget.writeBytes 1041 [0x7f])
      (FrameStep.arrayStore initialR0 (BitVec.ofNat 64 1041) (BitVec.ofNat 8 0x7f)) :=
  FrameCaller.source_u8_store_derived_raw u8Module u8Before 0 1 0 1
    initializedAllocation sourceRecord 0x7f initialR0 rfl rfl rfl rfl
    ready_embeds rfl rfl (by decide) (by decide) ready_represents

/-- Both another initialized byte of the same allocation and an initialized
byte of a DIFFERENT source allocation survive. Metadata and the complete
source Core are retained by the source-step extraction, not rebuilt. -/
theorem initialized_u8_preserves_other_source_bytes :
    (readyTarget.writeBytes 1041 [0x7f]).readBytes 1040 1 = some [0x5a] ∧
    (readyTarget.writeBytes 1041 [0x7f]).readBytes 1048 1 = some [0x44] ∧
    u8After.mem.nextAddr = u8Before.mem.nextAddr ∧
    (readyTarget.writeBytes 1041 [0x7f]).allocations = readyTarget.allocations ∧
    u8After = { next u8Before with
      mem := written u8Before.mem 0 1 initializedAllocation [.init 0x7f] } := by
  exact ⟨rfl, rfl, rfl, rfl,
    storeStep_u8_core (byte := (0x7f : UInt8)) rfl rfl rfl rfl initialized_u8_store_executes⟩

private def poisonBefore : Core :=
  { u8Before with env := [(0, .ptr 0 1), (1, .poison (.int .u8))] }

/-- Plain source Store transports poison. It cannot be relabeled as an
initialized byte to enter the initialized source/raw bridge. -/
theorem source_u8_poison_is_not_initialized (byte : UInt8) :
    storeStep 64 poisonBefore u8Node (.int .u8) 0 1 false none =
      .ok { next poisonBefore with
        mem := written readySource 0 1 initializedAllocation [.uninit] } ∧
    getV poisonBefore 1 ≠ .ok (.int .u8 byte.toNat) := by
  refine ⟨rfl, ?_⟩
  intro impossible
  cases impossible

private def deadAllocation : Alloc := { initializedAllocation with live := false }
private def deadSource : Mem :=
  { readySource with allocs := setNth readySource.allocs 0 deadAllocation }
private def deadBefore : Core := { u8Before with mem := deadSource }
private def outsideBefore : Core :=
  { u8Before with env := [(0, .ptr 0 8), (1, .int .u8 0x7f)] }
private def oversizedBefore : Core :=
  { u8Before with env := [(0, .ptr 0 1), (1, .int .u8 256)] }

/-- Actual dead/out-of-bounds/value-image computations refuse; address labels
or an initialized byte at the numeric target cannot authorize the source step. -/
theorem source_u8_bad_accesses_refuse :
    storeStep 64 deadBefore u8Node (.int .u8) 0 1 false none =
      .stop (.ub "Store: use after dealloc") ∧
    storeStep 64 outsideBefore u8Node (.int .u8) 0 1 false none =
      .stop (.ub "Store: access [8..9) is out of bounds for allocation size 8") ∧
    storeStep 64 oversizedBefore u8Node (.int .u8) 0 1 false none =
      .stop (.typeError "TypeError: integer value is out of range for the target width") ∧
    ¬ PointerImage readySource readyTarget twoIds (.ptr 0 1) (.ptr 1041 none) := by
  exact ⟨rfl, rfl, rfl, fun impossible => impossible⟩

-- The canonical conversion of the original captured JSON module is quoted
-- byte for byte below and decoded by SemR. Its actual function names, target,
-- operations and SSA edges are retained. The conversion is DATA, not a Rust
-- refinement, ABI licence or native frame certificate.
private def pathLoad : Node :=
  { inst := .load (.int .u8) 1 false none, results := [3] }
private def pathTrunc : Node :=
  { inst := .cast .trunc (.int .u64) (.int .u8) 2, results := [4] }
private def pathStore : Node :=
  { inst := .store (.int .u8) 0 4 false none, results := [] }
private def pathWide : Node :=
  { inst := .cast .zext (.int .u8) (.int .u64) 3, results := [5] }
private def pathReturn : Node := { inst := .ret [5], results := [] }
private def pathBlock : Block :=
  { id := 0, params := [(0, .ptr), (1, .ptr), (2, .int .u64)],
    body := [pathLoad, pathTrunc, pathStore, pathWide, pathReturn] }
private def pathSignature : FuncTy :=
  { params := [.ptr, .ptr, .int .u64], returns := [.int .u64], vararg := false }
private def pathFunction : Func :=
  { id := 0, ty := 0, entry := 0, blocks := [pathBlock],
    name := [95, 82, 78, 118, 67, 115, 52, 65, 104, 105, 115, 77, 66, 84, 120, 112, 118, 95, 50, 48, 115, 111, 117, 114, 99, 101, 95, 109, 101, 109, 111, 114, 121, 95, 99, 97, 108, 108, 101, 114, 50, 48, 115, 111, 117, 114, 99, 101, 95, 109, 101, 109, 111, 114, 121, 95, 99, 97, 108, 108, 101, 101] }
private def callNode : Node := { inst := .call 0 [0, 1, 2], results := [3] }
private def callerReturn : Node := { inst := .ret [3], results := [] }
private def callerBlock : Block :=
  { id := 0, params := pathBlock.params, body := [callNode, callerReturn] }
private def callerFunction : Func :=
  { id := 1, ty := 0, entry := 0, blocks := [callerBlock],
    name := [115, 111, 117, 114, 99, 101, 95, 109, 101, 109, 111, 114, 121, 95, 99, 97, 108, 108, 101, 114] }
private def pathModule : Module :=
  { funcTys := [pathSignature], enums := [], functions := [pathFunction, callerFunction],
    target := some { triple := [97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109, 97, 99, 111, 115, 120],
                     pointerSize := 8, bigEndian := false, abi := none, structPassing := 0 } }

-- Original capture fccc4c260617ebf86cc83a8bf32e56a17957aeb48949ea17050a997f116a2dae;
-- JSON module 5f421556cd357f2d25ec69b3da974153ab65f9a24123398fdfe412d5541283e6.
-- Ordinary trust-ir convert writes canonical wire v41, SHA-256
-- d87bf94e7127e1e6196efa795299cd021d96b22b264eb5e33f045d7d3c9940f5.
private def originalB8Bytes : List Nat :=
  [84, 82, 85, 83, 84, 95, 73, 82, 41, 0, 0, 0, 9, 20, 115, 111, 117, 114, 99, 101, 95, 109, 101, 109,
   111, 114, 121, 95, 99, 97, 108, 108, 101, 114, 18, 97, 114, 109, 54, 52, 45, 97, 112, 112, 108, 101, 45, 109,
   97, 99, 111, 115, 120, 10, 115, 117, 98, 106, 101, 99, 116, 46, 114, 115, 62, 95, 82, 78, 118, 67, 115, 52,
   65, 104, 105, 115, 77, 66, 84, 120, 112, 118, 95, 50, 48, 115, 111, 117, 114, 99, 101, 95, 109, 101, 109, 111,
   114, 121, 95, 99, 97, 108, 108, 101, 114, 50, 48, 115, 111, 117, 114, 99, 101, 95, 109, 101, 109, 111, 114, 121,
   95, 99, 97, 108, 108, 101, 101, 28, 116, 114, 117, 115, 116, 45, 100, 105, 114, 101, 99, 116, 45, 108, 97, 110,
   101, 45, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 20, 115, 111, 117, 114, 99, 101, 95, 109, 101, 109, 111,
   114, 121, 95, 99, 97, 108, 108, 101, 101, 2, 116, 111, 4, 102, 114, 111, 109, 5, 118, 97, 108, 117, 101, 0,
   1, 3, 13, 13, 8, 1, 8, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 1, 0, 3, 0, 13,
   1, 13, 2, 8, 5, 6, 5, 1, 0, 0, 1, 3, 0, 1, 0, 5, 26, 0, 1, 0, 5, 0, 8, 5,
   2, 1, 4, 0, 1, 0, 6, 19, 0, 1, 1, 7, 5, 0, 4, 0, 0, 0, 0, 1, 0, 6, 13, 0,
   1, 1, 5, 1, 5, 8, 3, 1, 5, 0, 1, 0, 7, 4, 0, 1, 1, 20, 1, 5, 0, 0, 1, 0,
   8, 1, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 1, 0, 1, 3, 0, 6, 1, 7, 2, 8, 1, 2,
   0, 0, 1, 0, 1, 0, 5, 4, 0, 2, 4, 1, 5, 1, 0, 0, 0, 1, 0, 3, 0, 13, 1, 13,
   2, 8, 2, 18, 0, 3, 0, 1, 2, 1, 3, 0, 1, 0, 12, 13, 0, 0, 20, 1, 3, 0, 0, 1,
   0, 13, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 6, 1, 7, 2, 8, 0, 0,
   2, 4, 1, 0, 0, 0, 1, 1, 8, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Kernel computation decodes the actual canonical conversion into the exact
module used by every source-path/caller/alias computation below. Metadata
transport and this quotation grant no source or native admission. -/
theorem original_b8_module_decodes : decode originalB8Bytes = .ok pathModule := by
  rfl
private def callerEntry : Core :=
  { fn := callerFunction, sig := pathSignature, block := callerBlock, pc := 0,
    env := [(0, .ptr 0 1), (1, .ptr 1 0), (2, .int .u64 0x17f)], depth := 2,
    stack := [], openFrames := [27], nextFrame := 28,
    cells := [{ id := 9, ty := .bool, value := .bool true }], nextCell := 10,
    mem := readySource }
private def pathEntry : Core :=
  { callerEntry with
    fn := pathFunction, block := pathBlock, pc := 0,
    env := [(2, .int .u64 0x17f), (1, .ptr 1 0), (0, .ptr 0 1)], depth := 1,
    stack := [suspend callerEntry callNode] }
private def pathLoaded : Core :=
  { next pathEntry with env := (3, .int .u8 0x44) :: pathEntry.env }
private def pathTruncated : Core :=
  { next pathLoaded with env := (4, .int .u8 0x7f) :: pathLoaded.env }
private def pathStored : Core :=
  { next pathTruncated with
    mem := written readySource 0 1 initializedAllocation [.init 0x7f] }
private def pathWidened : Core :=
  { next pathStored with env := (5, .int .u64 0x44) :: pathStored.env }
private def callerResumed : Core :=
  { callerEntry with
    pc := 1, env := (3, .int .u64 0x44) :: callerEntry.env,
    mem := pathStored.mem }
private def readyOtherAllocation : Alloc := { otherAllocation with data := [.init 0x44] }

/-- Every operation is the existing actual computation, including call entry
and return to the suspended source caller. -/
theorem source_path_computations :
    callStep pathModule callerEntry callNode 0 [0, 1, 2] = .ok pathEntry ∧
    loadStep 64 pathEntry pathLoad (.int .u8) 1 false none = .ok pathLoaded ∧
    castStep 64 pathLoaded pathTrunc .trunc (.int .u64) (.int .u8) 2 = .ok pathTruncated ∧
    storeStep 64 pathTruncated pathStore (.int .u8) 0 4 false none = .ok pathStored ∧
    castStep 64 pathStored pathWide .zext (.int .u8) (.int .u64) 3 = .ok pathWidened ∧
    retStep 64 pathWidened pathReturn [5] = .ok callerResumed ∧
    retStep 64 callerResumed callerReturn [3] = .stop (.ret [.int .u64 0x44]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original captured callee's fetched nodes execute for every typed U64
operand, deriving all four data operations from the entry state. The loaded
byte is retained before the write; source and raw storage keep their distinct
addresses. This is a callee-entry theorem, not an assertion that this changed
input was supplied by the frozen original caller or by a native invocation. -/
theorem source_path_derives_each_operation_from_entry_values (value : UInt64) :
    let entry := { pathEntry with
      env := [(2, .int .u64 value.toNat), (1, .ptr 1 0), (0, .ptr 0 1)] }
    let byte := UInt8.ofNat value.toNat
    ∃ widened : Core,
      Reaches pathModule entry widened ∧
      Step pathModule widened (ofR (retStep 64 widened pathReturn [5])) ∧
      getV widened 5 = .ok (.int .u64 0x44) ∧
      widened.mem = written entry.mem 0 1 initializedAllocation [.init byte.toNat] ∧
      widened.cells = entry.cells ∧ widened.nextCell = entry.nextCell ∧
      widened.stack = entry.stack ∧ widened.openFrames = entry.openFrames ∧
      widened.nextFrame = entry.nextFrame ∧
      Embeds widened.mem (readyTarget.writeBytes 1041 [byte]) twoIds ∧
      RawRepresents (readyTarget.writeBytes 1041 [byte])
        (FrameStep.arrayStore initialR0 (BitVec.ofNat 64 1041) (FrameStep.byteBits byte)) :=
  FrameCaller.source_u8_load_store_derived_raw pathModule _ 0 1 2 3 4 5
    1 0 0 1 readyOtherAllocation initializedAllocation sourceRecord 0x44 value initialR0
    rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    rfl rfl (by decide) (by decide) rfl rfl rfl (by decide) (by decide)
    ready_embeds rfl ready_represents

/-- The whole two-function IR path reaches its original source caller return;
its byte/cells/caller lineage are supplied by the SOURCE operations. The
initial raw array is fixed before the path, with no native post-state input. -/
theorem source_path_reaches_caller_return :
    Reaches pathModule callerEntry callerResumed ∧
    Step pathModule callerResumed (.done (.ret [.int .u64 0x44])) ∧
    Embeds callerResumed.mem (readyTarget.writeBytes 1041 [0x7f]) twoIds ∧
    RawRepresents (readyTarget.writeBytes 1041 [0x7f])
      (FrameStep.arrayStore initialR0 (BitVec.ofNat 64 1041) (BitVec.ofNat 8 0x7f)) ∧
    callerResumed.cells = callerEntry.cells ∧
    callerResumed.nextCell = callerEntry.nextCell ∧
    callerResumed.openFrames = callerEntry.openFrames ∧
    callerResumed.nextFrame = callerEntry.nextFrame := by
  have computations := source_path_computations
  have path := FrameCaller.source_u8_load_store_path pathModule
    pathEntry pathLoaded pathTruncated pathStored pathWidened 0 1 2 3 4 5
    1 0 0 1 readyOtherAllocation initializedAllocation sourceRecord 0x7f initialR0
    (.ok callerResumed) rfl rfl rfl computations.2.1 rfl computations.2.2.1
    rfl rfl rfl rfl computations.2.2.2.1 rfl computations.2.2.2.2.1
    rfl computations.2.2.2.2.2.1 ready_embeds rfl rfl (by decide) ready_represents
  have enter : Step pathModule callerEntry (.cont pathEntry) := by
    have actual := step_complete pathModule callerEntry
    have entered : stepCore pathModule callerEntry = .cont pathEntry := rfl
    rw [entered] at actual
    exact actual
  have finish : Step pathModule callerResumed (.done (.ret [.int .u64 0x44])) := by
    have actual := step_complete pathModule callerResumed
    have terminal : stepCore pathModule callerResumed = .done (.ret [.int .u64 0x44]) := rfl
    rw [terminal] at actual
    exact actual
  have returned : Reaches pathModule pathWidened callerResumed :=
    Reaches.step _ _ _ path.2.1 (Reaches.refl _)
  have join : ∀ {a b c : Core}, Reaches pathModule a b → Reaches pathModule b c →
      Reaches pathModule a c := by
    intro a b c first last
    induction first with
    | refl => exact last
    | step _ _ _ step _ ih => exact Reaches.step _ _ _ step (ih last)
  refine ⟨Reaches.step _ _ _ enter (join path.1 returned), finish, ?_, path.2.2.2.2.2.2.2.2.2.1,
    rfl, rfl, rfl, rfl⟩
  simpa only [callerResumed, pathStored, pathWidened, next] using path.2.2.2.2.2.2.2.2.1


/-- The decoded captured module itself has the complete source-caller path,
including the original suspended caller's terminal return and fixed-entry
raw byte equation. This does not identify a native execution with this path. -/
theorem original_b8_source_execution :
    ∃ module, decode originalB8Bytes = .ok module ∧
      Reaches module callerEntry callerResumed ∧
      Step module callerResumed (.done (.ret [.int .u64 0x44])) ∧
      Embeds callerResumed.mem (readyTarget.writeBytes 1041 [0x7f]) twoIds ∧
      RawRepresents (readyTarget.writeBytes 1041 [0x7f])
        (FrameStep.arrayStore initialR0 (BitVec.ofNat 64 1041) (BitVec.ofNat 8 0x7f)) ∧
      callerResumed.cells = callerEntry.cells ∧
      callerResumed.nextCell = callerEntry.nextCell ∧
      callerResumed.openFrames = callerEntry.openFrames ∧
      callerResumed.nextFrame = callerEntry.nextFrame :=
  ⟨pathModule, original_b8_module_decodes, source_path_reaches_caller_return⟩

private def uninitializedEntry : Core :=
  { pathEntry with env := [(2, .int .u64 0x17f), (1, .ptr 1 7), (0, .ptr 0 1)] }
private def uninitializedLoaded : Core :=
  { next uninitializedEntry with
    env := (3, .partialBytes (.int .u8) [.uninit]) :: uninitializedEntry.env }
private def poisonedTruncated : Core :=
  { next uninitializedLoaded with env := (4, .int .u8 0x7f) :: uninitializedLoaded.env }
private def poisonedStored : Core :=
  { next poisonedTruncated with mem := pathStored.mem }
private def changedInput : Core :=
  { pathLoaded with env := [(2, .int .u64 0x180)] ++ pathLoaded.env }

/-- An uninitialized source read cannot be widened into a successful return;
the real cast computation preserves its UB. A changed SOURCE value changes
the truncated byte, so the original 0x7f trace no longer applies. -/
theorem source_path_changed_inputs_refuse :
    loadStep 64 uninitializedEntry pathLoad (.int .u8) 1 false none =
      .ok uninitializedLoaded ∧
    castStep 64 uninitializedLoaded pathTrunc .trunc (.int .u64) (.int .u8) 2 =
      .ok poisonedTruncated ∧
    storeStep 64 poisonedTruncated pathStore (.int .u8) 0 4 false none =
      .ok poisonedStored ∧
    castStep 64 poisonedStored pathWide .zext (.int .u8) (.int .u64) 3 =
      .stop (.ub "cast: use of an uninitialized value (poison)") ∧
    castStep 64 changedInput pathTrunc .trunc (.int .u64) (.int .u8) 2 ≠
      .ok pathTruncated ∧
    nth? pathStored.block.body pathStored.pc ≠ some pathReturn := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro impossible
    have atValue := congrArg (fun outcome => match outcome with
      | .ok core => getV core 4
      | .stop _ => .stop (.typeError "refused")) impossible
    cases atValue
  · intro wrongPc
    have opposed : pathWide.inst = pathReturn.inst :=
      congrArg Node.inst (Option.some.inj wrongPc)
    cases opposed

-- IR aliasing control: the load observes the original 0xc3 before the store
-- replaces it by 0x7f. This is an IR computation, not Rust borrowing/ABI
-- permission for the source producer's pointer arguments.
private def aliasCaller : Core :=
  { callerEntry with env := [(0, .ptr 0 1), (1, .ptr 0 1), (2, .int .u64 0x17f)] }
private def aliasEntry : Core :=
  { pathEntry with
    env := [(2, .int .u64 0x17f), (1, .ptr 0 1), (0, .ptr 0 1)],
    stack := [suspend aliasCaller callNode] }
private def aliasLoaded : Core :=
  { next aliasEntry with env := (3, .int .u8 0xc3) :: aliasEntry.env }
private def aliasTruncated : Core :=
  { next aliasLoaded with env := (4, .int .u8 0x7f) :: aliasLoaded.env }
private def aliasStored : Core :=
  { next aliasTruncated with mem := pathStored.mem }
private def aliasWidened : Core :=
  { next aliasStored with env := (5, .int .u64 0xc3) :: aliasStored.env }
private def aliasResumed : Core :=
  { aliasCaller with
    pc := 1, env := (3, .int .u64 0xc3) :: aliasCaller.env, mem := aliasStored.mem }

/-- Aliased source access returns the BEFORE-store byte and updates memory
with the independently truncated source input. It cannot silently reverse the
Load/Store order or select the return value from the native post-memory. -/
theorem source_path_alias_keeps_loaded_value :
    callStep pathModule aliasCaller callNode 0 [0, 1, 2] = .ok aliasEntry ∧
    loadStep 64 aliasEntry pathLoad (.int .u8) 1 false none = .ok aliasLoaded ∧
    castStep 64 aliasLoaded pathTrunc .trunc (.int .u64) (.int .u8) 2 = .ok aliasTruncated ∧
    storeStep 64 aliasTruncated pathStore (.int .u8) 0 4 false none = .ok aliasStored ∧
    castStep 64 aliasStored pathWide .zext (.int .u8) (.int .u64) 3 = .ok aliasWidened ∧
    retStep 64 aliasWidened pathReturn [5] = .ok aliasResumed ∧
    retStep 64 aliasResumed callerReturn [3] = .stop (.ret [.int .u64 0xc3]) ∧
    byteAt (writeBytes initializedAllocation.data 1 [.init 0x7f]) 1 = .init 0x7f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SemR.MemoryEmbedding.FramePair.Checks

#print axioms SemR.MemoryEmbedding.FramePair.wordBytes_extract
#print axioms SemR.MemoryEmbedding.FramePair.extracts_reconstruct
#print axioms SemR.MemoryEmbedding.FramePair.raw_represents_write
#print axioms SemR.MemoryEmbedding.FramePair.raw_reads_word
#print axioms SemR.MemoryEmbedding.FramePair.placed_pair_memory
#print axioms SemR.MemoryEmbedding.FramePair.placed_pair_raw_memory
#print axioms SemR.MemoryEmbedding.FramePair.placed_pair_raw_readback
#print axioms SemR.MemoryEmbedding.FramePair.kept_frame_read
#print axioms SemR.MemoryEmbedding.FramePair.Checks.initialized_pair

#print axioms SemR.MemoryEmbedding.FramePair.Checks.original_b8_module_decodes
#print axioms SemR.MemoryEmbedding.FramePair.Checks.original_b8_source_execution
