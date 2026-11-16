-- Copyright 2026 Andrew Yates | Apache-2.0
import SemRFrameStep

namespace SemR.MemoryEmbedding.FrameCaller

open TrustIr (Memory Allocation AllocId)
open FramePair

/-- Exact machine load expression: every byte select, extension, shift and or.
The bit-vector base is retained, not guessed from a natural-address label. -/
def effectRead64 (raw : RawMemory) (address : Word) : Word :=
  joinWord (raw address) (raw (address + BitVec.ofNat 64 1))
    (raw (address + BitVec.ofNat 64 2)) (raw (address + BitVec.ofNat 64 3))
    (raw (address + BitVec.ofNat 64 4)) (raw (address + BitVec.ofNat 64 5))
    (raw (address + BitVec.ofNat 64 6)) (raw (address + BitVec.ofNat 64 7))

theorem effectRead64_eq (raw : RawMemory) (address : Nat) :
    effectRead64 raw (BitVec.ofNat 64 address) = rawReadWord raw address := by
  simp only [effectRead64, rawReadWord, BitVec.ofNat_add_ofNat]

/-- The real callee post-state remains arbitrary. This full-array equality is
an UNSUPPLIED actual-callee versus observed-model agreement, not a statement
that CER's frame-preserving call model is justified. SP agreement is separate.
No raw pointer/query is required to differ from SP. -/
structure ActualCallAgreement (actual modeled : RawMemory) (actualSp modeledSp : Word) : Prop where
  memory : actual = modeled
  sp : actualSp = modeledSp

/-- Readback for the very Store expression already checked at the save step.
The caller must supply its canonical placement/representation premises. -/
theorem saved_effect_readback {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} (sp fp lr : Word) (raw : RawMemory)
    (input : PlacedFrameInput source memory ids frame sp.toNat 16)
    (size : frame.size = 16) (represented : RawRepresents memory raw) :
    let saved := FrameStep.saveMemoryEffect raw sp fp lr
    effectRead64 saved (sp + BitVec.ofInt 64 (-16)) = fp ∧
    effectRead64 saved ((sp + BitVec.ofInt 64 (-16)) + BitVec.ofNat 64 8) = lr := by
  have saved := FrameStep.save_step sp fp lr raw input size represented
  have finite : frame.base + 16 < 2 ^ 64 := by
    have placement := input.endAtSp
    rw [size] at placement
    have bound := input.finiteSp
    dsimp only [TrustIr.Addr] at *
    omega
  have first := raw_reads_word saved.2.1 frame.base fp (by change frame.base + 8 ≤ 2 ^ 64; exact Nat.le_trans (Nat.add_le_add_left (by decide : 8 ≤ 16) frame.base) (Nat.le_of_lt finite))
    (saveMemory_read_fp memory frame.base fp lr)
  have second := raw_reads_word saved.2.1 (frame.base + 8) lr (by change frame.base + 8 + 8 ≤ 2 ^ 64; simpa only [Nat.add_assoc] using Nat.le_of_lt finite)
    (saveMemory_read_lr memory frame.base fp lr)
  dsimp only
  rw [saved.2.2, BitVec.ofNat_add_ofNat, effectRead64_eq, effectRead64_eq]
  exact ⟨raw_read_exact first, raw_read_exact second⟩

/-- A conditional save/call/restore composition. The before and after source
heaps are independently supplied; no source execution, SourceNoUB, entry ABI,
callee frame rely or actual/model agreement is manufactured by this theorem.

The post-call canonical memory and placement/representation are explicit
transported inputs. `modeledAfter` is precisely the observed CER array that
copies frame stores over its fresh paired post-memory. The unrestricted
`actualAfter` is related only by the undischarged full call agreement. -/
theorem save_call_restore {sourceBefore sourceAfter : Mem}
    {memoryBefore memoryAfter : Memory} {ids : Nat → AllocId} {frame : Allocation}
    (sp fp lr : Word) (rawBefore freshPost actualAfter : RawMemory) (actualSp : Word)
    (beforeInput : PlacedFrameInput sourceBefore memoryBefore ids frame sp.toNat 16)
    (afterInput : PlacedFrameInput sourceAfter memoryAfter ids frame sp.toNat 16)
    (size : frame.size = 16)
    (beforeRep : RawRepresents memoryBefore rawBefore)
    (afterRep : RawRepresents memoryAfter freshPost)
    (call : ActualCallAgreement actualAfter (FrameStep.saveMemoryEffect freshPost sp fp lr)
      actualSp (sp + BitVec.ofInt 64 (-16))) :
    Embeds sourceBefore (saveMemory memoryBefore frame.base fp lr) ids ∧
    Embeds sourceAfter (saveMemory memoryAfter frame.base fp lr) ids ∧
    RawRepresents (saveMemory memoryAfter frame.base fp lr) actualAfter ∧
    effectRead64 actualAfter actualSp = fp ∧
    effectRead64 actualAfter (actualSp + BitVec.ofNat 64 8) = lr ∧
    actualSp + BitVec.ofNat 64 16 = sp := by
  have before := FrameStep.save_step sp fp lr rawBefore beforeInput size beforeRep
  have after := FrameStep.save_step sp fp lr freshPost afterInput size afterRep
  have reads := saved_effect_readback sp fp lr freshPost afterInput size afterRep
  refine ⟨before.1, after.1, ?_, ?_, ?_, ?_⟩
  · rw [call.memory]
    exact after.2.1
  · rw [call.memory, call.sp]
    exact reads.1
  · rw [call.memory, call.sp]
    exact reads.2
  · rw [call.sp, after.2.2]
    apply BitVec.eq_of_toNat_eq
    exact post_index_sp afterInput size

/-- A real byte write to saved LR that changes its low byte falsifies the
full actual/model call agreement. No pointer/frame-disjoint assumption is used. -/
theorem overwritten_lr_refuses_agreement {source : Mem} {memory : Memory}
    {ids : Nat → AllocId} {frame : Allocation} (sp fp lr : Word) (raw : RawMemory)
    (input : PlacedFrameInput source memory ids frame sp.toNat 16)
    (size : frame.size = 16) (represented : RawRepresents memory raw)
    (byte : BitVec 8) (different : byte ≠ lr.extractLsb' 0 8) :
    let saved := FrameStep.saveMemoryEffect raw sp fp lr
    let address := (sp + BitVec.ofInt 64 (-16)) + BitVec.ofNat 64 8
    ¬ ActualCallAgreement (FrameStep.arrayStore saved address byte) saved
        (sp + BitVec.ofInt 64 (-16)) (sp + BitVec.ofInt 64 (-16)) := by
  dsimp only
  intro agreement
  have saved := FrameStep.save_step sp fp lr raw input size represented
  have finite : frame.base + 8 + 8 ≤ addrSpace := by
    have placement := input.endAtSp
    rw [size] at placement
    have bound := input.finiteSp
    dsimp only [TrustIr.Addr, addrSpace] at *
    omega
  have read := raw_reads_word saved.2.1 (frame.base + 8) lr finite
    (saveMemory_read_lr memory frame.base fp lr) 0 (by decide)
  simp only [Nat.add_zero, Nat.mul_zero] at read
  have value := congrArg
    (fun memory => memory ((sp + BitVec.ofInt 64 (-16)) + BitVec.ofNat 64 8))
    agreement.memory
  simp only [FrameStep.arrayStore, ↓reduceIte] at value
  rw [saved.2.2, BitVec.ofNat_add_ofNat, read] at value
  exact different value

/-- The one-byte destination is separate from each actual saved frame address.
This is an explicit obligation: scalar register placement does not establish it,
and a raw destination may alias saved LR without a source/entry-memory proof. -/
def SeparateFrameStore (sp destination : Word) : Prop :=
  ∀ index : Nat, index < 16 →
    destination ≠ (sp + BitVec.ofInt 64 (-16)) + BitVec.ofNat 64 index

/-- Derive separation from the checked source allocation and its actual
canonical address. No arbitrary raw destination is assumed disjoint, and no
query is excluded. This supplies separation, not source execution or NoUB. -/
theorem source_store_separate {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} (sp : Word)
    (input : PlacedFrameInput source memory ids frame sp.toNat 16)
    (size : frame.size = 16) (index : Nat) (allocation : Alloc) (record : Allocation)
    (present : nth? source.allocs index = some allocation)
    (found : memory.lookup (ids index) = some record)
    (offset : Nat) (inBounds : offset + 1 ≤ allocation.size) :
    SeparateFrameStore sp (BitVec.ofNat 64 (record.base + offset)) := by
  have apart := input.toFrameRecordInput.source_access_apart
    index allocation record present found offset 1 inBounds
  obtain ⟨original, originalFound, related⟩ := input.embedding.records index allocation present
  have same : original = record := by
    rw [found] at originalFound
    exact (Option.some.inj originalFound).symm
  subst original
  have sourceBound : record.base + offset < 2 ^ 64 := by
    have finite := related.finite
    have sameSize := related.size
    change record.base + record.size ≤ 2 ^ 64 at finite
    dsimp only [TrustIr.Addr] at *
    omega
  have frameBound : frame.base < 2 ^ 64 := by
    have placement := input.endAtSp
    have finite := input.finiteSp
    rw [size] at placement
    change sp.toNat < 2 ^ 64 at finite
    dsimp only [TrustIr.Addr] at *
    omega
  have base : sp + BitVec.ofInt 64 (-16) = BitVec.ofNat 64 frame.base := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt frameBound]
    simpa only [BitVec.ofNat_toNat] using pre_index_effect_address input size
  intro byte inside equal
  have address := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBound, base,
    transfer_address input size byte inside] at address
  dsimp only [TrustIr.Addr] at *
  rcases apart with before | after
  · omega
  · rw [size] at after
    omega

theorem arrayStore_commute (raw : RawMemory) (address destination : Word)
    (value byte : BitVec 8) (separate : destination ≠ address) :
    FrameStep.arrayStore (FrameStep.arrayStore raw address value) destination byte =
      FrameStep.arrayStore (FrameStep.arrayStore raw destination byte) address value := by
  funext query
  by_cases atDestination : query = destination
  · subst query
    simp [FrameStep.arrayStore, separate]
  · by_cases atAddress : query = address
    · subst query
      simp [FrameStep.arrayStore, Ne.symm separate]
    · simp [FrameStep.arrayStore, atDestination, atAddress]

theorem effectStoreBytes_commute (raw : RawMemory) (base destination : Word)
    (offset : Nat) (bytes : List (BitVec 8)) (byte : BitVec 8)
    (separate : ∀ index : Nat, offset ≤ index → index < offset + bytes.length →
      destination ≠ base + BitVec.ofNat 64 index) :
    FrameStep.arrayStore (FrameStep.effectStoreBytes raw base offset bytes) destination byte =
      FrameStep.effectStoreBytes (FrameStep.arrayStore raw destination byte) base offset bytes := by
  induction bytes generalizing raw offset with
  | nil => rfl
  | cons value rest induction =>
    have current : destination ≠
        (if offset = 0 then base else base + BitVec.ofNat 64 offset) := by
      have different := separate offset (Nat.le_refl _) (by simp)
      by_cases zero : offset = 0
      · simpa [zero] using different
      · simpa [zero] using different
    have tail : ∀ index : Nat, offset + 1 ≤ index →
        index < offset + 1 + rest.length → destination ≠ base + BitVec.ofNat 64 index := by
      intro index lower upper
      apply separate index (by omega)
      simp only [List.length_cons]
      omega
    simp only [FrameStep.effectStoreBytes_cons]
    rw [induction _ (offset + 1) tail, arrayStore_commute _ _ _ _ _ current]

/-- Move the actual separate byte store through all sixteen save Store nodes.
Every other raw-memory byte is retained; this is full function-array equality,
not merely agreement on a sampled frame address or an invented fresh array. -/
theorem separate_store_save_commutes (raw : RawMemory) (sp fp lr destination : Word)
    (byte : BitVec 8) (separate : SeparateFrameStore sp destination) :
    FrameStep.arrayStore (FrameStep.saveMemoryEffect raw sp fp lr) destination byte =
      FrameStep.saveMemoryEffect (FrameStep.arrayStore raw destination byte) sp fp lr := by
  let base := sp + BitVec.ofInt 64 (-16)
  have first : ∀ index : Nat, 0 ≤ index →
      index < 0 + (FrameStep.extractedBytes fp).length →
      destination ≠ base + BitVec.ofNat 64 index := by
    intro index _ inside
    change index < 8 at inside
    exact separate index (by omega)
  have second : ∀ index : Nat, 0 ≤ index →
      index < 0 + (FrameStep.extractedBytes lr).length →
      destination ≠ (base + BitVec.ofNat 64 8) + BitVec.ofNat 64 index := by
    intro index _ inside
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change index < 8 at inside
    exact separate (8 + index) (by omega)
  unfold FrameStep.saveMemoryEffect FrameStep.effectStore64
  rw [effectStoreBytes_commute _ _ _ _ _ _ second,
    effectStoreBytes_commute _ _ _ _ _ _ first]

/-- The callee's exact data-effect post-memory now supplies the full agreement
premise, conditional only on the explicit destination/frame separation. The
SPs are the actual unchanged data-effect expression, not a fresh post-state.
This does not prove source NoUB, entry ABI, separation, physical instruction
fetch or that an external execution follows this checked data-effect envelope. -/
theorem separate_store_agreement (raw : RawMemory) (sp fp lr destination : Word)
    (byte : BitVec 8) (separate : SeparateFrameStore sp destination) :
    ActualCallAgreement
      (FrameStep.arrayStore (FrameStep.saveMemoryEffect raw sp fp lr) destination byte)
      (FrameStep.saveMemoryEffect (FrameStep.arrayStore raw destination byte) sp fp lr)
      (sp + BitVec.ofInt 64 (-16)) (sp + BitVec.ofInt 64 (-16)) :=
  ⟨separate_store_save_commutes raw sp fp lr destination byte separate, rfl⟩

/-- The full-array commuting square with separation discharged by the source
allocation image. Actual source-step/value correspondence, entry custody and
machine execution are still distinct required inputs. The result compares
the native save/store array with the frame-lifted source store, never with the
bare source array or with an array chosen after observing the native exit. -/
theorem source_store_agreement {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} (raw : RawMemory) (sp fp lr : Word)
    (input : PlacedFrameInput source memory ids frame sp.toNat 16)
    (size : frame.size = 16) (index : Nat) (allocation : Alloc) (record : Allocation)
    (present : nth? source.allocs index = some allocation)
    (found : memory.lookup (ids index) = some record)
    (offset : Nat) (inBounds : offset + 1 ≤ allocation.size) (byte : BitVec 8) :
    ActualCallAgreement
      (FrameStep.arrayStore (FrameStep.saveMemoryEffect raw sp fp lr)
        (BitVec.ofNat 64 (record.base + offset)) byte)
      (FrameStep.saveMemoryEffect
        (FrameStep.arrayStore raw (BitVec.ofNat 64 (record.base + offset)) byte) sp fp lr)
      (sp + BitVec.ofInt 64 (-16)) (sp + BitVec.ofInt 64 (-16)) :=
  separate_store_agreement raw sp fp lr _ byte
    (source_store_separate sp input size index allocation record present found offset inBounds)

/-- The retained saved-LR alias counterexample cannot satisfy separation. -/
theorem saved_lr_not_separate (sp : Word) :
    ¬ SeparateFrameStore sp ((sp + BitVec.ofInt 64 (-16)) + BitVec.ofNat 64 8) := by
  intro separate
  exact separate 8 (by decide) rfl

/-- One ACTUAL source U8 Store owns this exact raw data-effect fold from the
fixed initial array. The result does not select an arbitrary raw completion
of the terminal heap. Entry custody, PointerImage/ABI, source quotation,
terminal Reaches, SourceNoUB and original Rust refinement remain separate. -/
theorem source_u8_store_raw {memory : Memory} {ids : Nat → AllocId}
    (module : Module) (before after : Core) (ptr value index offset : Nat)
    (allocation : Alloc) (record : Allocation) (byte : UInt8) (initialR0 : RawMemory)
    (fetched : nth? before.block.body before.pc =
      some { inst := .store (.int .u8) ptr value false none, results := [] })
    (pointer : getV before ptr = .ok (.ptr index offset))
    (stored : getV before value = .ok (.int .u8 byte.toNat))
    (present : nth? before.mem.allocs index = some allocation)
    (executed : storeStep module.pointerBits before
      { inst := .store (.int .u8) ptr value false none, results := [] }
      (.int .u8) ptr value false none = .ok after)
    (embedding : Embeds before.mem memory ids)
    (found : memory.lookup (ids index) = some record)
    (live : allocation.live = true) (inside : offset + 1 ≤ allocation.size)
    (represented : RawRepresents memory initialR0) :
    let canonicalAfter := memory.writeBytes (record.base + offset) [byte]
    let sourceDataExit := FrameStep.arrayStore initialR0
      (BitVec.ofNat 64 (record.base + offset)) (FrameStep.byteBits byte)
    Step module before (.cont after) ∧
    Embeds after.mem canonicalAfter ids ∧
    RawRepresents canonicalAfter sourceDataExit := by
  have core := storeStep_u8_core rfl pointer stored present executed
  have step := step_u8_of_storeStep module before after ptr value fetched executed
  have embedded := embedding.written_u8 index offset allocation record present found live inside byte
  obtain ⟨original, originalFound, related⟩ := embedding.records index allocation present
  have same : original = record := by
    rw [found] at originalFound
    exact (Option.some.inj originalFound).symm
  subst original
  have finite : record.base + offset + [byte].length ≤ addrSpace := by
    have bound := related.finite
    have size := related.size
    change record.base + record.size ≤ addrSpace at bound
    simp only [List.length_cons, List.length_nil]
    dsimp only [TrustIr.Addr] at *
    omega
  refine ⟨step, ?_, ?_⟩
  · rw [core]
    exact embedded
  · change RawRepresents (memory.writeBytes (record.base + offset) [byte])
      (rawWriteBytes initialR0 (record.base + offset) [byte])
    exact raw_represents_write represented (record.base + offset) [byte] finite

/-- Derive the source Store, fetched transition and raw-array result from
typed operands and source allocation bounds. No successful source Store is
assumed. The unchanged embedding still supplies actual allocation identity;
Rust refinement, entry ABI and physical native execution remain separate. -/
theorem source_u8_store_derived_raw {memory : Memory} {ids : Nat → AllocId}
    (module : Module) (before : Core) (ptr value index offset : Nat)
    (allocation : Alloc) (record : Allocation) (byte : UInt8) (initialR0 : RawMemory)
    (fetched : nth? before.block.body before.pc =
      some { inst := .store (.int .u8) ptr value false none, results := [] })
    (pointer : getV before ptr = .ok (.ptr index offset))
    (stored : getV before value = .ok (.int .u8 byte.toNat))
    (present : nth? before.mem.allocs index = some allocation)
    (embedding : Embeds before.mem memory ids)
    (found : memory.lookup (ids index) = some record)
    (live : allocation.live = true)
    (finite : allocation.base + allocation.size < addrSpace)
    (inside : offset + 1 ≤ allocation.size)
    (represented : RawRepresents memory initialR0) :
    let after := { next before with
      mem := written before.mem index offset allocation [.init byte.toNat] }
    let canonicalAfter := memory.writeBytes (record.base + offset) [byte]
    let sourceDataExit := FrameStep.arrayStore initialR0
      (BitVec.ofNat 64 (record.base + offset)) (FrameStep.byteBits byte)
    Step module before (.cont after) ∧
    Embeds after.mem canonicalAfter ids ∧
    RawRepresents canonicalAfter sourceDataExit :=
  source_u8_store_raw module before _ ptr value index offset allocation record byte initialR0
    fetched pointer stored present
    (storeStep_u8 module.pointerBits before ptr value index offset allocation byte
      pointer stored present live finite inside)
    embedding found live inside represented

/-- A fetched byte load executes from its live source allocation and initialized
byte, and returns the same byte selected from the represented raw array. The
source and target allocation bases may differ. Neither successful execution nor
the raw value is a premise; both follow from the checked source state and the
whole-allocation embedding. This supplies no Rust or native-entry authority. -/
theorem source_u8_load_derived_raw {memory : Memory} {ids : Nat → AllocId}
    (module : Module) (before : Core) (ptr result index offset : Nat)
    (allocation : Alloc) (record : Allocation) (byte : UInt8) (raw : RawMemory)
    (volatile : Bool)
    (fetched : nth? before.block.body before.pc =
      some { inst := .load (.int .u8) ptr volatile none, results := [result] })
    (pointer : getV before ptr = .ok (.ptr index offset))
    (present : nth? before.mem.allocs index = some allocation)
    (embedding : Embeds before.mem memory ids)
    (found : memory.lookup (ids index) = some record)
    (live : allocation.live = true)
    (finite : allocation.base + allocation.size < addrSpace)
    (inside : offset + 1 ≤ allocation.size)
    (initialized : byteAt allocation.data offset = .init byte.toNat)
    (represented : RawRepresents memory raw) :
    let after := { next before with env := (result, .int .u8 byte.toNat) :: before.env }
    Step module before (.cont after) ∧
    getV after result = .ok (.int .u8 byte.toNat) ∧
    Embeds after.mem memory ids ∧ RawRepresents memory raw ∧
    raw (BitVec.ofNat 64 (record.base + offset)) = FrameStep.byteBits byte := by
  have executed := loadStep_u8 module.pointerBits before ptr result index offset allocation byte
    volatile pointer present live finite inside initialized
  have stepped : Step module before (.cont
      { next before with env := (result, .int .u8 byte.toNat) :: before.env }) := by
    have actual := step_complete module before
    simpa only [stepCore, fetched, execNode, executed, ofR] using actual
  have related := embedding.bytes index allocation record present found live offset (by omega)
  rw [initialized] at related
  have targetByte : memory.bytes (record.base + offset) = some byte := by
    cases image : memory.bytes (record.base + offset) with
    | none => simp [image, ByteImage] at related
    | some actual =>
      simp only [image, ByteImage] at related
      have equal : actual = byte := UInt8.toNat_inj.mp related.symm
      simp [equal]
  obtain ⟨other, otherFound, allocationImage⟩ := embedding.records index allocation present
  have same : other = record := by
    rw [found] at otherFound
    exact (Option.some.inj otherFound).symm
  subst other
  have targetInside : record.base + offset < addrSpace := by
    have size := allocationImage.size
    have bound := allocationImage.finite
    dsimp only [TrustIr.Addr] at *
    omega
  refine ⟨stepped, ?_, embedding, represented, ?_⟩
  · simp [getV, lookupEnv]
  · exact represented _ byte targetInside targetByte

/-- The complete source Load/U64-to-U8/Store/U8-to-U64/Return path owns its
raw data effect. Each node is fetched from the actual source Core and every
transition uses the existing SemR operation. The destination and byte are
read from the source SSA state after truncation, never from a native trace.

The actual return outcome is retained, including a caller continuation or a
refusal: a successful return/SourceNoUB and source quotation/Rust refinement,
entry/cell/PointerImage/ABI custody remain separate required inputs. -/
theorem source_u8_load_store_path {memory : Memory} {ids : Nat → AllocId}
    (module : Module) (entry loaded truncated stored widened : Core)
    (destinationPtr sourcePtr input loadResult truncResult wideResult : Nat)
    (loadIndex loadOffset index offset : Nat) (loadAllocation allocation : Alloc)
    (record : Allocation) (byte : UInt8) (initialR0 : RawMemory) (returnOutcome : R Core)
    (loadFetched : nth? entry.block.body entry.pc =
      some { inst := .load (.int .u8) sourcePtr false none, results := [loadResult] })
    (loadPointer : getV entry sourcePtr = .ok (.ptr loadIndex loadOffset))
    (loadPresent : nth? entry.mem.allocs loadIndex = some loadAllocation)
    (loadExecuted : loadStep module.pointerBits entry
      { inst := .load (.int .u8) sourcePtr false none, results := [loadResult] }
      (.int .u8) sourcePtr false none = .ok loaded)
    (truncFetched : nth? loaded.block.body loaded.pc =
      some { inst := .cast .trunc (.int .u64) (.int .u8) input, results := [truncResult] })
    (truncExecuted : castStep module.pointerBits loaded
      { inst := .cast .trunc (.int .u64) (.int .u8) input, results := [truncResult] }
      .trunc (.int .u64) (.int .u8) input = .ok truncated)
    (storeFetched : nth? truncated.block.body truncated.pc =
      some { inst := .store (.int .u8) destinationPtr truncResult false none, results := [] })
    (storePointer : getV truncated destinationPtr = .ok (.ptr index offset))
    (sourceByte : getV truncated truncResult = .ok (.int .u8 byte.toNat))
    (present : nth? entry.mem.allocs index = some allocation)
    (storeExecuted : storeStep module.pointerBits truncated
      { inst := .store (.int .u8) destinationPtr truncResult false none, results := [] }
      (.int .u8) destinationPtr truncResult false none = .ok stored)
    (wideFetched : nth? stored.block.body stored.pc =
      some { inst := .cast .zext (.int .u8) (.int .u64) loadResult, results := [wideResult] })
    (wideExecuted : castStep module.pointerBits stored
      { inst := .cast .zext (.int .u8) (.int .u64) loadResult, results := [wideResult] }
      .zext (.int .u8) (.int .u64) loadResult = .ok widened)
    (returnFetched : nth? widened.block.body widened.pc =
      some { inst := .ret [wideResult], results := [] })
    (returnExecuted : retStep module.pointerBits widened
      { inst := .ret [wideResult], results := [] } [wideResult] = returnOutcome)
    (embedding : Embeds entry.mem memory ids)
    (found : memory.lookup (ids index) = some record)
    (live : allocation.live = true) (inside : offset + 1 ≤ allocation.size)
    (represented : RawRepresents memory initialR0) :
    let canonicalAfter := memory.writeBytes (record.base + offset) [byte]
    let sourceDataExit := FrameStep.arrayStore initialR0
      (BitVec.ofNat 64 (record.base + offset)) (FrameStep.byteBits byte)
    Reaches module entry widened ∧ Step module widened (ofR returnOutcome) ∧
    widened.mem = written entry.mem index offset allocation [.init byte.toNat] ∧
    widened.cells = entry.cells ∧ widened.nextCell = entry.nextCell ∧
    widened.stack = entry.stack ∧ widened.openFrames = entry.openFrames ∧
    widened.nextFrame = entry.nextFrame ∧
    Embeds widened.mem canonicalAfter ids ∧ RawRepresents canonicalAfter sourceDataExit ∧
    (∀ resumed, returnOutcome = .ok resumed →
      resumed.mem = widened.mem ∧ resumed.cells = entry.cells ∧
      resumed.nextCell = entry.nextCell ∧ resumed.openFrames = entry.openFrames ∧
      resumed.nextFrame = entry.nextFrame) := by
  obtain ⟨loadValue, loadCore⟩ := loadStep_u8_core loadPointer loadPresent loadExecuted
  obtain ⟨truncValue, truncCore⟩ := castStep_core truncExecuted
  obtain ⟨wideValue, wideCore⟩ := castStep_core wideExecuted
  have unchanged : truncated.mem = entry.mem := by simp only [truncCore, loadCore, next]
  have actualPresent : nth? truncated.mem.allocs index = some allocation := by
    rw [unchanged]
    exact present
  have storeCore := storeStep_u8_core rfl storePointer sourceByte actualPresent storeExecuted
  have data := source_u8_store_raw module truncated stored destinationPtr truncResult index offset
    allocation record byte initialR0 storeFetched storePointer sourceByte actualPresent storeExecuted
    (by rw [unchanged]; exact embedding) found live inside represented
  have loadedStep : Step module entry (.cont loaded) := by
    have actual := step_complete module entry
    simpa only [stepCore, loadFetched, execNode, loadExecuted, ofR] using actual
  have truncatedStep : Step module loaded (.cont truncated) := by
    have actual := step_complete module loaded
    simpa only [stepCore, truncFetched, execNode, truncExecuted, ofR] using actual
  have widenedStep : Step module stored (.cont widened) := by
    have actual := step_complete module stored
    simpa only [stepCore, wideFetched, execNode, wideExecuted, ofR] using actual
  have returnedStep : Step module widened (ofR returnOutcome) := by
    have actual := step_complete module widened
    simpa only [stepCore, returnFetched, execNode, returnExecuted] using actual
  have finalMemory : widened.mem = written entry.mem index offset allocation [.init byte.toNat] := by
    simp only [wideCore, storeCore, next, unchanged]
  have finalData : widened.cells = entry.cells ∧ widened.nextCell = entry.nextCell ∧
      widened.stack = entry.stack ∧ widened.openFrames = entry.openFrames ∧
      widened.nextFrame = entry.nextFrame := by
    simp only [wideCore, storeCore, truncCore, loadCore, next, and_self]
  refine ⟨Reaches.step _ _ _ loadedStep (Reaches.step _ _ _ truncatedStep
    (Reaches.step _ _ _ data.1 (Reaches.step _ _ _ widenedStep (Reaches.refl _)))),
    returnedStep, finalMemory, finalData.1, finalData.2.1, finalData.2.2.1,
    finalData.2.2.2.1, finalData.2.2.2.2, ?_, data.2.2, ?_⟩
  · simpa only [wideCore, next] using data.2.1
  · intro resumed resumedByReturn
    have successful : retStep module.pointerBits widened
        { inst := .ret [wideResult], results := [] } [wideResult] = .ok resumed :=
      returnExecuted.trans resumedByReturn
    have preserved := retStep_preserves_data successful
    exact ⟨preserved.1, preserved.2.1.trans finalData.1,
      preserved.2.2.1.trans finalData.2.1,
      preserved.2.2.2.1.trans finalData.2.2.2.1,
      preserved.2.2.2.2.trans finalData.2.2.2.2⟩

/-- Derive the complete load/truncate/store/widen path from entry SSA values,
live finite allocations and the actual fetched source nodes. No successful
load, cast, store or return equation is a premise. The four freshness checks
retain the original input/pointer and the loaded byte across SSA publication;
the source and destination allocations may alias. Return keeps its actual
outcome, including a continuation or refusal, rather than assuming SourceNoUB.
Rust quotation/refinement and physical native entry/execution remain separate. -/
theorem source_u8_load_store_derived_raw {memory : Memory} {ids : Nat → AllocId}
    (module : Module) (entry : Core)
    (destinationPtr sourcePtr input loadResult truncResult wideResult : Nat)
    (loadIndex loadOffset index offset : Nat) (loadAllocation allocation : Alloc)
    (record : Allocation) (loadedByte : UInt8) (value : UInt64) (raw : RawMemory)
    (loadFetched : nth? entry.block.body entry.pc =
      some { inst := .load (.int .u8) sourcePtr false none, results := [loadResult] })
    (truncFetched : nth? entry.block.body (entry.pc + 1) =
      some { inst := .cast .trunc (.int .u64) (.int .u8) input, results := [truncResult] })
    (storeFetched : nth? entry.block.body (entry.pc + 2) =
      some { inst := .store (.int .u8) destinationPtr truncResult false none, results := [] })
    (wideFetched : nth? entry.block.body (entry.pc + 3) =
      some { inst := .cast .zext (.int .u8) (.int .u64) loadResult, results := [wideResult] })
    (returnFetched : nth? entry.block.body (entry.pc + 4) =
      some { inst := .ret [wideResult], results := [] })
    (loadPointer : getV entry sourcePtr = .ok (.ptr loadIndex loadOffset))
    (storePointer : getV entry destinationPtr = .ok (.ptr index offset))
    (operand : getV entry input = .ok (.int .u64 value.toNat))
    (freshInput : loadResult ≠ input)
    (freshPointer : loadResult ≠ destinationPtr)
    (freshStore : truncResult ≠ destinationPtr)
    (freshLoaded : truncResult ≠ loadResult)
    (loadPresent : nth? entry.mem.allocs loadIndex = some loadAllocation)
    (loadLive : loadAllocation.live = true)
    (loadFinite : loadAllocation.base + loadAllocation.size < addrSpace)
    (loadInside : loadOffset + 1 ≤ loadAllocation.size)
    (initialized : byteAt loadAllocation.data loadOffset = .init loadedByte.toNat)
    (present : nth? entry.mem.allocs index = some allocation)
    (live : allocation.live = true)
    (finite : allocation.base + allocation.size < addrSpace)
    (inside : offset + 1 ≤ allocation.size)
    (embedding : Embeds entry.mem memory ids)
    (found : memory.lookup (ids index) = some record)
    (represented : RawRepresents memory raw) :
    let byte := UInt8.ofNat value.toNat
    ∃ widened : Core,
      Reaches module entry widened ∧
      Step module widened (ofR (retStep module.pointerBits widened
        { inst := .ret [wideResult], results := [] } [wideResult])) ∧
      getV widened wideResult = .ok (.int .u64 loadedByte.toNat) ∧
      widened.mem = written entry.mem index offset allocation [.init byte.toNat] ∧
      widened.cells = entry.cells ∧ widened.nextCell = entry.nextCell ∧
      widened.stack = entry.stack ∧ widened.openFrames = entry.openFrames ∧
      widened.nextFrame = entry.nextFrame ∧
      Embeds widened.mem (memory.writeBytes (record.base + offset) [byte]) ids ∧
      RawRepresents (memory.writeBytes (record.base + offset) [byte])
        (FrameStep.arrayStore raw (BitVec.ofNat 64 (record.base + offset))
          (FrameStep.byteBits byte)) := by
  let byte := UInt8.ofNat value.toNat
  let loaded := { next entry with env := (loadResult, .int .u8 loadedByte.toNat) :: entry.env }
  let truncated := { next loaded with env := (truncResult, .int .u8 byte.toNat) :: loaded.env }
  let stored := { next truncated with
    mem := written entry.mem index offset allocation [.init byte.toNat] }
  let widened := { next stored with env := (wideResult, .int .u64 loadedByte.toNat) :: stored.env }
  have loadExecuted : loadStep module.pointerBits entry
      { inst := .load (.int .u8) sourcePtr false none, results := [loadResult] }
      (.int .u8) sourcePtr false none = .ok loaded :=
    loadStep_u8 module.pointerBits entry sourcePtr loadResult loadIndex loadOffset
      loadAllocation loadedByte false loadPointer loadPresent loadLive loadFinite loadInside initialized
  have inputLoaded : getV loaded input = .ok (.int .u64 value.toNat) := by
    simpa [loaded, next, getV, lookupEnv, freshInput] using operand
  have truncExecuted := castStep_trunc_u64_u8 module.pointerBits loaded input truncResult value inputLoaded
  have destination : getV truncated destinationPtr = .ok (.ptr index offset) := by
    simpa [truncated, loaded, next, getV, lookupEnv, freshStore, freshPointer] using storePointer
  have sourceByte : getV truncated truncResult = .ok (.int .u8 byte.toNat) := by
    simp [truncated, getV, lookupEnv]
  have storeExecuted : storeStep module.pointerBits truncated
      { inst := .store (.int .u8) destinationPtr truncResult false none, results := [] }
      (.int .u8) destinationPtr truncResult false none = .ok stored :=
    storeStep_u8 module.pointerBits truncated destinationPtr truncResult index offset allocation byte
      destination sourceByte present live finite inside
  have sourceLoaded : getV stored loadResult = .ok (.int .u8 loadedByte.toNat) := by
    simp [stored, truncated, loaded, next, getV, lookupEnv, freshLoaded]
  have wideExecuted := castStep_zext_u8_u64 module.pointerBits stored loadResult wideResult loadedByte sourceLoaded
  have path := source_u8_load_store_path module entry loaded truncated stored widened
    destinationPtr sourcePtr input loadResult truncResult wideResult
    loadIndex loadOffset index offset loadAllocation allocation record byte raw
    (retStep module.pointerBits widened { inst := .ret [wideResult], results := [] } [wideResult])
    loadFetched loadPointer loadPresent loadExecuted
    (by simpa [loaded, next] using truncFetched) truncExecuted
    (by simpa [truncated, loaded, next, Nat.add_assoc] using storeFetched)
    destination sourceByte present storeExecuted
    (by simpa [stored, truncated, loaded, next, Nat.add_assoc] using wideFetched) wideExecuted
    (by simpa [widened, stored, truncated, loaded, next, Nat.add_assoc] using returnFetched)
    rfl embedding found live inside represented
  refine ⟨widened, path.1, path.2.1, ?_, path.2.2.1, path.2.2.2.1,
    path.2.2.2.2.1, path.2.2.2.2.2.1, path.2.2.2.2.2.2.1,
    path.2.2.2.2.2.2.2.1, path.2.2.2.2.2.2.2.2.1, path.2.2.2.2.2.2.2.2.2.1⟩
  simp [widened, getV, lookupEnv]

end SemR.MemoryEmbedding.FrameCaller

#print axioms SemR.MemoryEmbedding.FrameCaller.save_call_restore

#print axioms SemR.MemoryEmbedding.FrameCaller.effectRead64_eq
#print axioms SemR.MemoryEmbedding.FrameCaller.saved_effect_readback
#print axioms SemR.MemoryEmbedding.FrameCaller.overwritten_lr_refuses_agreement
#print axioms SemR.MemoryEmbedding.FrameCaller.separate_store_agreement
#print axioms SemR.MemoryEmbedding.FrameCaller.source_store_separate
#print axioms SemR.MemoryEmbedding.FrameCaller.source_store_agreement
#print axioms SemR.MemoryEmbedding.FrameCaller.saved_lr_not_separate
