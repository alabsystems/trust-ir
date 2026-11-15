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

/-- The retained saved-LR alias counterexample cannot satisfy separation. -/
theorem saved_lr_not_separate (sp : Word) :
    ¬ SeparateFrameStore sp ((sp + BitVec.ofInt 64 (-16)) + BitVec.ofNat 64 8) := by
  intro separate
  exact separate 8 (by decide) rfl

end SemR.MemoryEmbedding.FrameCaller

#print axioms SemR.MemoryEmbedding.FrameCaller.save_call_restore

#print axioms SemR.MemoryEmbedding.FrameCaller.effectRead64_eq
#print axioms SemR.MemoryEmbedding.FrameCaller.saved_effect_readback
#print axioms SemR.MemoryEmbedding.FrameCaller.overwritten_lr_refuses_agreement
#print axioms SemR.MemoryEmbedding.FrameCaller.separate_store_agreement
#print axioms SemR.MemoryEmbedding.FrameCaller.saved_lr_not_separate
