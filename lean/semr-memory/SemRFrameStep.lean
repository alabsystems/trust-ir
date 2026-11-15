-- Copyright 2026 Andrew Yates | Apache-2.0
import SemRFramePair

namespace SemR.MemoryEmbedding.FrameStep

open TrustIr (Memory Allocation AllocId)
open FramePair

/-- The exact function update denoted by an SMT byte-array Store. -/
def arrayStore (memory : RawMemory) (address : Word) (value : BitVec 8) : RawMemory :=
  fun query => if query = address then value else memory query

def byteBits (value : UInt8) : BitVec 8 := BitVec.ofNat 8 value.toNat

/-- Preserve the actual base-plus-byte-offset address spelling. -/
def effectStoreBytes (memory : RawMemory) (base : Word) (offset : Nat)
    (bytes : List (BitVec 8)) : RawMemory :=
  (bytes.foldl (fun (state : RawMemory × Nat) byte =>
    let address := if state.2 = 0 then base else base + BitVec.ofNat 64 state.2
    (arrayStore state.1 address byte, state.2 + 1)) (memory,offset)).1

@[simp] theorem effectStoreBytes_nil (memory : RawMemory) (base : Word) (offset : Nat) :
    effectStoreBytes memory base offset [] = memory := rfl

/-- The fold retains the exact conditional address and sequential-store equation. -/
theorem effectStoreBytes_cons (memory : RawMemory) (base : Word) (offset : Nat)
    (byte : BitVec 8) (rest : List (BitVec 8)) :
    effectStoreBytes memory base offset (byte :: rest) =
      effectStoreBytes (arrayStore memory (if offset = 0 then base else base + BitVec.ofNat 64 offset) byte)
        base (offset + 1) rest := rfl

def extractedBytes (value : Word) : List (BitVec 8) :=
  [value.extractLsb' 0 8, value.extractLsb' 8 8,
   value.extractLsb' 16 8, value.extractLsb' 24 8,
   value.extractLsb' 32 8, value.extractLsb' 40 8,
   value.extractLsb' 48 8, value.extractLsb' 56 8]

theorem extractedBytes_eq (value : Word) :
    extractedBytes value = (wordBytes value).map byteBits := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < 8
  · have byte := wordBytes_extract value index inside
    have mapped := congrArg (Option.map (BitVec.ofNat 8)) byte
    have converted : ((wordBytes value).map byteBits)[index]? =
        some (value.extractLsb' (8 * index) 8) := by
      rw [List.getElem?_map]
      simpa only [Option.map_map, Function.comp_def, Option.map_some,
        BitVec.ofNat_toNat] using mapped
    have positions : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 := by omega
    rcases positions with h | h | h | h | h | h | h | h
    all_goals
      subst index
      simpa only [extractedBytes, List.getElem?_cons_zero, List.getElem?_cons_succ] using converted.symm
  · have length : ((wordBytes value).map byteBits).length = 8 := by simp [wordBytes_length]
    have other : (extractedBytes value).length = 8 := rfl
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem effectStoreBytes_eq (memory : RawMemory) (base offset : Nat) (bytes : List UInt8) :
    effectStoreBytes memory (BitVec.ofNat 64 base) offset (bytes.map byteBits) =
      rawWriteBytes memory (base + offset) bytes := by
  induction bytes generalizing memory offset with
  | nil => rfl
  | cons byte rest induction =>
    have address : (if offset = 0 then BitVec.ofNat 64 base else
        BitVec.ofNat 64 base + BitVec.ofNat 64 offset) = BitVec.ofNat 64 (base + offset) := by
      by_cases zero : offset = 0
      · simp [zero]
      · simp [zero, BitVec.ofNat_add_ofNat]
    simp only [List.map_cons, effectStoreBytes_cons, address, rawWriteBytes_cons]
    change effectStoreBytes (rawStore memory (BitVec.ofNat 64 (base + offset)) byte)
      (BitVec.ofNat 64 base) (offset + 1) (rest.map byteBits) = _
    simpa only [Nat.add_assoc] using
      induction (rawStore memory (BitVec.ofNat 64 (base + offset)) byte) (offset + 1)

/-- Exactly the eight low-byte extracts and Store nodes of a canonical
MachineState MemWrite application, not a normalized or opaque memory summary. -/
def effectStore64 (memory : RawMemory) (address value : Word) : RawMemory :=
  effectStoreBytes memory address 0 (extractedBytes value)

theorem effectStore64_eq (memory : RawMemory) (address : Nat) (value : Word) :
    effectStore64 memory (BitVec.ofNat 64 address) value =
      rawWriteBytes memory address (wordBytes value) := by
  unfold effectStore64
  rw [extractedBytes_eq, effectStoreBytes_eq]
  simp

def saveMemoryEffect (memory : RawMemory) (sp fp lr : Word) : RawMemory :=
  let address := sp + BitVec.ofInt 64 (-16)
  effectStore64 (effectStore64 memory address fp) (address + BitVec.ofNat 64 8) lr

/-- A conditional single-step theorem over the exact bit-vector state and
Store expression. Entry allocation/representation premises remain explicit;
it grants no caller/ABI/object execution authority by itself. -/
theorem save_step {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} (sp fp lr : Word) (raw : RawMemory)
    (input : PlacedFrameInput source memory ids frame sp.toNat 16)
    (size : frame.size = 16) (represented : RawRepresents memory raw) :
    Embeds source (saveMemory memory frame.base fp lr) ids ∧
    RawRepresents (saveMemory memory frame.base fp lr) (saveMemoryEffect raw sp fp lr) ∧
    sp + BitVec.ofInt 64 (-16) = BitVec.ofNat 64 frame.base := by
  have address : sp + BitVec.ofInt 64 (-16) = BitVec.ofNat 64 frame.base := by
    apply BitVec.eq_of_toNat_eq
    have bound : frame.base < 2 ^ 64 := by
      have endAtSp := input.endAtSp
      have finite := sp.isLt
      rw [size] at endAtSp
      dsimp only [TrustIr.Addr] at *
      omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    have exact := pre_index_effect_address input size
    simpa only [BitVec.ofNat_toNat] using exact
  have update : saveMemoryEffect raw sp fp lr =
      rawWriteBytes (rawWriteBytes raw frame.base (wordBytes fp)) (frame.base + 8) (wordBytes lr) := by
    unfold saveMemoryEffect
    rw [address]
    dsimp only
    rw [BitVec.ofNat_add_ofNat, effectStore64_eq, effectStore64_eq]
  have result := placed_pair_raw_memory input size represented fp lr
  exact ⟨result.1, update.symm ▸ result.2.1, address⟩

end SemR.MemoryEmbedding.FrameStep

#print axioms SemR.MemoryEmbedding.FrameStep.save_step
