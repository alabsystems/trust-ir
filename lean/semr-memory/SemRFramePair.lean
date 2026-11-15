-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRPlacedFrame

/-! Denotation of the canonical memory effects for the actual FP/LR pair.

These are the existing Memory read/write and integer codecs, with full 64-bit
values. Actual decoded instruction/effect binding is a separate required input;
this module neither guesses an entry allocation nor claims a whole call proof.
-/

namespace SemR.MemoryEmbedding.FramePair

open TrustIr (Memory Allocation AllocId Addr)

local macro "frame_arith" : tactic =>
  `(tactic| ((try simp only [Addr, addrSpace] at *) <;> (try dsimp only at *) <;> omega))

abbrev Word := BitVec 64

/-- The canonical integer encoder, not a second byte representation. -/
def wordBytes (value : Word) : List UInt8 :=
  TrustIr.encodeIntBytes (Int.ofNat value.toNat) 8

theorem wordBytes_length (value : Word) : (wordBytes value).length = 8 :=
  TrustIr.encodeIntBytes_length _ _

theorem wordBytes_decode (value : Word) :
    TrustIr.decodeIntBytes (wordBytes value) = value.toNat :=
  TrustIr.decode_encode_address value.toNat value.isLt

private theorem encoded_at (count value index : Nat) (inside : index < count) :
    (TrustIr.encodeIntBytes.go count value)[index]? =
      some (UInt8.ofNat ((value / 256 ^ index) % 256)) := by
  induction index generalizing count value with
  | zero =>
    cases count with
    | zero => omega
    | succ count => simp [TrustIr.encodeIntBytes.go]
  | succ index induction =>
    cases count with
    | zero => omega
    | succ count =>
      simp only [TrustIr.encodeIntBytes.go, List.getElem?_cons_succ]
      rw [induction count (value / 256) (by omega)]
      rw [Nat.div_div_eq_div_mul]
      simp [Nat.pow_succ, Nat.mul_comm]

/-- The byte written by the canonical codec is exactly the bit-vector
extract in MachineState's actual little-endian MemWrite application. -/
theorem wordBytes_extract (value : Word) (index : Nat) (inside : index < 8) :
    ((wordBytes value)[index]?).map UInt8.toNat =
      some ((value.extractLsb' (8 * index) 8).toNat) := by
  unfold wordBytes TrustIr.encodeIntBytes
  change ((TrustIr.encodeIntBytes.go 8 value.toNat)[index]?).map UInt8.toNat = _
  rw [encoded_at 8 value.toNat index inside]
  simp only [Option.map_some, TrustIr.uint8_toNat_ofNat_mod, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have power : 256 ^ index = 2 ^ (8 * index) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]
  rw [power]

/-- The exact left-associated zero-extend/shift/or expression emitted for
the eight-byte canonical LDP load, with no unspecified high bits. -/
def joinWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : Word :=
  ((((((b0.setWidth 64 ||| (b1.setWidth 64 <<< 8)) ||| (b2.setWidth 64 <<< 16)) |||
    (b3.setWidth 64 <<< 24)) ||| (b4.setWidth 64 <<< 32)) |||
    (b5.setWidth 64 <<< 40)) ||| (b6.setWidth 64 <<< 48)) ||| (b7.setWidth 64 <<< 56)

theorem extracts_reconstruct (value : Word) :
    joinWord (value.extractLsb' 0 8) (value.extractLsb' 8 8)
      (value.extractLsb' 16 8) (value.extractLsb' 24 8)
      (value.extractLsb' 32 8) (value.extractLsb' 40 8)
      (value.extractLsb' 48 8) (value.extractLsb' 56 8) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  -- Finite bit positions, arbitrary 64-bit value; no native decision axiom.
  have positions : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 ∨ index = 17 ∨ index = 18 ∨ index = 19 ∨ index = 20 ∨ index = 21 ∨ index = 22 ∨ index = 23 ∨ index = 24 ∨ index = 25 ∨ index = 26 ∨ index = 27 ∨ index = 28 ∨ index = 29 ∨ index = 30 ∨ index = 31 ∨ index = 32 ∨ index = 33 ∨ index = 34 ∨ index = 35 ∨ index = 36 ∨ index = 37 ∨ index = 38 ∨ index = 39 ∨ index = 40 ∨ index = 41 ∨ index = 42 ∨ index = 43 ∨ index = 44 ∨ index = 45 ∨ index = 46 ∨ index = 47 ∨ index = 48 ∨ index = 49 ∨ index = 50 ∨ index = 51 ∨ index = 52 ∨ index = 53 ∨ index = 54 ∨ index = 55 ∨ index = 56 ∨ index = 57 ∨ index = 58 ∨ index = 59 ∨ index = 60 ∨ index = 61 ∨ index = 62 ∨ index = 63 := by omega
  rcases positions with position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position | position
  all_goals
    subst index
    simp [joinWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']

/-- Exactly the two memory writes of STP X29,X30,[SP,#-16]!: first
FP at the resulting SP, then LR eight bytes above it. -/
def saveMemory (memory : Memory) (base : Addr) (fp lr : Word) : Memory :=
  (memory.writeBytes base (wordBytes fp)).writeBytes (base + 8) (wordBytes lr)

/-- Exactly the two little-endian reads of LDP X29,X30,[SP],#16. -/
def restoreValues (memory : Memory) (base : Addr) : Option (Nat × Nat) := do
  let fp ← memory.readBytes base 8
  let lr ← memory.readBytes (base + 8) 8
  pure (TrustIr.decodeIntBytes fp, TrustIr.decodeIntBytes lr)

/-- The total byte-array domain used by the actual machine formulas. -/
abbrev RawMemory := Word → BitVec 8

/-- Defined canonical bytes have their exact machine image. An uninitialized
canonical byte remains unconstrained, not fabricated as zero. This is an
additional representation obligation, not a source-entry heap constructor. -/
def RawRepresents (memory : Memory) (raw : RawMemory) : Prop :=
  ∀ address byte, address < addrSpace → memory.bytes address = some byte →
    raw (BitVec.ofNat 64 address) = BitVec.ofNat 8 byte.toNat

def rawStore (raw : RawMemory) (address : Word) (byte : UInt8) : RawMemory :=
  fun query => if query = address then BitVec.ofNat 8 byte.toNat else raw query

/-- Sequential SMT array stores of the very same canonical bytes. The
address bridge below proves equality to the actual 64-bit effect addresses. -/
def rawWriteBytes (raw : RawMemory) (address : Nat) (bytes : List UInt8) : RawMemory :=
  (bytes.foldl (fun (state : RawMemory × Nat) byte =>
    (rawStore state.1 (BitVec.ofNat 64 state.2) byte, state.2 + 1)) (raw,address)).1

@[simp] theorem rawWriteBytes_nil (raw : RawMemory) (address : Nat) :
    rawWriteBytes raw address [] = raw := rfl

/-- The fold retains the original sequential-store equation exactly. -/
theorem rawWriteBytes_cons (raw : RawMemory) (address : Nat) (byte : UInt8) (rest : List UInt8) :
    rawWriteBytes raw address (byte :: rest) =
      rawWriteBytes (rawStore raw (BitVec.ofNat 64 address) byte) (address + 1) rest := rfl

private theorem raw_represents_byte {memory : Memory} {raw : RawMemory}
    (related : RawRepresents memory raw) (address : Nat) (byte : UInt8)
    (finite : address < addrSpace) :
    RawRepresents (memory.writeBytes address [byte])
      (rawStore raw (BitVec.ofNat 64 address) byte) := by
  intro query value queryFinite stored
  by_cases same : query = address
  · subst query
    have written : (memory.writeBytes address [byte]).bytes address = some byte := by
      simpa using Memory.bytes_writeBytes_inside memory address 0 [byte] (by simp)
    rw [written] at stored
    cases stored
    simp [rawStore]
  · have different : BitVec.ofNat 64 query ≠ BitVec.ofNat 64 address := by
      intro equal
      have naturals := congrArg BitVec.toNat equal
      change query < 2 ^ 64 at queryFinite
      change address < 2 ^ 64 at finite
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt queryFinite,
        Nat.mod_eq_of_lt finite] at naturals
      exact same naturals
    simp only [rawStore, different, ↓reduceIte]
    apply related query value queryFinite
    have outside : query < address ∨ address + [byte].length ≤ query := by
      change query < address ∨ address + 1 ≤ query
      omega
    rw [Memory.bytes_writeBytes_outside memory address query [byte] outside] at stored
    exact stored

/-- The authoritative compact store and sequential head/tail writes have
    identical byte observations. Their storage trees need not be equal. -/
private theorem write_cons_observations (memory : Memory) (address : Nat) (byte : UInt8) (rest : List UInt8) :
    ((memory.writeBytes address [byte]).writeBytes (address + 1) rest).bytes =
      (memory.writeBytes address (byte :: rest)).bytes := by
  funext query
  by_cases before : query < address
  · rw [Memory.bytes_writeBytes_outside _ (address + 1) query rest (Or.inl (Nat.lt_succ_of_lt before)),
      Memory.bytes_writeBytes_outside memory address query [byte] (Or.inl before),
      Memory.bytes_writeBytes_outside memory address query (byte :: rest) (Or.inl before)]
  · obtain ⟨index,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    cases index with
    | zero =>
      simp only [Nat.add_zero]
      rw [Memory.bytes_writeBytes_outside _ (address + 1) address rest (Or.inl (by omega))]
      have singleton : (memory.writeBytes address [byte]).bytes address = some byte := by
        simpa using Memory.bytes_writeBytes_inside memory address 0 [byte] (by simp)
      have head : (memory.writeBytes address (byte :: rest)).bytes address = some byte := by
        simpa using Memory.bytes_writeBytes_inside memory address 0 (byte :: rest) (by simp)
      exact singleton.trans head.symm
    | succ index =>
      by_cases inside : index < rest.length
      · have tail := Memory.bytes_writeBytes_inside (memory.writeBytes address [byte]) (address + 1) index rest inside
        have whole := Memory.bytes_writeBytes_inside memory address (index + 1) (byte :: rest) (by simpa using Nat.succ_lt_succ inside)
        have same : address + (index + 1) = (address + 1) + index := by omega
        rw [← same] at tail
        exact tail.trans (by simpa using whole.symm)
      · rw [Memory.bytes_writeBytes_outside _ (address + 1) (address + (index + 1)) rest (Or.inr (by omega)),
          Memory.bytes_writeBytes_outside memory address (address + (index + 1)) [byte] (Or.inr (by change address + 1 ≤ _; omega)),
          Memory.bytes_writeBytes_outside memory address (address + (index + 1)) (byte :: rest) (Or.inr (by simp only [List.length_cons]; omega))]

theorem raw_represents_write {memory : Memory} {raw : RawMemory}
    (related : RawRepresents memory raw) (address : Nat) (data : List UInt8)
    (finite : address + data.length ≤ addrSpace) :
    RawRepresents (memory.writeBytes address data) (rawWriteBytes raw address data) := by
  induction data generalizing memory raw address with
  | nil => exact related
  | cons byte rest induction =>
    have first : address < addrSpace := by simp only [List.length_cons] at finite; omega
    have later : address + 1 + rest.length ≤ addrSpace := by
      simp only [List.length_cons] at finite
      omega
    have represented := induction (raw_represents_byte related address byte first) (address + 1) later
    intro query value queryFinite stored
    apply represented query value queryFinite
    rw [write_cons_observations]
    exact stored

private theorem read_some_byte (memory : Memory) (address : Nat) (bytes : List UInt8)
    (read : memory.readBytes address bytes.length = some bytes)
    (index : Nat) (inside : index < bytes.length) :
    memory.bytes (address + index) = some bytes[index] := by
  induction bytes generalizing address index with
  | nil => simp at inside
  | cons byte rest induction =>
    change Memory.readBytes.go memory (rest.length + 1) address = some (byte :: rest) at read
    simp only [Memory.readBytes.go] at read
    cases first : memory.bytes address with
    | none => simp [first] at read
    | some actual =>
      rw [first] at read
      cases tail : Memory.readBytes.go memory rest.length (address + 1) with
      | none => simp [tail] at read
      | some remaining =>
        rw [tail] at read
        have equal := Option.some.inj read
        have headEqual : actual = byte := (List.cons.inj equal).1
        have restEqual : remaining = rest := (List.cons.inj equal).2
        subst actual
        subst remaining
        cases index with
        | zero => simpa using first
        | succ index =>
          have insideRest : index < rest.length := by simpa using inside
          have value := induction (address + 1) tail index insideRest
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using value

def RawReadsWord (raw : RawMemory) (address : Nat) (value : Word) : Prop :=
  ∀ index, index < 8 → raw (BitVec.ofNat 64 (address + index)) = value.extractLsb' (8 * index) 8

/-- Connect a successful canonical little-endian word read to every raw byte
select used by the actual LDP expression. No query is excluded. -/
theorem raw_reads_word {memory : Memory} {raw : RawMemory} (related : RawRepresents memory raw)
    (address : Nat) (value : Word) (finite : address + 8 ≤ addrSpace)
    (read : memory.readBytes address 8 = some (wordBytes value)) :
    RawReadsWord raw address value := by
  intro index inside
  have length := wordBytes_length value
  have indexBound : index < (wordBytes value).length := by rwa [length]
  have observed := read_some_byte memory address (wordBytes value) (by simpa [length] using read) index indexBound
  have bound : address + index < addrSpace := by omega
  have rawByte := related (address + index) _ bound observed
  have extracted := wordBytes_extract value index inside
  rw [List.getElem?_eq_getElem indexBound] at extracted
  simp only [Option.map_some] at extracted
  have byteEqual := Option.some.inj extracted
  rw [rawByte]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [byteEqual]
  exact Nat.mod_eq_of_lt (value.extractLsb' (8 * index) 8).isLt

def rawReadWord (raw : RawMemory) (address : Nat) : Word :=
  joinWord (raw (BitVec.ofNat 64 address)) (raw (BitVec.ofNat 64 (address + 1)))
    (raw (BitVec.ofNat 64 (address + 2))) (raw (BitVec.ofNat 64 (address + 3)))
    (raw (BitVec.ofNat 64 (address + 4))) (raw (BitVec.ofNat 64 (address + 5)))
    (raw (BitVec.ofNat 64 (address + 6))) (raw (BitVec.ofNat 64 (address + 7)))

theorem raw_read_exact {raw : RawMemory} {address : Nat} {value : Word}
    (read : RawReadsWord raw address value) : rawReadWord raw address = value := by
  have b0 := read 0 (by decide)
  have b1 := read 1 (by decide)
  have b2 := read 2 (by decide)
  have b3 := read 3 (by decide)
  have b4 := read 4 (by decide)
  have b5 := read 5 (by decide)
  have b6 := read 6 (by decide)
  have b7 := read 7 (by decide)
  simp only [Nat.add_zero] at b0
  unfold rawReadWord
  rw [b0, b1, b2, b3, b4, b5, b6, b7]
  exact extracts_reconstruct value

theorem saveMemory_read_fp (memory : Memory) (base : Addr) (fp lr : Word) :
    (saveMemory memory base fp lr).readBytes base 8 = some (wordBytes fp) := by
  unfold saveMemory
  rw [TrustIr.writeBytes_non_aliasing]
  · simpa only [wordBytes_length] using TrustIr.writeBytes_readBytes_general memory base (wordBytes fp)
  · exact Or.inl (Nat.le_refl _)

theorem saveMemory_read_lr (memory : Memory) (base : Addr) (fp lr : Word) :
    (saveMemory memory base fp lr).readBytes (base + 8) 8 = some (wordBytes lr) := by
  unfold saveMemory
  simpa only [wordBytes_length] using
    TrustIr.writeBytes_readBytes_general (memory.writeBytes base (wordBytes fp)) (base + 8) (wordBytes lr)

/-- Every bit of both saved register values is recovered; no truncation or
specified-low-bits-only result is substituted. -/
theorem save_restore_exact (memory : Memory) (base : Addr) (fp lr : Word) :
    restoreValues (saveMemory memory base fp lr) base = some (fp.toNat, lr.toNat) := by
  simp [restoreValues, saveMemory_read_fp, saveMemory_read_lr, wordBytes_decode]

theorem save_preserves_source {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) (fp lr : Word) :
    Embeds source (saveMemory memory frame.base fp lr) ids := by
  apply input.preserves
  apply FrameWrites.store (data := wordBytes lr)
  · apply FrameWrites.store (data := wordBytes fp)
    · exact FrameWrites.done memory
    · unfold WithinFrame
      rw [wordBytes_length, size]
      constructor <;> frame_arith
  · unfold WithinFrame
    rw [wordBytes_length, size]
    constructor <;> frame_arith

/-- The actual 64-bit pre-index subtraction denotes the canonical frame
base. It cannot wrap because the checked placement supplies the full extent. -/
theorem pre_index_address {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) :
    ((BitVec.ofNat 64 entrySp) - (BitVec.ofNat 64 16)).toNat = frame.base := by
  have entry : (BitVec.ofNat 64 entrySp).toNat = entrySp :=
    Nat.mod_eq_of_lt input.finiteSp
  rw [BitVec.toNat_sub_of_not_usubOverflow]
  · rw [entry]
    simp only [BitVec.toNat_ofNat]
    have placement := input.endAtSp
    rw [size] at placement
    frame_arith
  · simp only [BitVec.usubOverflow, entry, BitVec.toNat_ofNat, decide_eq_true_eq]
    have placement := input.endAtSp
    rw [size] at placement
    frame_arith

/-- Every actual byte address of both pair transfers agrees with natural
canonical addressing. This includes the highest LR byte and excludes wrap. -/
theorem transfer_address {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) (offset : Nat) (inside : offset < 16) :
    ((BitVec.ofNat 64 frame.base) + (BitVec.ofNat 64 offset)).toNat = frame.base + offset := by
  have placement := input.endAtSp
  rw [size] at placement
  have baseBound : frame.base < 2 ^ 64 := by have := input.finiteSp; frame_arith
  have offsetBound : offset < 2 ^ 64 := by frame_arith
  have sumBound : frame.base + offset < 2 ^ 64 := by have := input.finiteSp; frame_arith
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseBound,
    Nat.mod_eq_of_lt offsetBound, Nat.mod_eq_of_lt sumBound]

/-- Exact BvAdd-by-negative-16 spelling emitted by Aarch64Semantics for the
pre-index effect, rather than only its equivalent subtraction spelling. -/
theorem pre_index_effect_address {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) :
    ((BitVec.ofNat 64 entrySp) + (BitVec.ofInt 64 (-16))).toNat = frame.base := by
  have negative : BitVec.ofInt 64 (-16) = -(BitVec.ofNat 64 16) := by decide
  rw [negative, ← BitVec.sub_eq_add_neg]
  exact pre_index_address input size

/-- Exact nested base-plus-eight-plus-byte address of the second transfer's
array stores/selects in the canonical machine effect application. -/
theorem second_transfer_effect_address {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) (byte : Nat) (inside : byte < 8) :
    (((BitVec.ofNat 64 frame.base) + (BitVec.ofNat 64 8)) +
      (BitVec.ofNat 64 byte)).toNat = frame.base + 8 + byte := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simpa [Nat.add_assoc] using transfer_address input size (8 + byte) (by omega)

theorem post_index_sp {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) :
    ((BitVec.ofNat 64 frame.base) + (BitVec.ofNat 64 16)).toNat = entrySp := by
  have placement := input.endAtSp
  rw [size] at placement
  have baseBound : frame.base < 2 ^ 64 := by have := input.finiteSp; frame_arith
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseBound]
  rw [placement]
  exact Nat.mod_eq_of_lt input.finiteSp

/-- The canonical pair effect preserves every embedded live source byte and
recovers all 128 saved bits. It does not assert that an intervening call kept
those bytes, or that entry heap / ABI / object custody has been established. -/
theorem placed_pair_memory {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) (fp lr : Word) :
    Embeds source (saveMemory memory frame.base fp lr) ids ∧
    restoreValues (saveMemory memory frame.base fp lr) frame.base = some (fp.toNat, lr.toNat) ∧
    ((BitVec.ofNat 64 entrySp) - (BitVec.ofNat 64 16)).toNat = frame.base ∧
    ((BitVec.ofNat 64 frame.base) + (BitVec.ofNat 64 16)).toNat = entrySp :=
  ⟨save_preserves_source input size fp lr, save_restore_exact memory frame.base fp lr,
    pre_index_address input size, post_index_sp input size⟩

/-- Connect the actual total-array pair stores to the canonical allocation
memory. The entire source embedding survives, and every defined canonical
byte still has its exact raw-machine image at every finite query. -/
theorem placed_pair_raw_memory {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat} {raw : RawMemory}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) (related : RawRepresents memory raw) (fp lr : Word) :
    Embeds source (saveMemory memory frame.base fp lr) ids ∧
    RawRepresents (saveMemory memory frame.base fp lr)
      (rawWriteBytes (rawWriteBytes raw frame.base (wordBytes fp))
        (frame.base + 8) (wordBytes lr)) ∧
    restoreValues (saveMemory memory frame.base fp lr) frame.base = some (fp.toNat, lr.toNat) := by
  have placement := input.endAtSp
  rw [size] at placement
  have capacity := input.finiteSp
  have first : frame.base + (wordBytes fp).length ≤ addrSpace := by
    rw [wordBytes_length]
    frame_arith
  have second : frame.base + 8 + (wordBytes lr).length ≤ addrSpace := by
    rw [wordBytes_length]
    frame_arith
  exact ⟨save_preserves_source input size fp lr,
    raw_represents_write (raw_represents_write related frame.base (wordBytes fp) first)
      (frame.base + 8) (wordBytes lr) second,
    save_restore_exact memory frame.base fp lr⟩

/-- The complete raw-machine register readback for the two checked pair
effects, together with preservation of the unrestricted source embedding. -/
theorem placed_pair_raw_readback {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    {frame : Allocation} {entrySp : Nat} {raw : RawMemory}
    (input : PlacedFrameInput source memory ids frame entrySp 16)
    (size : frame.size = 16) (related : RawRepresents memory raw) (fp lr : Word) :
    let saved := rawWriteBytes (rawWriteBytes raw frame.base (wordBytes fp))
      (frame.base + 8) (wordBytes lr)
    Embeds source (saveMemory memory frame.base fp lr) ids ∧
    rawReadWord saved frame.base = fp ∧ rawReadWord saved (frame.base + 8) = lr := by
  obtain ⟨embedding, image, _⟩ := placed_pair_raw_memory input size related fp lr
  have placement := input.endAtSp
  rw [size] at placement
  have capacity := input.finiteSp
  refine ⟨embedding, ?_, ?_⟩
  · exact raw_read_exact (raw_reads_word image frame.base fp (by frame_arith)
      (saveMemory_read_fp memory frame.base fp lr))
  · exact raw_read_exact (raw_reads_word image (frame.base + 8) lr (by frame_arith)
      (saveMemory_read_lr memory frame.base fp lr))

/-- An intervening callee must prove this property for the saved allocation.
This definition does not assume it of a raw pointer or supply a call rely. -/
def KeepsFrame (before after : RawMemory) (base : Nat) : Prop :=
  ∀ offset, offset < 16 → after (BitVec.ofNat 64 (base + offset)) = before (BitVec.ofNat 64 (base + offset))

theorem kept_frame_read (before after : RawMemory) (base offset : Nat)
    (kept : KeepsFrame before after base) (inside : offset + 8 ≤ 16) :
    rawReadWord after (base + offset) = rawReadWord before (base + offset) := by
  have eqAt : ∀ byte, byte < 8 →
      after (BitVec.ofNat 64 (base + offset + byte)) =
        before (BitVec.ofNat 64 (base + offset + byte)) := by
    intro byte bounded
    simpa [Nat.add_assoc] using kept (offset + byte) (by omega)
  have zero := eqAt 0 (by decide)
  simp only [Nat.add_zero] at zero
  unfold rawReadWord
  simp only [zero, eqAt 1 (by decide), eqAt 2 (by decide),
    eqAt 3 (by decide), eqAt 4 (by decide), eqAt 5 (by decide),
    eqAt 6 (by decide), eqAt 7 (by decide), Nat.add_zero]

end SemR.MemoryEmbedding.FramePair
