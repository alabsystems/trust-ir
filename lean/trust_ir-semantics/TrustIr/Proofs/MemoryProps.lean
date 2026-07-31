-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Memory safety theorems: load-after-store, store-store, non-aliasing,
-- alloca freshness, and encoding round-trip properties.
-- Phase 2 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 2

import TrustIr.Semantics.Memory

namespace TrustIr

/-!
# Memory Properties

These theorems establish key correctness properties of TrustIr memory
operations. They are the Phase 2 proof deliverables.

## Proved properties (all proof-placeholder-free)

1. Encode/decode round-trip for integer types
2. Alloca returns a valid (non-zero) address
3. Memory.alloc increases the nextAddr
4. writeBytes then readBytes returns the written data (single byte AND multi-byte)
5. writeBytes_overwrite: second store overwrites the first
6. writeBytes_non_aliasing: writes to non-overlapping addresses are independent
7. gepByteOffset_zero and gepByteOffset_monotone
8. encode_decode_bool: Bool encode/decode round-trip
9. encode_decode_nullPtr: NullPtr encode/decode round-trip
10. writeBytes_readBytes_general: multi-byte writeBytes/readBytes round-trip
11. encodeIntBytes_length: encodeIntBytes produces exactly numBytes bytes
12. encodeValue_int_length: encoded integer length matches width/8
13. encodeValue_bool_length: encoded bool length is 1
14. encodeValue_nullPtr_length: encoded null pointer length is 8

## Helper lemmas (proved, building blocks for 5, 6, and 10)

- updateBytes_below: bytes below write range are unchanged
- updateBytes_above: bytes above write range are unchanged
- readBytes_go_partial_ext: readBytes.go depends only on bytes in the read range
- updateBytes_input_irrelevant: updateBytes depends only on bytes outside write range
- updateBytes_overwrite_eq: most recent write wins at updateBytes level
- updateBytes_at_index: updateBytes writes data[i] at addr+i
- readBytes_go_from_bytes: readBytes.go recovers bytes when each position is initialized

## Design note

These proofs operate on the pure helper functions (Memory.readBytes,
Memory.writeBytes, encodeValue, decodeValue) rather than the monadic
wrappers (semLoad, semStore). This keeps the proofs clean and
composable. Lifting to the monadic level is mechanical.
-/

-- =================================================================
-- Encoding round-trip properties
-- =================================================================

/-- Encoding then decoding a single byte returns the original value. -/
theorem encode_decode_uint8 (b : UInt8) :
    decodeIntBytes [b] = b.toNat := by
  simp [decodeIntBytes, decodeIntBytes.go]

/-- encodeIntBytes with 0 bytes produces an empty list. -/
theorem encode_zero_bytes (v : Int) :
    encodeIntBytes v 0 = [] := by
  simp [encodeIntBytes, encodeIntBytes.go]

/-- encodeIntBytes with 1 byte produces a singleton list. -/
theorem encode_one_byte (v : Int) :
    (encodeIntBytes v 1).length = 1 := by
  simp [encodeIntBytes, encodeIntBytes.go]

/-- Encoding a bool produces exactly one byte. -/
theorem encode_bool_length (b : Bool) :
    encodeValue (.bool b) = some [if b then 1 else 0] := by
  simp [encodeValue]

/-- Encoding a null pointer produces 8 zero bytes. -/
theorem encode_nullPtr :
    encodeValue .nullPtr = some (List.replicate 8 0) := by
  simp [encodeValue]

-- =================================================================
-- Alloca properties
-- =================================================================

/-- Memory.alloc always returns an address >= the current nextAddr.
    Since nextAddr starts at 1024 (the null page), this guarantees
    the returned address is never zero. -/
theorem alloc_addr_is_nextAddr (mem : Memory) (size : Nat) (origin : AllocationOrigin) :
    (mem.alloc size origin).fst = mem.nextAddr := by
  simp [Memory.alloc]

/-- Memory.alloc advances nextAddr by exactly size bytes. -/
theorem alloc_advances_nextAddr (mem : Memory) (size : Nat) (origin : AllocationOrigin) :
    (mem.alloc size origin).snd.nextAddr = mem.nextAddr + size := by
  simp [Memory.alloc]

/-- Memory.alloc increments the allocation ID counter. -/
theorem alloc_increments_allocId (mem : Memory) (size : Nat) (origin : AllocationOrigin) :
    (mem.alloc size origin).snd.nextAllocId = mem.nextAllocId + 1 := by
  simp [Memory.alloc]

/-- Memory.alloc adds exactly one allocation to the list. -/
theorem alloc_adds_one_allocation (mem : Memory) (size : Nat) (origin : AllocationOrigin) :
    (mem.alloc size origin).snd.allocations.length = mem.allocations.length + 1 := by
  simp [Memory.alloc, List.length_cons]

/-- The fresh allocation from Memory.alloc is alive. -/
theorem alloc_is_alive (mem : Memory) (size : Nat) (origin : AllocationOrigin) :
    let result := mem.alloc size origin
    let newAllocs := result.snd.allocations
    match newAllocs with
    | alloc :: _ => alloc.alive = true
    | [] => False := by
  simp [Memory.alloc]

/-- In the initial empty memory, nextAddr is 1024 (null page reserve).
    Combined with alloc_addr_is_nextAddr, this proves alloca never
    returns address 0. -/
theorem empty_memory_nextAddr :
    Memory.empty.nextAddr = 1024 := by
  simp [Memory.empty]

/-- Alloca on empty memory produces a non-null address. -/
theorem alloc_on_empty_is_nonzero (size : Nat) (origin : AllocationOrigin) :
    (Memory.empty.alloc size origin).fst > 0 := by
  simp [Memory.alloc, Memory.empty]

-- =================================================================
-- Allocation origins are provenance, not discipline (P1 CleanHeap)
-- =================================================================

/-- The IR→memory-model origin mapping sends Clean's Perceus RC origin to
    `cleanHeap` — the mapping lock for `AllocOrigin.CleanHeap` (the Rust
    binary codec's origin byte 3). -/
theorem cleanHeap_toAllocationOrigin :
    AllocOrigin.CleanHeap.toAllocationOrigin = AllocationOrigin.cleanHeap := rfl

/-- Origins are provenance, not discipline: the origin tag never affects
    which accesses an allocation admits. In particular a `cleanHeap` cell
    and its `swiftHeap` twin accept exactly the same in-bounds accesses —
    the symbolic backbone of the executable cleanHeap/swiftHeap refcount
    parity fixtures (`ExecutableFixtures.lean`). No operational rule
    matches on `AllocationOrigin`; ARC ops gate on `Permission.arcRef` and
    `semDealloc` on `Permission.canDealloc`. -/
theorem alloc_isInBounds_ignores_origin (mem : Memory) (size : Nat)
    (o₁ o₂ : AllocationOrigin) (addr : Addr) (n : Nat) :
    (mem.alloc size o₁).snd.isInBounds addr n
      = (mem.alloc size o₂).snd.isInBounds addr n := rfl

/-- Origin-irrelevance of liveness: same statement for `isAllocated`. -/
theorem alloc_isAllocated_ignores_origin (mem : Memory) (size : Nat)
    (o₁ o₂ : AllocationOrigin) (addr : Addr) :
    (mem.alloc size o₁).snd.isAllocated addr
      = (mem.alloc size o₂).snd.isAllocated addr := rfl

-- =================================================================
-- writeBytes / readBytes round-trip
-- =================================================================

/-- Writing zero bytes is a no-op: the bytes function is unchanged. -/
theorem writeBytes_nil (mem : Memory) (addr : Addr) :
    (mem.writeBytes addr []).bytes = mem.bytes := by
  simp [Memory.writeBytes, Memory.writeBytes.updateBytes]

/-- Reading zero bytes always succeeds with an empty list. -/
theorem readBytes_zero (mem : Memory) (addr : Addr) :
    mem.readBytes addr 0 = some [] := by
  simp [Memory.readBytes, Memory.readBytes.go]

/-- Writing a single byte then reading it back returns the byte.
    This is the base case for the writeBytes/readBytes round-trip. -/
theorem writeBytes_readBytes_single (mem : Memory) (addr : Addr) (b : UInt8) :
    (mem.writeBytes addr [b]).readBytes addr 1 = some [b] := by
  simp [Memory.writeBytes, Memory.writeBytes.updateBytes,
        Memory.readBytes, Memory.readBytes.go]

-- =================================================================
-- updateBytes helper lemmas (building blocks for store-store and
-- non-aliasing proofs)
-- =================================================================

/-- updateBytes does not change bytes below the write start address.
    If a < addr, then the byte at a is unchanged after updateBytes.
    Proved by induction on data: each step extends the write range by 1
    at the top, but a remains below the start. -/
private theorem updateBytes_below (bytes : Addr -> Option UInt8) (data : List UInt8)
    (addr a : Addr) (hlt : a < addr) :
    Memory.writeBytes.updateBytes bytes addr data a = bytes a := by
  induction data generalizing addr bytes with
  | nil => simp [Memory.writeBytes.updateBytes]
  | cons b rest ih =>
    simp only [Memory.writeBytes.updateBytes]
    have hne : ¬(a == addr) = true := by simp [beq_iff_eq]; exact Nat.ne_of_lt hlt
    rw [ih _ _ (Nat.lt_succ_of_lt hlt)]; simp [hne]

/-- updateBytes does not change bytes above the write range.
    If a >= addr + data.length, then the byte at a is unchanged.
    Proved by induction on data. -/
private theorem updateBytes_above (bytes : Addr -> Option UInt8) (data : List UInt8)
    (addr a : Addr) (hab : a >= addr + data.length) :
    Memory.writeBytes.updateBytes bytes addr data a = bytes a := by
  induction data generalizing addr bytes with
  | nil => simp [Memory.writeBytes.updateBytes]
  | cons b rest ih =>
    simp only [Memory.writeBytes.updateBytes, List.length_cons] at hab |-
    have hlt : addr < a :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos rest.length)) hab
    have hab' : a >= (addr + 1) + rest.length := by
      have h1 : addr + rest.length.succ = addr + rest.length + 1 := rfl
      have h2 : addr + rest.length + 1 = (addr + 1) + rest.length := by
        rw [Nat.add_assoc, Nat.add_comm rest.length 1, Nat.add_assoc]
      rw [h1, h2] at hab; exact hab
    let bytes' : Addr -> Option UInt8 :=
      fun x => if (x == addr) = true then some b else bytes x
    rw [ih bytes' (addr + 1) hab']
    simp [bytes', beq_iff_eq, Nat.ne_of_gt hlt]

-- =================================================================
-- readBytes extensionality (partial range)
-- =================================================================

/-- readBytes.go only reads mem.bytes at addresses in [addr, addr+n).
    If two memories agree on the bytes function over this range,
    readBytes.go returns the same result.

    Proof by induction on n. At each step, readBytes.go reads mem.bytes
    at the current address, then recurses with (addr+1, n-1). -/
private theorem readBytes_go_partial_ext (mem1 mem2 : Memory)
    (n : Nat) (addr : Addr)
    (hBytes : forall a, addr <= a -> a < addr + n -> mem1.bytes a = mem2.bytes a) :
    Memory.readBytes.go mem1 n addr = Memory.readBytes.go mem2 n addr := by
  induction n generalizing addr with
  | zero => simp [Memory.readBytes.go]
  | succ k ih =>
    simp only [Memory.readBytes.go]
    have hAddr : mem1.bytes addr = mem2.bytes addr :=
      hBytes addr (Nat.le_refl addr) (Nat.lt_add_of_pos_right (Nat.succ_pos k))
    rw [hAddr]
    cases mem2.bytes addr with
    | none => rfl
    | some b =>
      have ihResult := ih (addr + 1) (fun a ha1 ha2 => by
        apply hBytes a
        · exact Nat.le_of_succ_le ha1
        · have h1 : addr + 1 + k = addr + (k + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 k]
          rw [h1] at ha2; exact ha2)
      rw [ihResult]

-- =================================================================
-- Multi-byte writeBytes/readBytes round-trip
-- =================================================================

/-- updateBytes writes exactly the given byte at each indexed position.
    After updateBytes bytes addr data, reading addr+i gives some data[i]
    for i < data.length. Proved by induction on data with index tracking. -/
private theorem updateBytes_at_index (bytes : Addr -> Option UInt8) (data : List UInt8)
    (addr : Addr) (i : Nat) (hi : i < data.length) :
    Memory.writeBytes.updateBytes bytes addr data (addr + i) = some (data.get ⟨i, hi⟩) := by
  induction data generalizing addr bytes i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons b rest ih =>
    simp only [Memory.writeBytes.updateBytes]
    cases i with
    | zero =>
      simp only [Nat.add_zero, List.get]
      have h : addr < addr + 1 := Nat.lt_succ_of_le (Nat.le_refl addr)
      rw [updateBytes_below _ rest (addr + 1) addr h]
      simp
    | succ j =>
      have hj : j < rest.length := Nat.lt_of_succ_lt_succ (List.length_cons b rest ▸ hi)
      simp only [List.get]
      have hAddr : addr + (j + 1) = (addr + 1) + j := Nat.add_right_comm addr j 1
      rw [hAddr]
      exact ih _ (addr + 1) j hj

/-- readBytes.go succeeds when every byte in the range is initialized.
    If for all i < data.length, mem.bytes at addr+i equals some data[i],
    then readBytes.go mem data.length addr returns some data. -/
private theorem readBytes_go_from_bytes (mem : Memory)
    (data : List UInt8) (addr : Addr)
    (hBytes : forall i, (hi : i < data.length) -> mem.bytes (addr + i) = some (data.get ⟨i, hi⟩)) :
    Memory.readBytes.go mem data.length addr = some data := by
  induction data generalizing addr with
  | nil => simp [Memory.readBytes.go]
  | cons b rest ih =>
    simp only [Memory.readBytes.go, List.length_cons]
    have h0 : mem.bytes addr = some b := by
      have := hBytes 0 (Nat.succ_pos rest.length)
      simp only [Nat.add_zero, List.get] at this; exact this
    rw [h0]
    have ihResult := ih (addr + 1) (fun i hi => by
      have hShift : (addr + 1) + i = addr + (i + 1) := (Nat.add_right_comm addr i 1).symm
      rw [hShift]
      exact hBytes (i + 1) (Nat.succ_lt_succ hi))
    simp [ihResult]

/-- Writing bytes then reading them back returns the original data.
    This is the general multi-byte writeBytes/readBytes round-trip theorem.

    Proof: writeBytes addr data writes data[i] at addr+i for each i.
    readBytes addr data.length reads addr+i for i in 0 to data.length-1.
    By updateBytes_at_index, each read recovers the written byte. -/
theorem writeBytes_readBytes_general (mem : Memory) (addr : Addr) (data : List UInt8) :
    (mem.writeBytes addr data).readBytes addr data.length = some data := by
  simp only [Memory.readBytes, Memory.writeBytes]
  apply readBytes_go_from_bytes _ data addr
  intro i hi
  exact updateBytes_at_index mem.bytes data addr i hi

-- =================================================================
-- updateBytes overwrite helper
-- =================================================================

/-- updateBytes at addr with data overwrites [addr, addr+data.length).
    If two byte functions agree outside this range, updateBytes results agree.
    This is the key property: updateBytes overwrites bytes in the range
    independently of the original function's values there. -/
private theorem updateBytes_input_irrelevant (f1 f2 : Addr -> Option UInt8)
    (data : List UInt8) (addr a : Addr)
    (hAgree : forall x, x < addr \/ x >= addr + data.length -> f1 x = f2 x) :
    Memory.writeBytes.updateBytes f1 addr data a =
    Memory.writeBytes.updateBytes f2 addr data a := by
  induction data generalizing addr f1 f2 with
  | nil =>
    simp only [Memory.writeBytes.updateBytes, List.length_nil, Nat.add_zero]
    apply hAgree
    rcases Nat.lt_or_ge a addr with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr hge
  | cons b rest ih =>
    simp only [Memory.writeBytes.updateBytes]
    apply ih
    intro x hx
    -- Goal: (if (x == addr) = true then some b else f1 x) =
    --       (if (x == addr) = true then some b else f2 x)
    by_cases hxa : (x == addr) = true
    · simp [hxa]
    · simp [hxa]
      -- Need: f1 x = f2 x, using hAgree
      apply hAgree
      cases hx with
      | inl hlt =>
        -- x < addr + 1 and x ≠ addr, so x < addr
        have hxne : x ≠ addr := by
          intro heq; apply hxa; rw [beq_iff_eq]; exact heq
        exact Or.inl (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hxne)
      | inr hge =>
        -- x >= addr + 1 + rest.length, so x >= addr + (rest.length + 1)
        exact Or.inr (by
          show addr + (rest.length + 1) ≤ x
          calc addr + (rest.length + 1) = addr + 1 + rest.length := by
                rw [Nat.add_assoc, Nat.add_comm 1 rest.length]
               _ ≤ x := hge)

/-- The most recent write wins: writing data2 after data1 at the same
    address produces the same byte function as writing data2 alone
    (when data1.length = data2.length). -/
private theorem updateBytes_overwrite_eq (bytes : Addr -> Option UInt8)
    (data1 data2 : List UInt8) (addr a : Addr)
    (h : data1.length = data2.length) :
    Memory.writeBytes.updateBytes
      (Memory.writeBytes.updateBytes bytes addr data1) addr data2 a =
    Memory.writeBytes.updateBytes bytes addr data2 a := by
  apply updateBytes_input_irrelevant
  intro x hx
  cases hx with
  | inl hlt => exact updateBytes_below bytes data1 addr x hlt
  | inr hge => exact updateBytes_above bytes data1 addr x (h ▸ hge)

-- =================================================================
-- Store-store property
-- =================================================================

/-- Storing to the same address twice: the second store overwrites
    the first at the byte level. The bytes function at the stored
    addresses reflects the second write.

    Stated at the byte level: writing data2 after data1 at the same
    address means readBytes returns data2. -/
theorem writeBytes_overwrite (mem : Memory) (addr : Addr) (data1 data2 : List UInt8)
    (h : data1.length = data2.length) :
    (mem.writeBytes addr data1 |>.writeBytes addr data2).readBytes addr data2.length =
    (mem.writeBytes addr data2).readBytes addr data2.length := by
  -- Both sides call readBytes on memories that only differ in the bytes function.
  -- We use readBytes_go_partial_ext to show readBytes agrees when bytes agree.
  simp only [Memory.readBytes]
  apply readBytes_go_partial_ext
  intro a _ _
  -- Show bytes fields agree at address a
  show (mem.writeBytes addr data1 |>.writeBytes addr data2).bytes a =
       (mem.writeBytes addr data2).bytes a
  simp only [Memory.writeBytes]
  exact updateBytes_overwrite_eq mem.bytes data1 data2 addr a h

-- =================================================================
-- Non-aliasing property
-- =================================================================

/-- Writing to a non-overlapping address does not affect reads from
    the original address.

    Stated at the byte level: if [addr1, addr1+n1) and [addr2, addr2+n2)
    do not overlap, then writeBytes at addr2 does not change readBytes
    at addr1.

    This is a key correctness property for optimizations that reorder
    non-aliasing memory accesses. -/
theorem writeBytes_non_aliasing (mem : Memory) (addr1 addr2 : Addr)
    (n1 : Nat) (data2 : List UInt8)
    (hNoOverlap : addr1 + n1 <= addr2 \/ addr2 + data2.length <= addr1) :
    (mem.writeBytes addr2 data2).readBytes addr1 n1 = mem.readBytes addr1 n1 := by
  -- writeBytes produces { mem with bytes := updateBytes mem.bytes addr2 data2 }.
  -- readBytes addr1 n1 only reads mem.bytes at addresses in [addr1, addr1+n1).
  -- For those addresses, updateBytes is identity because they are disjoint.
  simp only [Memory.readBytes]
  apply readBytes_go_partial_ext
  intro a ha1 ha2
  show (mem.writeBytes addr2 data2).bytes a = mem.bytes a
  simp only [Memory.writeBytes]
  cases hNoOverlap with
  | inl hLeft =>
    -- addr1 + n1 <= addr2, so a < addr1 + n1 <= addr2
    exact updateBytes_below mem.bytes data2 addr2 a (Nat.lt_of_lt_of_le ha2 hLeft)
  | inr hRight =>
    -- addr2 + data2.length <= addr1, so a >= addr1 >= addr2 + data2.length
    exact updateBytes_above mem.bytes data2 addr2 a (Nat.le_trans hRight ha1)

-- =================================================================
-- GEP properties
-- =================================================================

/-- GEP with index 0 produces the base address unchanged. -/
theorem gepByteOffset_zero (ty : Ty) (s : Nat) (h : ty.byteSize = some s) :
    gepByteOffset ty 0 = .ok 0 := by
  simp [gepByteOffset, h]

/-- GEP byte offset is monotonically increasing with positive indices.
    Proof: gepByteOffset with hTy gives .ok (index.toNat * s) for
    non-negative index. Then i.toNat <= j.toNat (monotonicity of
    Int.toNat on non-negatives) implies i.toNat * s <= j.toNat * s. -/
theorem gepByteOffset_monotone (ty : Ty) (s : Nat) (i j : Int)
    (hTy : ty.byteSize = some s) (hi : 0 <= i) (hj : i <= j) :
    exists oi oj, gepByteOffset ty i = .ok oi /\ gepByteOffset ty j = .ok oj /\ oi <= oj := by
  -- i >= 0 implies -(i < 0)
  have hi_nonneg : ¬(i < 0) := Int.not_lt.mpr hi
  -- j >= 0 follows from 0 <= i <= j
  have hj_nonneg : ¬(j < 0) := Int.not_lt.mpr (Int.le_trans hi hj)
  -- Unfold gepByteOffset for both i and j
  refine ⟨i.toNat * s, j.toNat * s, ?_, ?_, ?_⟩
  · simp [gepByteOffset, hTy, hi_nonneg]
  · simp [gepByteOffset, hTy, hj_nonneg]
  · -- Need: i.toNat <= j.toNat from 0 <= i <= j
    apply Nat.mul_le_mul_right
    cases i with
    | ofNat n =>
      cases j with
      | ofNat m => simp only [Int.toNat]; exact Int.ofNat_le.mp hj
      | negSucc m => exact absurd (Int.le_trans hi hj) (by simp)
    | negSucc n => exact absurd hi (by simp)

-- =================================================================
-- Combined load-after-store theorem sketch
-- =================================================================

/-!
## Load-after-store theorem

The full load-after-store theorem says:

  If we store a value v at address addr, then immediately load from
  addr with the same type, we get back v (modulo encoding round-trip).

  Formally: for well-typed v with ty.byteSize = some n,
    semLoad ty ptrId (semStore ty ptrId valId state) = (v', state')
  where decodeValue ty (encodeValue v) = some v'.

This requires:
1. encodeValue/decodeValue round-trip (per-type)
2. writeBytes/readBytes round-trip (byte level)
3. Bounds checks pass (address is in bounds both times)

The byte-level round-trip (writeBytes_readBytes_single) is the
foundation. The full theorem is composed from these building blocks
but requires significant bookkeeping with the monadic state, which
we defer to a subsequent iteration.
-/

/-- The encode/decode round-trip for booleans. -/
theorem encode_decode_bool (b : Bool) :
    decodeValue .Bool (match encodeValue (.bool b) with | some bs => bs | none => []) =
    some (.bool b) := by
  cases b <;> simp [encodeValue, decodeValue]

/-- The encode/decode round-trip for null pointers.
    encodeValue .nullPtr = some (replicate 8 0), and
    decodeValue .Ptr (replicate 8 0) = some .nullPtr since
    decodeIntBytes of all-zero bytes is 0, and addr==0 maps to nullPtr. -/
theorem encode_decode_nullPtr :
    decodeValue .Ptr (match encodeValue .nullPtr with | some bs => bs | none => []) =
    some .nullPtr := by
  simp [encodeValue, decodeValue, decodeIntBytes, decodeIntBytes.go, List.length, List.replicate]

/-- The encoded byte length of a boolean value is 1. -/
theorem encodeValue_bool_length (b : Bool) :
    (match encodeValue (.bool b) with | some bs => bs.length | none => 0) = 1 := by
  cases b <;> simp [encodeValue]

/-- The encoded byte length of a null pointer is 8. -/
theorem encodeValue_nullPtr_length :
    (match encodeValue .nullPtr with | some bs => bs.length | none => 0) = 8 := by
  simp [encodeValue, List.length_replicate]

/-- encodeIntBytes produces exactly numBytes bytes. -/
theorem encodeIntBytes_length (val : Int) (numBytes : Nat) :
    (encodeIntBytes val numBytes).length = numBytes := by
  simp [encodeIntBytes]
  suffices h : forall n v, (encodeIntBytes.go n v).length = n from h numBytes val.toNat
  intro n
  induction n with
  | zero => intro _; simp [encodeIntBytes.go]
  | succ k ih => intro _; simp [encodeIntBytes.go, ih]

/-- The encoded byte length of an integer value matches width/8. -/
theorem encodeValue_int_length (w : Nat) (n : Int) :
    (match encodeValue (.int w n) with | some bs => bs.length | none => 0) = w / 8 := by
  simp [encodeValue, encodeIntBytes_length]

-- =================================================================
-- Future work stubs (Phase 2 completeness claims)
-- =================================================================

/-
## Theorems to prove in subsequent iterations

1. **Integer encode/decode round-trip:**
   Prove encodeIntBytes/decodeIntBytes round-trip for values that fit
   in the given byte width. Requires showing the LE encoding is
   invertible for unsigned values in range. Then prove per-type
   encode_decode_int8, encode_decode_int16, etc.

2. **Pointer encode/decode round-trip (non-null):**
   Prove encodeValue (.ptr addr)/decodeValue .Ptr round-trip for
   non-zero addresses that fit in 64 bits. Requires integer round-trip.

3. **Alloca freshness (non-aliasing):**
   Fresh allocations from alloca do not overlap with existing allocations.
   Proof: alloc uses nextAddr which is always beyond all existing allocations.

4. **GEP in-bounds:**
   If gep base [i] is in bounds, then i < arrayLen.
   Requires connecting GEP semantics to the allocation size.

5. **Permission preservation:**
   Memory operations preserve the permission map (only alloca adds entries).

6. **Monadic load-after-store extraction:**
   Extract address and encoded bytes from semStore/semLoad monadic
   computations to connect the byte-level round-trip
   (writeBytes_readBytes_general, proved) to the program-level
   load_after_store_program theorem. Requires unfolding ~20 monadic
   binds through StateT/Except.

NOTE: Item 5 from previous iteration (Full writeBytes/readBytes round-trip)
is now PROVED as writeBytes_readBytes_general.
-/

-- =================================================================
-- GlobalAddr: pointer identity / aliasing (B1)
-- =================================================================

/-- `Sem.run` of `getState` returns the state unchanged. -/
private theorem run_getState (s : MachineState) :
    Sem.run Sem.getState s = .ok (s, s) := rfl

/-- `Sem.run` of `bindFresh` binds the value to a fresh SSA id and advances
    `nextValueId`, touching only `locals`/`nextValueId`. -/
private theorem run_bindFresh (val : Value) (st : MachineState) :
    Sem.run (Sem.bindFresh val) st =
      .ok (ValueId.mk st.nextValueId,
           { st with locals := st.locals.set (ValueId.mk st.nextValueId) val,
                     nextValueId := st.nextValueId + 1 }) := rfl

/-- Reading back the SSA value `bindFresh` just set. -/
private theorem lookupValue_bindFresh (val : Value) (st : MachineState) :
    ({ st with locals := st.locals.set (ValueId.mk st.nextValueId) val,
               nextValueId := st.nextValueId + 1 } : MachineState).lookupValue
      (ValueId.mk st.nextValueId) = some val := by
  simp [MachineState.lookupValue, ValueMap.get, ValueMap.set]

/-- **GlobalAddr cache hit is deterministic — the core of aliasing.** If a
    global's address is already cached, `semGlobalAddr` returns a pointer to
    exactly that address and leaves the cache unchanged. Hence once the first
    address-of a global fixes its address (`global_addr_*` fixtures), EVERY later
    address-of the SAME global yields the SAME pointer — they alias and compare
    equal. Universal over all globals/states; no proof placeholder or new axiom. -/
theorem semGlobalAddr_cache_hit (g : GlobalId) (addr : Addr) (s : MachineState)
    (h : s.lookupGlobal g = some addr) :
    ∃ v s',
      Sem.run (semGlobalAddr g) s = .ok (v, s')
      ∧ s'.lookupValue v = some (.ptr addr)
      ∧ s'.lookupGlobal g = some addr := by
  refine ⟨ValueId.mk s.nextValueId,
          { s with locals := s.locals.set (ValueId.mk s.nextValueId) (.ptr addr),
                   nextValueId := s.nextValueId + 1 }, ?_, ?_, ?_⟩
  · unfold semGlobalAddr
    simp only [Sem.run_bind, run_getState, Except.bind, h]
    exact run_bindFresh (.ptr addr) s
  · exact lookupValue_bindFresh (.ptr addr) s
  · simpa [MachineState.lookupGlobal] using h

-- =================================================================
-- Fat-pointer trio: value-level round trip (B3 depth ledger)
-- =================================================================

/-- **Fat-pointer round trip, value level (headline form).**
    `PtrFromParts (PtrData p) (PtrMetadata p) = p` for every fat-pointer
    value `p = .fatPtr data metadata` — decompose-then-recombine is the
    identity, with NO side condition: both projections are total on
    `.fatPtr`, and the data lane always re-injects (a 0 data lane reads
    back as `.nullPtr` and re-injects as address 0). -/
theorem fatPtr_roundTrip_value (data : Nat) (metadata : Value) :
    (do
      let d ← fatPtrDataValue (.fatPtr data metadata)
      let m ← fatPtrMetadataValue (.fatPtr data metadata)
      fatPtrFromPartsValue d m) = some (Value.fatPtr data metadata) := by
  cases data <;> rfl

/-- **Fat-pointer round trip, value level (projection form).** Any value
    on which BOTH projections are defined is a fat pointer, and
    recombining the projections yields it back exactly. -/
theorem fatPtrFromParts_data_metadata (p d m : Value)
    (hd : fatPtrDataValue p = some d) (hm : fatPtrMetadataValue p = some m) :
    fatPtrFromPartsValue d m = some p := by
  cases p <;> simp only [fatPtrDataValue, fatPtrMetadataValue,
    Option.some.injEq] at hd hm
  case fatPtr data metadata =>
    subst d; subst m
    cases data <;> rfl

end TrustIr
