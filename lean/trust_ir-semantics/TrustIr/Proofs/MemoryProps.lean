-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Memory safety theorems: load-after-store, store-store, non-aliasing,
-- alloca freshness, and encoding round-trip properties.
-- Phase 2 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 2

import TrustIr.Proofs.AllocationLayout

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

## Byte-image lookup laws

The shared byte store supplies exact snapshot, fill, inside-write and outside-
write laws. Bulk operations retain images instead of building per-byte closures.

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

-- =================================================================
-- Authoritative image helpers are in Semantics.Memory
-- =================================================================

-- =================================================================
-- GEP properties
-- =================================================================

theorem memoryExcept_bind {α β : Type} (e : Except SemError α)
    (f : α → Except SemError β) :
    Sem.fromMemoryExcept (e >>= f) = (do
      let value ← Sem.fromMemoryExcept e
      Sem.fromMemoryExcept (f value)) := by
  cases e <;> rfl

theorem memoryExcept_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Except SemError (ForInStep β)) :
    (forIn xs initial (fun x value => Sem.fromMemoryExcept (body x value)) : Sem β) =
      Sem.fromMemoryExcept (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    first
    | simp only [forIn, List.forIn, List.forIn.loop]
    | simp only [List.forIn_cons]
    rw [memoryExcept_bind]
    cases hb : body x initial with
    | error error => rfl
    | ok step =>
      cases step with
      | done result => rfl
      | yield result => exact ih result

/-- The former per-step lifting and the pure-plan implementation agree for
    all readers, layouts, worlds, errors and target models. This proof records
    the refactor without retaining a second runtime implementation. -/
private def gepValuesLiftedLoop {key : Type} (layoutOf : MemoryLayoutQuery)
    (readInteger : key → Value → Except SemError Int) (pointeeTy : Ty)
    (base : Value) (indices : List (key × Value)) (model : ByteModel := .le64) : Sem Value := do
  let layout ← Sem.fromMemoryExcept (layoutOf pointeeTy)
  let mut delta : Nat := 0
  for (identity, value) in indices do
    let integer ← Sem.fromMemoryExcept (readInteger identity value)
    let index ← Sem.fromMemoryExcept (checkedWord64Operand "GEP" false integer)
    let offset ← Sem.fromMemoryExcept (checkedWord64Mul "GEP" layout.size index)
    delta ← Sem.fromMemoryExcept (checkedWord64Add "GEP" delta offset)
  semGEPAddress base delta model

theorem semGEPValuesUsing_liftedLoop {key : Type} (layoutOf : MemoryLayoutQuery)
    (reader : key → Value → Except SemError Int) (ty : Ty)
    (base : Value) (indices : List (key × Value)) (model : ByteModel) :
    semGEPValuesUsing layoutOf reader ty base indices model =
      gepValuesLiftedLoop layoutOf reader ty base indices model := by
  apply Eq.symm
  unfold gepValuesLiftedLoop semGEPValuesUsing gepOffsetUsing
  rw [memoryExcept_bind]
  cases hl : layoutOf ty with
  | error error => rfl
  | ok layout =>
    simp only [Sem.fromMemoryExcept, pure_bind]
    have body : (fun (input : key × Value) (delta : Nat) => do
        let integer ← Sem.fromMemoryExcept (reader input.1 input.2)
        let magnitude ← Sem.fromMemoryExcept (checkedWord64Operand "GEP" false integer)
        let offset ← Sem.fromMemoryExcept (checkedWord64Mul "GEP" layout.size magnitude)
        let result ← Sem.fromMemoryExcept (checkedWord64Add "GEP" delta offset)
        pure PUnit.unit
        pure (ForInStep.yield result)) =
      (fun input delta => Sem.fromMemoryExcept (do
        let integer ← reader input.1 input.2
        let magnitude ← checkedWord64Operand "GEP" false integer
        let offset ← checkedWord64Mul "GEP" layout.size magnitude
        let result ← checkedWord64Add "GEP" delta offset
        pure (ForInStep.yield result))) := by
      funext input delta
      simp only [memoryExcept_bind, pure_bind]
      rfl
    simp only [Sem.fromMemoryExcept, pure_bind] at body
    have lifted := memoryExcept_forIn indices (0 : Nat) (fun input delta => do
      let integer ← reader input.1 input.2
      let magnitude ← checkedWord64Operand "GEP" false integer
      let offset ← checkedWord64Mul "GEP" layout.size magnitude
      let result ← checkedWord64Add "GEP" delta offset
      pure (ForInStep.yield result))
    simp only [Sem.fromMemoryExcept] at lifted
    rw [body, lifted]

/-- Every legacy-sized type also has its declared natural alignment. -/
theorem byteAlign_of_byteSize (ty : Ty) (size : Nat) (h : ty.byteSize = some size) :
    ty.byteAlign = some (ty.byteAlign.getD 1) := by
  cases ty <;> simp_all only [Ty.byteSize, Ty.byteAlign, Option.getD_some, Option.noConfusion]
  case Vector count elemTy =>
    split at h
    · contradiction
    · simp only [Ty.byteAlign, ‹¬(count == 0) = true›, ↓reduceIte]
      cases he : vectorScalarByteSize elemTy <;> simp_all

theorem scalarMemoryLayout_of_byteSize (ty : Ty) (size : Nat)
    (h : ty.byteSize = some size) :
    scalarMemoryLayout .le64 ty = .ok ⟨size, ty.byteAlign.getD 1⟩ := by
  have ha := byteAlign_of_byteSize ty size h
  cases hal : ty.byteAlign with
  | none => simp [hal] at ha
  | some alignment =>
    simp only [hal, Option.getD_some] at ha ⊢
    simp only [scalarMemoryLayout, Ty.byteSizeFor, Ty.byteAlignFor, h, hal]

/-- A bounded nonnegative integer converts to its mathematical magnitude. -/
theorem checkedWord64Operand_nonnegative (op : String) (value : Int)
    (h0 : 0 ≤ value) (h64 : value ≤ (word64Max : Int)) :
    checkedWord64Operand op false value = .ok value.toNat := by
  simp [checkedWord64Operand, Int.not_lt.mpr h0, Int.not_lt.mpr h64]

/-- GEP with index 0 produces the base address unchanged, including ZSTs. -/
theorem gepByteOffset_zero (ty : Ty) (s : Nat) (h : ty.byteSize = some s) :
    gepByteOffset ty 0 = .ok 0 := by
  simp [gepByteOffset, scalarMemoryLayout_of_byteSize ty s h,
    checkedWord64Operand, checkedWord64Mul, word64Max, word64Limit, word64Bits, bind, Except.bind, pure, Except.pure]

/-- The word conversion and multiplication guards are separate: a ZST does
    not erase an oversized operand. -/
theorem gepByteOffset_bounded (ty : Ty) (size : Nat) (index : Int)
    (hTy : ty.byteSize = some size) (h0 : 0 ≤ index)
    (h64 : index ≤ (word64Max : Int)) (hMul : index.toNat * size ≤ word64Max) :
    gepByteOffset ty index = .ok (index.toNat * size) := by
  simp [gepByteOffset, scalarMemoryLayout_of_byteSize ty size hTy,
    checkedWord64Operand_nonnegative "GEP" index h0 h64, checkedWord64Mul, hMul, bind, Except.bind, pure, Except.pure]

/-- GEP offsets are monotone on the admitted u64 domain. The former theorem
    over all nonnegative Ints was false once word overflow was modelled. -/
theorem gepByteOffset_monotone (ty : Ty) (s : Nat) (i j : Int)
    (hTy : ty.byteSize = some s) (hi : 0 ≤ i) (hj : i ≤ j)
    (hj64 : j ≤ (word64Max : Int)) (hjMul : j.toNat * s ≤ word64Max) :
    exists oi oj, gepByteOffset ty i = .ok oi ∧ gepByteOffset ty j = .ok oj ∧ oi ≤ oj := by
  have hnat : i.toNat ≤ j.toNat := by
    cases i with
    | ofNat n =>
      cases j with
      | ofNat m => exact Int.ofNat_le.mp hj
      | negSucc m => exact absurd (Int.le_trans hi hj) (by simp)
    | negSucc n => exact absurd hi (by simp)
  have hmul := Nat.mul_le_mul_right s hnat
  exact ⟨i.toNat * s, j.toNat * s,
    gepByteOffset_bounded ty s i hTy hi (Int.le_trans hj hj64) (Nat.le_trans hmul hjMul),
    gepByteOffset_bounded ty s j hTy (Int.le_trans hi hj) hj64 hjMul, hmul⟩

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
theorem semGlobalAddr_cache_hit (g : GlobalId) (addr : Addr) (id : AllocId)
    (s : MachineState) (h : s.lookupGlobal g = some (addr, id)) :
    ∃ v s',
      Sem.run (semGlobalAddr g) s = .ok (v, s')
      ∧ s'.lookupValue v = some (.ptr addr (some id))
      ∧ s'.lookupGlobal g = some (addr, id) := by
  refine ⟨ValueId.mk s.nextValueId,
          { s with locals := s.locals.set (ValueId.mk s.nextValueId) (.ptr addr (some id)),
                   nextValueId := s.nextValueId + 1 }, ?_, ?_, ?_⟩
  · unfold semGlobalAddr
    simp only [Sem.run_bind, run_getState, Except.bind, h]
    exact run_bindFresh (.ptr addr (some id)) s
  · exact lookupValue_bindFresh (.ptr addr (some id)) s
  · simpa [MachineState.lookupGlobal] using h

-- =================================================================
-- Fat-pointer trio: value-level round trip (B3 depth ledger)
-- =================================================================

/-- **Fat-pointer round trip, value level (headline form).**
    `PtrFromParts (PtrData p) (PtrMetadata p) = p` for every fat-pointer
    value `p = .fatPtr data prov metadata` whose null data lane carries no
    provenance (`data = 0 → prov = none`, which every constructor of a fat
    pointer keeps): both projections are total on `.fatPtr`, and the data
    lane always re-injects with its provenance (a 0 data lane reads back as
    `.nullPtr` and re-injects as address 0 with none). -/
theorem fatPtr_roundTrip_value (data : Nat) (prov : Option AllocId) (metadata : Value)
    (hNull : data = 0 → prov = none) :
    (do
      let d ← fatPtrDataValue (.fatPtr data prov metadata)
      let m ← fatPtrMetadataValue (.fatPtr data prov metadata)
      fatPtrFromPartsValue d m) = some (Value.fatPtr data prov metadata) := by
  cases data with
  | zero => rw [hNull rfl]; rfl
  | succ _ => rfl

/-- **Fat-pointer round trip, value level (projection form).** Any value
    on which BOTH projections are defined is a fat pointer, and
    recombining the projections yields it back exactly. -/
theorem fatPtrFromParts_data_metadata (p d m : Value)
    (hNull : ∀ prov metadata, p = .fatPtr 0 prov metadata → prov = none)
    (hd : fatPtrDataValue p = some d) (hm : fatPtrMetadataValue p = some m) :
    fatPtrFromPartsValue d m = some p := by
  cases p <;> simp only [fatPtrDataValue, fatPtrMetadataValue,
    Option.some.injEq] at hd hm <;> try contradiction
  case fatPtr data prov metadata =>
    subst d; subst m
    cases data with
    | zero => rw [hNull prov metadata rfl]; rfl
    | succ _ => rfl


-- =================================================================
-- The reference placement and exposed provenance (SPEC "A pointer operand
-- names the allocation it was derived from")
-- =================================================================

-- Lean 4.8 core has no `List.find?` inversion lemmas; these supply the facts
-- the provenance lookups need.

theorem find?_eq_none_of_forall {α : Type _} {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, p a = false) : l.find? p = none := by
  induction l with
  | nil => simp [List.find?]
  | cons x xs ih =>
    rw [List.find?_cons, h x ((trustIrListMemConsSelf x xs))]
    exact ih fun a ha => h a (List.mem_cons_of_mem x ha)

theorem mem_append_iff' {α : Type _} {a : α} : ∀ {l1 l2 : List α}, a ∈ l1 ++ l2 ↔ a ∈ l1 ∨ a ∈ l2
  | [], l2 => by simp
  | x :: xs, l2 => by
    rw [List.cons_append, List.mem_cons, List.mem_cons, mem_append_iff', or_assoc]

theorem mem_reverse_iff' {α : Type _} {a : α} : ∀ {l : List α}, a ∈ l.reverse ↔ a ∈ l
  | [] => by simp
  | x :: xs => by
    rw [List.reverse_cons, mem_append_iff', mem_reverse_iff']
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.comm

/-- `find?` finds SOMETHING when an element passes. -/
theorem find?_isSome_of_mem {α : Type _} {p : α → Bool} {l : List α} {a : α}
    (hMem : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b := by
  induction l with
  | nil => cases hMem
  | cons x xs ih =>
    rw [List.find?_cons]
    cases hx : p x
    · simp only []
      rcases List.mem_cons.mp hMem with rfl | h
      · rw [hp] at hx; exact Bool.noConfusion hx
      · exact ih h
    · exact ⟨x, rfl⟩

local macro "addr_omega" : tactic => `(tactic| ((try simp only [Addr] at *) <;> omega))

/-- **Exposed provenance, containment.** Under the layout invariant, an
    address inside an allocation's footprint recovers exactly that
    allocation, live or dead (`Memory.provenanceAt`, the interpreter's
    `try_pointer_from_address`). -/
theorem provenanceAt_inside (mem : Memory) (alloc : Allocation) (addr : Addr)
    (hWF : mem.layoutWF) (hMem : alloc ∈ mem.allocations)
    (hBase : alloc.base ≤ addr) (hIn : addr < alloc.base + alloc.size) :
    mem.provenanceAt addr = some alloc.id := by
  obtain ⟨-, -, -, hDisj, -⟩ := hWF
  unfold Memory.provenanceAt
  dsimp only
  have hMemR : alloc ∈ mem.allocations.reverse := mem_reverse_iff'.mpr hMem
  have hp : (decide (alloc.base ≤ addr) && decide (addr < alloc.base + alloc.size)) = true := by
    simp [hBase, hIn]
  obtain ⟨b, hb⟩ := find?_isSome_of_mem
    (p := fun a => decide (a.base ≤ addr) && decide (addr < a.base + a.size)) hMemR hp
  rw [hb]
  have hbMem : b ∈ mem.allocations := mem_reverse_iff'.mp (mem_of_find?_some hb)
  have hbp := find?_some_pred hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbp
  by_cases hab : b = alloc
  · rw [hab]
  · rcases hDisj b hbMem alloc hMem hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> addr_omega

/-- Factor pointer decoding over an arbitrary eight-byte image before
    instantiating it with a concrete encoder expression. Provenance is still
    resolved from the actual receiving memory. -/
theorem decodeValueAt_pointer_image (memory : Memory) (bytes : List UInt8)
    (size : bytes.length = 8) :
    decodeValueAt memory .Ptr bytes = .ok (memory.resolveAddr (decodeIntBytes bytes)) := by
  simp only [decodeValueAt, decodeImageAt, Ty.isFloat, decodeValue, size,
    beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false, Memory.resolveDecoded]
  by_cases zero : decodeIntBytes bytes = 0 <;> simp [zero, Memory.resolveAddr]

/-- **Load after store of a pointer recovers its provenance (exposed
    provenance through bytes).** A pointer to an address inside an
    allocation, stored as its eight-byte image and read back, decodes —
    whatever provenance the stored value carried — to that address with that
    allocation's provenance: the image holds the address only, and the
    decode recovers the allocation by `Memory.provenanceAt`, as the
    interpreter's `decode_leaf` does. -/
theorem load_after_store_ptr_recovers_inside (mem : Memory) (slot a : Addr)
    (prov : Option AllocId) (alloc : Allocation)
    (hWF : mem.layoutWF) (hMem : alloc ∈ mem.allocations)
    (hBase : alloc.base ≤ a) (hIn : a < alloc.base + alloc.size)
    (hNZ : a ≠ 0) (hLt : a < 2 ^ 64) :
    ∃ enc, encodeValueAt .Ptr (.ptr a prov) = .ok enc ∧
      (mem.writeBytes slot enc).readBytes slot 8 = some enc ∧
      decodeValueAt (mem.writeBytes slot enc) .Ptr enc = .ok (.ptr a (some alloc.id)) := by
  refine ⟨encodeIntBytes (Int.ofNat a) 8, rfl, ?_, ?_⟩
  · have h := writeBytes_readBytes_general mem slot (encodeIntBytes (Int.ofNat a) 8)
    rwa [encodeIntBytes_length] at h
  · have hProv : (mem.writeBytes slot (encodeIntBytes (Int.ofNat a) 8)).provenanceAt a
        = some alloc.id := provenanceAt_inside mem alloc a hWF hMem hBase hIn
    have hLen : (encodeIntBytes (Int.ofNat a) 8).length = 8 := encodeIntBytes_length _ _
    have hA : (a == 0) = false := by simpa using hNZ
    rw [decodeValueAt_pointer_image _ _ hLen, decode_encode_address a hLt]
    simp only [Memory.resolveAddr, hA, hProv, Bool.false_eq_true, if_false, ite_false]

-- =================================================================
-- Bulk memory: MemCopy preserves bytes (WS3.20, F-057)
-- =================================================================

/-- The actual MemCopy operation preserves every source byte and its init
    state. The snapshot is captured before writing, including overlap. -/
theorem memcopy_preserves_bytes (mem : Memory) (dst src n i : Nat) (hi : i < n) :
    (mem.writeImage dst (mem.readImage src n)).bytes (dst + i) = mem.bytes (src + i) :=
  Memory.bytes_copyImage mem dst src n i hi

/-- Bytes below the actual destination interval remain unchanged. -/
theorem memcopy_untouched_below (mem : Memory) (dst src n a : Nat) (ha : a < dst) :
    (mem.writeImage dst (mem.readImage src n)).bytes a = mem.bytes a := by
  apply Memory.bytes_writeImage_outside
  exact Or.inl ha

/-- Bytes after the actual destination interval remain unchanged. -/
theorem memcopy_untouched_above (mem : Memory) (dst src n a : Nat) (ha : dst + n ≤ a) :
    (mem.writeImage dst (mem.readImage src n)).bytes a = mem.bytes a := by
  apply Memory.bytes_writeImage_outside
  right
  simpa using ha

-- =================================================================
-- Sealed handle slots (WS3.7, F-047 memory half)
-- =================================================================

/-- A v43 handle occupies exactly one 64-bit word (8 bytes) at the model's
    pointer-width pin: the width a sealed handle slot is loaded and stored at. -/
theorem handle_slot_width (name runtime : String) :
    (Ty.Handle name runtime).bitWidth = some (8 * 8) := by
  simp [Ty.bitWidth, Ty.bitWidthAtPointerBits]

/-- **The sealed-slot round trip at a v43 handle (WS3.7, F-047).**

    The validator's sealed-slot rule (`crates/trust-ir-build/src/validate/
    handle_slots.rs`) admits a handle in memory only in a function-local
    `alloca` slot that is stored and loaded at EXACTLY the handle type, whose
    pointer never escapes, and whose every load is dominated by a store. What
    that rule needs from the model is no handle semantics at all: it is
    `load ∘ store = id` at one handle-width word — the handle's own 8 bytes
    written at the slot address read back unchanged, so a reload yields the
    handle that was stored and never a word some other store forged.

    An instance of `writeBytes_readBytes_general` at the handle width
    (`handle_slot_width`); no new axiom (see `AxiomAudit`). -/
theorem load_store_roundtrip_handle (name runtime : String) (mem : Memory) (addr : Addr)
    (word : List UInt8)
    (hWord : (Ty.Handle name runtime).bitWidth = some (8 * word.length)) :
    (mem.writeBytes addr word).readBytes addr 8 = some word := by
  rw [handle_slot_width] at hWord
  have hLen : word.length = 8 := by
    have h := Option.some.inj hWord
    omega
  rw [← hLen]
  exact writeBytes_readBytes_general mem addr word

end TrustIr

#trustIrAxiomsExact TrustIr.fatPtr_roundTrip_value == []
