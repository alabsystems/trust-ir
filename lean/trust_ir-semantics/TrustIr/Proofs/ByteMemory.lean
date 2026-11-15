-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Memory

/-! Canonical byte-memory statements shared with the full memory library and
cross-version consumers. Proofs use authoritative image lookup laws, rather
than the removed per-byte closure-update implementation. -/

namespace TrustIr

/-- Writing zero bytes leaves lookup unchanged. -/
theorem writeBytes_nil (mem : Memory) (addr : Addr) :
    (mem.writeBytes addr []).bytes = mem.bytes := by rfl

theorem readBytes_zero (mem : Memory) (addr : Addr) :
    mem.readBytes addr 0 = some [] := by
  simp [Memory.readBytes, Memory.readBytes.go]

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

/-- Exact initialized-buffer round trip through the authoritative store. -/
theorem writeBytes_readBytes_general (mem : Memory) (addr : Addr) (data : List UInt8) :
    (mem.writeBytes addr data).readBytes addr data.length = some data := by
  unfold Memory.readBytes
  apply readBytes_go_from_bytes
  intro index inside
  exact Memory.bytes_writeBytes_inside mem addr index data inside

theorem writeBytes_readBytes_single (mem : Memory) (addr : Addr) (b : UInt8) :
    (mem.writeBytes addr [b]).readBytes addr 1 = some [b] :=
  writeBytes_readBytes_general mem addr [b]

/-- The latest write supplies every byte of its own read range. -/
theorem writeBytes_overwrite (mem : Memory) (addr : Addr) (data1 data2 : List UInt8)
    (_h : data1.length = data2.length) :
    (mem.writeBytes addr data1 |>.writeBytes addr data2).readBytes addr data2.length =
    (mem.writeBytes addr data2).readBytes addr data2.length := by
  rw [writeBytes_readBytes_general, writeBytes_readBytes_general]

/-- Disjoint writes preserve the complete read range. -/
theorem writeBytes_non_aliasing (mem : Memory) (addr1 addr2 : Addr)
    (n1 : Nat) (data2 : List UInt8)
    (hNoOverlap : addr1 + n1 <= addr2 \/ addr2 + data2.length <= addr1) :
    (mem.writeBytes addr2 data2).readBytes addr1 n1 = mem.readBytes addr1 n1 := by
  unfold Memory.readBytes
  apply readBytes_go_partial_ext
  intro address starts stops
  apply Memory.bytes_writeBytes_outside
  rcases hNoOverlap with before | after
  · exact Or.inl (Nat.lt_of_lt_of_le stops before)
  · exact Or.inr (Nat.le_trans after starts)

/-- encodeIntBytes produces exactly numBytes bytes. -/
theorem encodeIntBytes_length (val : Int) (numBytes : Nat) :
    (encodeIntBytes val numBytes).length = numBytes := by
  simp [encodeIntBytes]
  suffices h : forall n v, (encodeIntBytes.go n v).length = n from h numBytes val.toNat
  intro n
  induction n with
  | zero => intro _; simp [encodeIntBytes.go]
  | succ k ih => intro _; simp [encodeIntBytes.go, ih]


theorem uint8_toNat_ofNat_mod (v : Nat) : (UInt8.ofNat (v % 256)).toNat = v % 256 := by
  have h : v % 256 < 256 := Nat.mod_lt _ (by decide)
  simp [UInt8.ofNat, UInt8.toNat, Fin.ofNat, Nat.mod_eq_of_lt h]

theorem decode_encode_go (n v k : Nat) :
    decodeIntBytes.go (encodeIntBytes.go n v) k = 256 ^ k * (v % 256 ^ n) := by
  induction n generalizing v k with
  | zero => simp [encodeIntBytes.go, decodeIntBytes.go, Nat.mod_one]
  | succ n ih =>
    simp only [encodeIntBytes.go, decodeIntBytes.go]
    rw [ih, uint8_toNat_ofNat_mod]
    rw [show 256 ^ (n + 1) = 256 * 256 ^ n by rw [Nat.pow_succ, Nat.mul_comm], Nat.mod_mul,
      Nat.pow_succ, Nat.mul_add]
    ac_rfl

/-- A pointer word's eight-byte image decodes back to the address. -/
theorem decode_encode_address (a : Nat) (h : a < 2 ^ 64) :
    decodeIntBytes (encodeIntBytes (Int.ofNat a) 8) = a := by
  change decodeIntBytes.go (encodeIntBytes.go 8 a) 0 = a
  rw [decode_encode_go]
  simp only [Nat.pow_zero, Nat.one_mul]
  exact Nat.mod_eq_of_lt (by simpa using h)

end TrustIr
