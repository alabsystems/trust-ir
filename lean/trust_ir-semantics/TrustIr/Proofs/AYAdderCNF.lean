-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYGateCNF

namespace TrustIr.AYGateCNF

/-- One cell records its operands, sum and outgoing carry ids. -/
structure AdderCell where
  left : Nat
  right : Nat
  sum : Nat
  outputCarry : Nat
  deriving Repr

/-- Concrete little-endian ripple topology. The preceding carry wire supplies
this cell's carry input; each cell supplies the next cell's input carry. -/
structure Adder where
  inputCarry : Nat
  cells : List AdderCell
  deriving Repr

def Adder.nil (carry : Nat) : Adder := ⟨carry, []⟩

def Adder.cons (left right sum carry : Nat) (tail : Adder) : Adder :=
  ⟨carry, ⟨left, right, sum, tail.inputCarry⟩ :: tail.cells⟩

theorem Adder.induction {motive : Adder → Prop}
    (nil : ∀ carry, motive (Adder.nil carry))
    (cons : ∀ left right sum carry tail, motive tail →
      motive (Adder.cons left right sum carry tail)) (adder : Adder) : motive adder := by
  rcases adder with ⟨carry, cells⟩
  induction cells generalizing carry with
  | nil => exact nil carry
  | cons cell rest ih =>
    rcases cell with ⟨left, right, sum, nextCarry⟩
    exact cons left right sum carry ⟨nextCarry, rest⟩ (ih nextCarry)

def Adder.outputCarry (adder : Adder) : Nat :=
  adder.cells.foldl (fun _ cell => cell.outputCarry) adder.inputCarry

def Adder.width (adder : Adder) : Nat := adder.cells.length

def Adder.leftValue (env : Assignment) (adder : Adder) : Nat :=
  adder.cells.foldr (fun cell rest => (env cell.left).toNat + 2 * rest) 0

def Adder.rightValue (env : Assignment) (adder : Adder) : Nat :=
  adder.cells.foldr (fun cell rest => (env cell.right).toNat + 2 * rest) 0

def Adder.sumValue (env : Assignment) (adder : Adder) : Nat :=
  adder.cells.foldr (fun cell rest => (env cell.sum).toNat + 2 * rest) 0

def Adder.gates (adder : Adder) : List Gate :=
  adder.cells.foldr (fun cell rest carry =>
    .xor3 cell.sum cell.left cell.right carry ::
      .fullAdderCarry cell.outputCarry cell.left cell.right carry :: rest cell.outputCarry)
    (fun _ => []) adder.inputCarry

/-- Every satisfying assignment of the concrete CNF is exact addition with
carry, at every width and for every wiring (aliases included). -/
theorem Adder.encode_numeric (adder : Adder) (env : Assignment)
    (model : CNF.eval env (encode adder.gates) = true) :
    adder.leftValue env + adder.rightValue env + (env adder.inputCarry).toNat =
      adder.sumValue env + 2 ^ adder.width * (env adder.outputCarry).toNat := by
  induction adder using Adder.induction with
  | nil carry => simp [Adder.leftValue, Adder.rightValue, Adder.sumValue,
      Adder.nil, Adder.outputCarry, Adder.width, List.foldr, List.foldl]
  | cons left right sum carry tail ih =>
    have equations := (encode_correct _ env).mp model
    have sumEq := equations _ (List.Mem.head _)
    have carryEq := equations _ (List.Mem.tail _ (List.Mem.head _))
    change env sum = xor (xor (env left) (env right)) (env carry) at sumEq
    change env tail.inputCarry =
      ((env left && env right) || (env carry && xor (env left) (env right))) at carryEq
    have rest : CNF.eval env (encode tail.gates) = true := by
      apply (encode_correct _ env).mpr
      intro gate member
      exact equations gate (List.Mem.tail _ (List.Mem.tail _ member))
    have tailEq := ih rest
    have bitEq := fullAdder_numeric (env left) (env right) (env carry)
    rw [← sumEq, ← carryEq] at bitEq
    change (env left).toNat + 2 * tail.leftValue env +
      ((env right).toNat + 2 * tail.rightValue env) + (env carry).toNat =
      (env sum).toNat + 2 * tail.sumValue env +
        2 ^ (tail.width + 1) * (env tail.outputCarry).toNat
    calc
      _ = (env sum).toNat + 2 * (tail.leftValue env + tail.rightValue env +
          (env tail.inputCarry).toNat) := by omega
      _ = (env sum).toNat + 2 * (tail.sumValue env +
          2 ^ tail.width * (env tail.outputCarry).toNat) := by rw [tailEq]
      _ = _ := by simp [Nat.pow_succ, Nat.mul_add, Nat.add_assoc,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The CNF's full carry equation implies the native modular word result. -/
theorem Adder.encode_word (adder : Adder) (env : Assignment)
    (model : CNF.eval env (encode adder.gates) = true) :
    BitVec.ofNat adder.width
      (adder.leftValue env + adder.rightValue env + (env adder.inputCarry).toNat) =
      BitVec.ofNat adder.width (adder.sumValue env) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, adder.encode_numeric env model]
  simp [Nat.add_mod, Nat.mul_mod]

/-- The concrete gate CNF enforces native core word addition, including carry-in. -/
theorem Adder.encode_native_add (adder : Adder) (env : Assignment)
    (model : CNF.eval env (encode adder.gates) = true) :
    (BitVec.ofNat adder.width (adder.leftValue env) +
      BitVec.ofNat adder.width (adder.rightValue env)) +
      BitVec.ofNat adder.width (env adder.inputCarry).toNat =
      BitVec.ofNat adder.width (adder.sumValue env) := by
  simpa only [BitVec.ofNat_add] using adder.encode_word env model

end TrustIr.AYGateCNF

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.encode_numeric == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.encode_word == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Adder.encode_native_add == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
