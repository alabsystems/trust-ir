-- Copyright 2026 Andrew Yates | Apache-2.0
-- Constructive bound witnesses for the same core BitVec OR/XOR functions.
-- The modern standard bound proof uses a higher-order unfolding equation.
-- Pointwise fuel induction avoids that dependency; whole-function equalities
-- below are rfl and retain the standard operations' own recorded dependencies.
import TrustIr.CompilerCompat
import Lean

macro "trustIrBitVec430 " declaration:command : command => do
  if Lean.versionString == "4.30.0-rc2" then pure declaration
  else if Lean.versionString == "4.8.0" then `(command| run_cmd pure ())
  else Lean.Macro.throwError "unsupported compiler for constructive BitVec bounds"
macro "trustIrBitVec48 " declaration:command : command => do
  if Lean.versionString == "4.8.0" then pure declaration
  else if Lean.versionString == "4.30.0-rc2" then `(command| run_cmd pure ())
  else Lean.Macro.throwError "unsupported compiler for constructive BitVec bounds"
open Lean Elab Tactic in
elab "trustIrUnfoldBitwiseUnary" : tactic => do
  let env ← getEnv
  let names := env.constants.toList.filter (fun p => p.1.toString.endsWith "Nat.bitwise._unary")
  unless names.length == 1 do throwError "expected one actual bitwise unary definition"
  let name := names.head!.1
  let ident := mkIdent name
  evalTactic (← `(tactic| delta $ident:ident))

namespace TrustIr.BitVecCompat
trustIrBitVec430 abbrev Pair := (_ : Nat) ×' Nat
trustIrBitVec430 def measure (p : Pair) : Nat := p.fst
trustIrBitVec430 def step (f : Bool → Bool → Bool) : (p : Pair) → ((q : Pair) → measure q < measure p → Nat) → Nat
  | ⟨n, m⟩, recur =>
    if hn : n = 0 then (if f false true then m else 0)
    else if m = 0 then (if f true false then n else 0)
    else
      let r := recur ⟨n / 2, m / 2⟩ (Nat.bitwise_rec_lemma hn)
      if f (decide (n % 2 = 1)) (decide (m % 2 = 1)) then r + r + 1 else r + r
trustIrBitVec430 def fuelBitwise (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, n, m =>
    if n = 0 then (if f false true then m else 0)
    else if m = 0 then (if f true false then n else 0)
    else
      let r := fuelBitwise f fuel (n / 2) (m / 2)
      if f (decide (n % 2 = 1)) (decide (m % 2 = 1)) then r + r + 1 else r + r
trustIrBitVec430 theorem actual_step (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m = WellFounded.Nat.fix measure (step f) ⟨n, m⟩ := by
  delta Nat.bitwise
  trustIrUnfoldBitwiseUnary
  rfl
trustIrBitVec430 theorem go_eq_fuel (f : Bool → Bool → Bool) (fuel n m : Nat) (enough : n < fuel) :
    WellFounded.Nat.fix.go measure (step f) fuel ⟨n, m⟩ enough = fuelBitwise f fuel n m := by
  induction fuel generalizing n m with
  | zero => exact (Nat.not_lt_zero _ enough).elim
  | succ fuel ih =>
    dsimp only [WellFounded.Nat.fix.go, fuelBitwise, step]
    by_cases hn : n = 0
    · simp only [hn, dif_pos, if_true]
    · simp only [hn, dif_neg, if_false]
      by_cases hm : m = 0
      · simp only [hm, dif_pos, if_true, ↓reduceDIte, ↓reduceIte]
      · simp only [hm, dif_neg, if_false, ↓reduceDIte, ↓reduceIte]
        exact congrArg
          (fun r : Nat => if f (decide (n % 2 = 1)) (decide (m % 2 = 1)) then r + r + 1 else r + r)
          (ih (n / 2) (m / 2) (Nat.lt_of_lt_of_le (Nat.bitwise_rec_lemma hn) (Nat.le_of_lt_succ enough)))
trustIrBitVec430 theorem actual_eq_fuel (f : Bool → Bool → Bool) (n m : Nat) :
    Nat.bitwise f n m = fuelBitwise f (n + 1) n m := by
  rw [actual_step]
  unfold WellFounded.Nat.fix
  simp only [WellFounded.Nat.eager_eq, measure]
  exact go_eq_fuel f (n + 1) n m (Nat.lt_succ_self n)
end TrustIr.BitVecCompat

namespace TrustIr.BitVecCompat
trustIrBitVec430 theorem fuel_bound (f : Bool → Bool → Bool) (fuel : Nat) {x y n : Nat}
    (left : x < 2 ^ n) (right : y < 2 ^ n) : fuelBitwise f fuel x y < 2 ^ n := by
  induction n generalizing fuel x y with
  | zero =>
    have hx : x = 0 := by simpa using left
    have hy : y = 0 := by simpa using right
    subst x; subst y
    cases fuel <;> simp [fuelBitwise]
  | succ n ih =>
    cases fuel with
    | zero => exact Nat.two_pow_pos _
    | succ fuel =>
      dsimp only [fuelBitwise]
      by_cases hx : x = 0
      · simp only [hx, if_true]
        split
        · exact right
        · exact Nat.two_pow_pos _
      · simp only [hx, if_false]
        by_cases hy : y = 0
        · simp only [hy, if_true]
          split
          · exact left
          · exact Nat.two_pow_pos _
        · simp only [hy, if_false]
          have halfLeft : x / 2 < 2 ^ n :=
            (Nat.div_lt_iff_lt_mul Nat.zero_lt_two).mpr (by simpa only [Nat.pow_succ] using left)
          have halfRight : y / 2 < 2 ^ n :=
            (Nat.div_lt_iff_lt_mul Nat.zero_lt_two).mpr (by simpa only [Nat.pow_succ] using right)
          have smaller := ih fuel halfLeft halfRight
          split
          · rw [Nat.pow_succ, Nat.mul_two]
            apply Nat.lt_of_succ_le
            simpa only [Nat.succ_add] using Nat.add_le_add smaller smaller
          · simpa only [Nat.pow_succ, Nat.mul_two] using Nat.add_lt_add smaller smaller
trustIrBitVec430 theorem bound (f : Bool → Bool → Bool) {x y n : Nat}
    (left : x < 2 ^ n) (right : y < 2 ^ n) : Nat.bitwise f x y < 2 ^ n := by
  rw [actual_eq_fuel]
  exact fuel_bound f (x + 1) left right
trustIrBitVec430 def bitOr {n : Nat} (x y : BitVec n) : BitVec n :=
  BitVec.ofNatLT (x.toNat ||| y.toNat) (bound Bool.or x.isLt y.isLt)
trustIrBitVec430 def bitXor {n : Nat} (x y : BitVec n) : BitVec n :=
  BitVec.ofNatLT (x.toNat ^^^ y.toNat) (bound (fun a b => a != b) x.isLt y.isLt)
trustIrBitVec430 theorem bitOr_eq_standard {n : Nat} (x y : BitVec n) : bitOr x y = BitVec.or x y := rfl
trustIrBitVec430 theorem bitXor_eq_standard {n : Nat} (x y : BitVec n) : bitXor x y = BitVec.xor x y := rfl
trustIrBitVec430 theorem bitOr_function_eq_standard (n : Nat) : @bitOr n = @BitVec.or n := rfl
trustIrBitVec430 theorem bitXor_function_eq_standard (n : Nat) : @bitXor n = @BitVec.xor n := rfl
end TrustIr.BitVecCompat

namespace TrustIr.BitVecCompat
trustIrBitVec48 abbrev bitOr {n : Nat} (x y : BitVec n) : BitVec n := x ||| y
trustIrBitVec48 abbrev bitXor {n : Nat} (x y : BitVec n) : BitVec n := x ^^^ y
trustIrBitVec48 theorem bitOr_eq_standard {n : Nat} (x y : BitVec n) : bitOr x y = BitVec.or x y := rfl
trustIrBitVec48 theorem bitXor_eq_standard {n : Nat} (x y : BitVec n) : bitXor x y = BitVec.xor x y := rfl
trustIrBitVec48 theorem bitOr_function_eq_standard (n : Nat) : @bitOr n = @BitVec.or n := rfl
trustIrBitVec48 theorem bitXor_function_eq_standard (n : Nat) : @bitXor n = @BitVec.xor n := rfl
 theorem toNat_bitOr {n : Nat} (x y : BitVec n) : (bitOr x y).toNat = x.toNat ||| y.toNat := rfl
 theorem toNat_bitXor {n : Nat} (x y : BitVec n) : (bitXor x y).toNat = x.toNat ^^^ y.toNat := rfl
#trustIrAxiomsExact bitOr == [propext]
#trustIrAxiomsExact bitXor == [propext]
#trustIrAxiomsExact toNat_bitOr == [propext]
#trustIrAxiomsExact toNat_bitXor == [propext]
trustIrBitVec430 #trustIrAxiomsExact actual_step == [propext]
trustIrBitVec430 #trustIrAxiomsExact go_eq_fuel == [propext]
trustIrBitVec430 #trustIrAxiomsExact actual_eq_fuel == [propext]
trustIrBitVec430 #trustIrAxiomsExact fuel_bound == [propext]
trustIrBitVec430 #trustIrAxiomsExact bound == [propext]
trustIrBitVec48 #trustIrAxiomsExact bitOr_function_eq_standard == [propext]
trustIrBitVec48 #trustIrAxiomsExact bitXor_function_eq_standard == [propext]
trustIrBitVec430 #trustIrAxiomsExact bitOr_function_eq_standard == [propext, Quot.sound]
trustIrBitVec430 #trustIrAxiomsExact bitXor_function_eq_standard == [propext, Quot.sound]
-- Complement uses the same all-ones XOR payload with the constructive witness.
trustIrBitVec430 def bitNot {n : Nat} (x : BitVec n) : BitVec n := bitXor (BitVec.allOnes n) x
trustIrBitVec48 abbrev bitNot {n : Nat} (x : BitVec n) : BitVec n := BitVec.not x
theorem bitNot_function_eq_standard (n : Nat) : @bitNot n = @BitVec.not n := rfl
#trustIrAxiomsExact bitNot == [propext]
trustIrBitVec48 #trustIrAxiomsExact bitNot_function_eq_standard == [propext]
trustIrBitVec430 #trustIrAxiomsExact bitNot_function_eq_standard == [propext, Quot.sound]
end TrustIr.BitVecCompat
