-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYPopulationCount

namespace TrustIr.TrustIrExpr

inductive ZeroCountDirection where
  | leading | trailing
  deriving Repr, DecidableEq

def ZeroCountDirection.index (direction : ZeroCountDirection) (width iteration : Nat) : Nat :=
  match direction with
  | .leading => iteration
  | .trailing => width-1-iteration

theorem ZeroCountDirection.index_lt (direction : ZeroCountDirection) (width iteration : Nat)
    (bound : iteration < width) : direction.index width iteration < width := by
  cases direction <;> dsimp [ZeroCountDirection.index] <;> omega

/-- Independent natural-valued priority scan. No modular arithmetic occurs
in this definition; the initial width is the total all-zero answer. -/
def zeroScan (direction : ZeroCountDirection) (width value count : Nat) : Nat :=
  Nat.rec width (fun i previous =>
    if (value / 2^(direction.index width i)) % 2 == 1 then width-1-i else previous) count

theorem zeroScan_bound (direction : ZeroCountDirection) (width value count : Nat) :
    zeroScan direction width value count ≤ width := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    change (if (value/2^(direction.index width n))%2 == 1 then width-1-n else zeroScan direction width value n) ≤ width
    split <;> omega

theorem zeroScan_zero (direction : ZeroCountDirection) (width count : Nat) :
    zeroScan direction width 0 count = width := by
  induction count with
  | zero => rfl
  | succ i ih =>
    change (if (0/2^(direction.index width i))%2 == 1 then width-1-i else zeroScan direction width 0 i) = width
    simpa using ih

theorem zeroScan_leading (width value count : Nat) (bound : count ≤ width) :
    zeroScan .leading width value count = width-count+ctlzWidth value count := by
  induction count with
  | zero => change width = width-0+0; omega
  | succ n ih =>
    change (if (value/2^n)%2 == 1 then width-1-n else zeroScan .leading width value n) = _
    rw [ctlzWidth]
    split
    · omega
    · rw [ih (by omega)]; omega

theorem zeroScan_trailing (width value count : Nat) (bound : count ≤ width) :
    zeroScan .trailing width value count = width-count+cttzWidth (value/2^(width-count)) count := by
  induction count with
  | zero => change width = width-0+0; omega
  | succ n ih =>
    have pos : width-1-n = width-(n+1) := by omega
    have step : width-n = width-(n+1)+1 := by omega
    have shift : value / 2^(width-(n+1)) / 2 = value / 2^(width-n) := by
      rw [Nat.div_div_eq_div_mul, step, Nat.pow_succ]
    change (if (value/2^(width-1-n))%2 == 1 then width-1-n else zeroScan .trailing width value n) = _
    rw [pos, cttzWidth]
    split
    · omega
    · rw [shift, ih (by omega)]; omega

def ZeroCountDirection.number (direction : ZeroCountDirection) (value width : Nat) : Nat :=
  match direction with
  | .leading => ctlzWidth value width
  | .trailing => cttzWidth value width

theorem zeroScan_complete (direction : ZeroCountDirection) (width value : Nat) :
    zeroScan direction width value width = direction.number value width := by
  cases direction
  · simpa [ZeroCountDirection.number] using zeroScan_leading width value width (Nat.le_refl _)
  · simpa [ZeroCountDirection.number] using zeroScan_trailing width value width (Nat.le_refl _)

private theorem zero_count_capacity (width : Nat) (positive : 0 < width) : width < 2^width :=
  Nat.lt_of_lt_of_le (populationBits_capacity width)
    ((trustIrWidthLemma Nat.pow_le_pow_of_le_right Nat.pow_le_pow_right) (by decide) (populationBits_le width positive))

def SMTTerm.zeroBitSet {width : Nat} (word : SMTTerm (.bv width)) (index : Nat) (bound : index < width) :
    SMTTerm .bool :=
  .binary (.eq (.bv 1)) (word.chunk 1 (by decide) index (by omega)) (.bvConst 1 1)

theorem SMTTerm.zeroBitSet_eval {width : Nat} (word : SMTTerm (.bv width)) (index : Nat)
    (bound : index < width) (env : SMTEnv) :
    (word.zeroBitSet index bound).eval env = ((word.eval env).toNat/2^index%2 == 1) := by
  change decide (((word.chunk 1 (by decide) index (by omega)).eval env) = BitVec.ofInt 1 1) = _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
  rw [BitVec.toNat_eq, word.chunk_toNat]
  simp

/-- The exact Rust AY priority chain, using core recursion over its actual
iteration count. Every leaf extracts from the original word. -/
def SMTTerm.zeroCountScan {width : Nat} (word : SMTTerm (.bv width)) (direction : ZeroCountDirection) :
    (count : Nat) → count ≤ width → SMTTerm (.bv width) :=
  Nat.rec (motive := fun count => count ≤ width → SMTTerm (.bv width))
    (fun _ => .bvConst width (Int.ofNat width))
    (fun i previous bound =>
      let index := direction.index width i
      have indexed : index < width := by cases direction <;> dsimp [ZeroCountDirection.index, index] <;> omega
      .ite (word.zeroBitSet index indexed) (.bvConst width (Int.ofNat (width-1-i))) (previous (by omega)))

private theorem zero_count_const (width value : Nat) (small : value < 2^width) (env : SMTEnv) :
    ((SMTTerm.bvConst width (Int.ofNat value)).eval env).toNat = value := by
  change (BitVec.ofInt width (Int.ofNat value)).toNat = value
  rw [BitVec.toNat_ofInt]
  norm_cast
  exact Nat.mod_eq_of_lt small

theorem SMTTerm.zeroCountScan_toNat {width : Nat} (word : SMTTerm (.bv width))
    (direction : ZeroCountDirection) (positive : 0 < width) (count : Nat) (bound : count ≤ width) (env : SMTEnv) :
    ((word.zeroCountScan direction count bound).eval env).toNat = zeroScan direction width (word.eval env).toNat count := by
  induction count with
  | zero => exact zero_count_const width width (zero_count_capacity width positive) env
  | succ i ih =>
    change (BitVec.toNat (if (word.zeroBitSet (direction.index width i)
      (by cases direction <;> dsimp [ZeroCountDirection.index] <;> omega)).eval env then
        BitVec.ofInt width (Int.ofNat (width-1-i)) else
        (word.zeroCountScan direction i (by omega)).eval env)) = _
    rw [SMTTerm.zeroBitSet_eval]
    change (BitVec.toNat (if (word.eval env).toNat/2^(direction.index width i)%2 == 1 then _ else _)) =
      (if (word.eval env).toNat/2^(direction.index width i)%2 == 1 then width-1-i else zeroScan direction width (word.eval env).toNat i)
    split
    · exact zero_count_const width (width-1-i) (Nat.lt_of_le_of_lt (by omega) (zero_count_capacity width positive)) env
    · exact ih (by omega)

theorem SMTTerm.zeroBitSet_wellFormed {width : Nat} (word : SMTTerm (.bv width)) (index : Nat)
    (bound : index < width) (wellFormed : word.WellFormed) : (word.zeroBitSet index bound).WellFormed :=
  ⟨word.chunk_wellFormed 1 (by decide) index (by omega) wellFormed, by decide⟩

theorem SMTTerm.zeroBitSet_bindings {width : Nat} (word : SMTTerm (.bv width)) (index : Nat)
    (bound : index < width) : (word.zeroBitSet index bound).bindings = word.bindings := by
  change (word.chunk 1 (by decide) index (by omega)).bindings ++ [] = _
  rw [SMTTerm.chunk_bindings, List.append_nil]


theorem SMTTerm.zeroBitSet_boolBindings {width : Nat} (word : SMTTerm (.bv width)) (index : Nat)
    (bound : index < width) : (word.zeroBitSet index bound).boolBindings = word.boolBindings := by
  change (word.chunk 1 (by decide) index (by omega)).boolBindings ++ [] = _
  rw [SMTTerm.chunk_boolBindings, List.append_nil]

theorem SMTTerm.zeroCountScan_wellFormed {width : Nat} (word : SMTTerm (.bv width))
    (direction : ZeroCountDirection) (positive : 0 < width) (count : Nat) (bound : count ≤ width)
    (wellFormed : word.WellFormed) : (word.zeroCountScan direction count bound).WellFormed := by
  induction count with
  | zero => exact positive
  | succ i ih =>
    exact ⟨word.zeroBitSet_wellFormed _ (direction.index_lt width i (by omega)) wellFormed, positive, ih (by omega)⟩

theorem zeroBindings_cons {α : Type} (count : Nat) (bindings : List α) :
    permutationBindings (count+1) bindings = bindings ++ permutationBindings count bindings := by
  induction count with
  | zero => simp [permutationBindings]
  | succ n ih =>
    have commute : permutationBindings n bindings ++ bindings = bindings ++ permutationBindings n bindings :=
      (permutationBindings_snoc n bindings).symm.trans ih
    rw [permutationBindings_snoc (n+1), ih, List.append_assoc, commute]

theorem SMTTerm.zeroCountScan_bindings {width : Nat} (word : SMTTerm (.bv width))
    (direction : ZeroCountDirection) (count : Nat) (bound : count ≤ width) :
    (word.zeroCountScan direction count bound).bindings = permutationBindings count word.bindings := by
  induction count with
  | zero => rfl
  | succ i ih =>
    change (word.zeroBitSet (direction.index width i) (direction.index_lt width i (by omega))).bindings ++ [] ++
      (word.zeroCountScan direction i (by omega)).bindings = _
    rw [SMTTerm.zeroBitSet_bindings, List.append_nil, ih, zeroBindings_cons]


theorem SMTTerm.zeroCountScan_boolBindings {width : Nat} (word : SMTTerm (.bv width))
    (direction : ZeroCountDirection) (count : Nat) (bound : count ≤ width) :
    (word.zeroCountScan direction count bound).boolBindings = permutationBindings count word.boolBindings := by
  induction count with
  | zero => rfl
  | succ i ih =>
    change (word.zeroBitSet (direction.index width i) (direction.index_lt width i (by omega))).boolBindings ++ [] ++
      (word.zeroCountScan direction i (by omega)).boolBindings = _
    rw [SMTTerm.zeroBitSet_boolBindings, List.append_nil, ih, zeroBindings_cons]

/-- Checked construction retains the exact chain, with its inventory built in
one replication pass rather than repeatedly appended during the scan. -/
def SMTCheckedTerm.zeroCount {width : Nat} (word : SMTCheckedTerm (.bv width)) (direction : ZeroCountDirection) :
    Except String (SMTCheckedTerm (.bv width)) :=
  if positive : 0 < width then
    .ok ⟨word.term.zeroCountScan direction width (Nat.le_refl _), permutationBindings width word.bindings,
      word.term.zeroCountScan_wellFormed direction positive width (Nat.le_refl _) word.wellFormed,
      by rw [SMTTerm.zeroCountScan_bindings, word.inventory],
      permutationBindings width word.boolBindings,
      by rw [SMTTerm.zeroCountScan_boolBindings, word.boolInventory]⟩
  else .error "zero count of a zero-width bit-vector"

theorem SMTCheckedTerm.zeroCount_toNat {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (direction : ZeroCountDirection) (built : word.zeroCount direction = .ok result) (env : SMTEnv) :
    (result.term.eval env).toNat = direction.number (word.term.eval env).toNat width := by
  unfold SMTCheckedTerm.zeroCount at built
  split at built
  · rename_i positive
    cases built
    exact (word.term.zeroCountScan_toNat direction positive width (Nat.le_refl _) env).trans
      (zeroScan_complete direction width _)
  · contradiction

theorem SMTCheckedTerm.zeroCount_bound {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (direction : ZeroCountDirection) (built : word.zeroCount direction = .ok result) (env : SMTEnv) :
    (result.term.eval env).toNat ≤ width := by
  rw [word.zeroCount_toNat result direction built env, ← zeroScan_complete]
  exact zeroScan_bound _ _ _ _

theorem SMTCheckedTerm.zeroCount_zero {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (direction : ZeroCountDirection) (built : word.zeroCount direction = .ok result) (env : SMTEnv)
    (zero : (word.term.eval env).toNat = 0) : (result.term.eval env).toNat = width := by
  rw [word.zeroCount_toNat result direction built env, ← zeroScan_complete, zero]
  exact zeroScan_zero _ _ _

theorem SMTCheckedTerm.zeroCount_request {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (direction : ZeroCountDirection) (built : word.zeroCount direction = .ok result)
    (request : SMTTypedRequest (.bv width)) (requested : result.toTypedRequest = .ok request) (env : SMTEnv) :
    request.target = result.term ∧ request.target.WellFormed ∧
      (request.target.eval env).toNat = direction.number (word.term.eval env).toNat width := by
  have actual := result.toTypedRequest_admitted request requested
  exact ⟨actual.1, actual.2.1, by rw [actual.1]; exact word.zeroCount_toNat result direction built env⟩

def ZeroCountDirection.irOp : ZeroCountDirection → UnOp
  | .leading => .CtLz
  | .trailing => .CtTz

private theorem zero_count_wrappedNat (width : Nat) (operand : Int) :
    (((operand % (2 : Int)^width) + (2 : Int)^width) % (2 : Int)^width).toNat =
      (BitVec.ofInt width operand).toNat := by
  rw [BitVec.toNat_ofInt, Int.natCast_pow]
  simp [Int.add_emod, Int.emod_emod]

theorem SMTCheckedTerm.zeroCount_semIntUnOp {width : Nat} (word result : SMTCheckedTerm (.bv width))
    (direction : ZeroCountDirection) (built : word.zeroCount direction = .ok result) (operand : Int) (env : SMTEnv)
    (source : word.term.eval env = BitVec.ofInt width operand) :
    semIntUnOp direction.irOp width operand = .ok (Int.ofNat (result.term.eval env).toNat) := by
  rw [word.zeroCount_toNat result direction built env, source]
  cases direction <;> simp only [ZeroCountDirection.irOp, ZeroCountDirection.number, semIntUnOp, zero_count_wrappedNat]

end TrustIr.TrustIrExpr
