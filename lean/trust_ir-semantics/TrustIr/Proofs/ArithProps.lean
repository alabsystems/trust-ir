-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Arithmetic properties: commutativity, associativity, etc.
-- Phase 1 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 1

import TrustIr.Semantics.Arith
import TrustIr.Semantics.Compare

namespace TrustIr

/-!
# Arithmetic Properties

These theorems establish key algebraic properties of TrustIr's arithmetic
instructions. They are the Phase 1 proof deliverables.

## Proved properties

1. Integer addition commutativity
2. Integer multiplication commutativity
3. Bitwise AND/OR/XOR commutativity
4. ICmpOp double negation (in CmpOp.lean)
5. Truncate-unsigned is idempotent

## Design note

These proofs operate on the pure functions (semIntBinOp, truncateUnsigned)
rather than the monadic wrappers (semBinOp). This keeps the proofs
clean and composable. Lifting to the monadic level is mechanical.
-/

-- =================================================================
-- Commutativity
-- =================================================================

/-- Integer addition wraps around `2^width`, so `a + b ≡ b + a (mod 2^w)`.
    This is the wrapping addition commutativity theorem. -/
theorem add_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Add width a b = semIntBinOp .Add width b a := by
  simp [semIntBinOp, Int.add_comm]

/-- Integer multiplication commutativity under modular arithmetic. -/
theorem mul_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Mul width a b = semIntBinOp .Mul width b a := by
  simp [semIntBinOp, Int.mul_comm]

/-- Bitwise AND commutativity. -/
theorem and_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .And width a b = semIntBinOp .And width b a := by
  simp [semIntBinOp, Int.land_comm]

/-- Bitwise OR commutativity. -/
theorem or_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Or width a b = semIntBinOp .Or width b a := by
  simp [semIntBinOp, Int.lor_comm]

/-- Bitwise XOR commutativity. -/
theorem xor_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Xor width a b = semIntBinOp .Xor width b a := by
  simp [semIntBinOp, Int.xor_comm]

-- =================================================================
-- Truncation properties
-- =================================================================

/-- Truncating an already-truncated value is idempotent.
    truncateUnsigned (truncateUnsigned v w) w = truncateUnsigned v w -/
theorem truncate_idempotent (v : Int) (w : Nat) :
    truncateUnsigned (truncateUnsigned v w) w = truncateUnsigned v w := by
  simp [truncateUnsigned, Int.emod_emod_of_dvd]

-- =================================================================
-- Division safety
-- =================================================================

/-- Unsigned division by nonzero always succeeds. -/
theorem udiv_nonzero_ok (width : Nat) (a b : Int) (hb : b ≠ 0) :
    ∃ r, semIntBinOp .UDiv width a b = .ok r := by
  simp [semIntBinOp, hb]

/-- Signed division by a nonzero divisor succeeds **except** for the one
    overflowing case `INT_MIN / -1`, which is undefined behavior (matches the
    Rust reference interpreter and LLVM `sdiv`; see docs/ub-numerics-policy.md
    §1). The `hov` hypothesis is exactly the `NoOverflow` obligation a frontend
    must discharge for an unconstrained signed division. -/
theorem sdiv_nonzero_ok (width : Nat) (a b : Int) (hb : b ≠ 0)
    (hov : ¬(toSigned a width = -((2 : Int) ^ (width - 1)) ∧ toSigned b width = -1)) :
    ∃ r, semIntBinOp .SDiv width a b = .ok r := by
  have hb' : (b == 0) = false := by simpa using hb
  simp only [semIntBinOp, hb', Bool.false_eq_true, if_false]
  split
  · rename_i hbad
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hbad
    exact absurd hbad hov
  · exact ⟨_, rfl⟩

-- =================================================================
-- Future work stubs (Phase 1 completeness claims)
-- =================================================================

/-
## Theorems to prove in subsequent iterations

1. **Associativity of wrapping addition:**
   `semIntBinOp .Add w (semIntBinOp .Add w a b) c = semIntBinOp .Add w a (semIntBinOp .Add w b c)`
   Requires extracting the .ok value from the Except.

2. **Cast round-trip (ZExt after Trunc):**
   When upper bits are zero and n <= m:
   `semCast .ZExt n m (semCast .Trunc m n x) = semCast .ZExt n m x`

3. **Determinism (trivially true for pure instructions):**
   `stepInst inst s = stepInst inst s`

4. **Progress (well-typed pure instructions always produce a result):**
   For well-typed arithmetic instructions, stepInst never returns typeError.
-/

-- =================================================================
-- Two-result binding (WS2.24)
-- =================================================================

/-- `semOverflow` over same-width integer operands IS `bindFreshPair` of its two
    components: the wrapped result and the overflow flag are bound as SEPARATE
    SSA values (the Rust `InstrNode.results = [%v, %o]` shape). There is no
    packed `Value.aggregate`, so no projection appears in the statement. -/
theorem semOverflow_eq_bindFreshPair (op : OverflowOp) (ty : Ty)
    (lhsId rhsId : ValueId) (s : MachineState) (w : Nat) (l r res : Int)
    (flag : Bool)
    (hl : s.lookupValue lhsId = some (.int w l))
    (hr : s.lookupValue rhsId = some (.int w r))
    (hop : semOverflowOp op w ty.isSigned l r = .ok (res, flag)) :
    Sem.run (semOverflow op ty lhsId rhsId) s =
      Sem.run (Sem.bindFreshPair (.int w res) (.bool flag)) s := by
  simp [semOverflow, Sem.run, StateT.run, Sem.lookupValue, Sem.getState,
    StateT.get, Sem.rejectPartial, bind, StateT.bind, Except.bind, pure,
    StateT.pure, Except.pure, hl, hr, hop]

/-- The overflow components land in two DISTINCT destinations, each holding
    exactly its own value: `%v = wrap(l op r)`, `%o = flag`. -/
theorem semOverflow_binds_components (op : OverflowOp) (ty : Ty)
    (lhsId rhsId : ValueId) (s : MachineState) (w : Nat) (l r res : Int)
    (flag : Bool)
    (hl : s.lookupValue lhsId = some (.int w l))
    (hr : s.lookupValue rhsId = some (.int w r))
    (hop : semOverflowOp op w ty.isSigned l r = .ok (res, flag)) :
    ∃ ids s', Sem.run (semOverflow op ty lhsId rhsId) s = .ok (ids, s') ∧
      ids.1 ≠ ids.2 ∧ s'.lookupValue ids.1 = some (.int w res) ∧
      s'.lookupValue ids.2 = some (.bool flag) := by
  rw [semOverflow_eq_bindFreshPair op ty lhsId rhsId s w l r res flag hl hr hop]
  exact ⟨_, _, Sem.run_bindFreshPair _ _ _,
    Sem.bindFreshPair_ok (Sem.run_bindFreshPair _ _ _)⟩

/-- Concrete instance of the Rust-shaped node `%v, %o = add_overflow i8 127, 1`:
    `%v` is `-128` (residue `128`) and `%o` is `true`. -/
theorem add_overflow_i8_127_1 :
    semOverflowOp .AddOverflow 8 true 127 1 = .ok (128, true) := by
  rfl

/-- The complete Bool comparison truth table. Signed order reads true as the
    one-bit value `-1`; unsigned order reads it as `1`. -/
theorem semBoolICmp_spec (op : ICmpOp) (lhs rhs : Bool) :
    semBoolICmp op lhs rhs =
      match op with
      | .Eq => lhs == rhs
      | .Ne => lhs != rhs
      | .Ult => !lhs && rhs
      | .Ule => !lhs || rhs
      | .Ugt => lhs && !rhs
      | .Uge => lhs || !rhs
      | .Slt => lhs && !rhs
      | .Sle => lhs || !rhs
      | .Sgt => !lhs && rhs
      | .Sge => !lhs || rhs := by
  cases op <;> cases lhs <;> cases rhs <;> decide

/-- Every well-typed Bool vector comparison returns exactly the corresponding
    lane predicates in source order, for arbitrary matching lane counts. -/
theorem semVectorBoolICmp_map (op : ICmpOp) (lhs rhs : List Bool)
    (h : lhs.length = rhs.length) :
    semVectorBoolICmp op (lhs.map Value.bool) (rhs.map Value.bool) =
      .ok (lhs.zipWith (fun l r => Value.bool (semBoolICmp op l r)) rhs) := by
  induction lhs generalizing rhs with
  | nil =>
    cases rhs with
    | nil => rfl
    | cons r rs => simp only [List.length_nil, List.length_cons] at h <;> omega
  | cons l ls ih =>
    cases rhs with
    | nil => simp only [List.length_nil, List.length_cons] at h <;> omega
    | cons r rs =>
      have htail : ls.length = rs.length := Nat.succ.inj h
      simp [semVectorBoolICmp, icmpBoolValue, ih rs htail, bind, pure, Except.bind, Except.pure]

/-- Integer vector comparison likewise traverses arbitrary matching lists,
    retaining each lane's declared width and source position. -/
theorem semVectorICmp_map (op : ICmpOp) (width : Nat) (lhs rhs : List Int)
    (h : lhs.length = rhs.length) :
    semVectorICmp op width (lhs.map (Value.int width)) (rhs.map (Value.int width)) =
      .ok (lhs.zipWith (fun l r => Value.bool (semICmp op width l r)) rhs) := by
  induction lhs generalizing rhs with
  | nil =>
    cases rhs with
    | nil => rfl
    | cons r rs => simp only [List.length_nil, List.length_cons] at h <;> omega
  | cons l ls ih =>
    cases rhs with
    | nil => simp only [List.length_nil, List.length_cons] at h <;> omega
    | cons r rs =>
      have htail : ls.length = rs.length := Nat.succ.inj h
      simp [semVectorICmp, icmpIntValue, ih rs htail, bind, pure, Except.bind, Except.pure]

/-- Scalar checked Bool comparison implements the same truth table. -/
theorem semICmpValues_bool (op : ICmpOp) (lhs rhs : Bool) (model : ByteModel) :
    semICmpValues op .Bool (.bool lhs) (.bool rhs) model =
      .ok (.bool (semBoolICmp op lhs rhs)) := by
  rfl

/-- The checked instruction-level value rule admits every positive Bool
    vector census and returns the exact lane predicates. -/
theorem semICmpValues_boolVector (op : ICmpOp) (lhs rhs : List Bool)
    (hn : lhs.length ≠ 0) (h : lhs.length = rhs.length) (model : ByteModel) :
    semICmpValues op (.Vector lhs.length .Bool)
        (.vector (lhs.map Value.bool)) (.vector (rhs.map Value.bool)) model =
      .ok (.vector (lhs.zipWith (fun l r => Value.bool (semBoolICmp op l r)) rhs)) := by
  have hnRight : rhs.length ≠ 0 := by rw [← h]; exact hn
  simp [semICmpValues, List.length_map, hn, hnRight, h,
    semVectorBoolICmp_map op lhs rhs h, bind, pure, Except.bind, Except.pure]

end TrustIr
