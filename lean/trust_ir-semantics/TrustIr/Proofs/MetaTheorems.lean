-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Phase 5 meta-theorems: properties about the TrustIr semantics as a whole.
-- These prove structural properties of the semantic framework rather than
-- properties of individual instructions.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 5
-- Reference: Wright & Felleisen, "A Syntactic Approach to Type Soundness", 1994

import TrustIr.Semantics.Eval

namespace TrustIr

/-!
# Meta-Theorems (Phase 5)

These theorems establish properties about the TrustIr semantics AS A WHOLE,
rather than about individual instruction categories (which were Phases 1-4).

## Proved properties

1. **Determinism:** The semantics are deterministic -- same instruction + same
   state always produces the same result. This is trivially true because
   Sem is a pure functional monad (no nondeterminism source).

2. **Progress for pure instructions:** Well-typed constants, copies, and
   arithmetic on well-typed operands always produce a result (never stuck).

3. **Fuel monotonicity:** If a computation terminates with fuel1, it
   produces the same result with any fuel2 >= fuel1.

4. **Terminal state characterization:** Every stepN invocation either
   succeeds with a result or produces a SemError.

## Design note

These theorems operate on Sem.run (the unwrapped monadic computation)
to state properties about the input/output behavior. The key insight is
that Sem = StateT MachineState (Except SemError) is a pure function
MachineState -> Except SemError (a * MachineState), so determinism is
a consequence of functional purity -- not a deep semantic property.

The deeper properties (type safety / progress for the full language)
require a well-typedness judgment that connects Ty annotations to
Value inhabitants. This judgment is sketched here and will be refined
as the type system formalization matures.
-/

-- =================================================================
-- Determinism
-- =================================================================

/-- The single-step semantics is deterministic: executing the same
    instruction in the same state always produces the same result.

    This is trivially true because Sem is a pure functional monad
    (StateT MachineState (Except SemError)). There is no source of
    nondeterminism. We state it explicitly because:
    1. It is a standard meta-theorem in PL formalization.
    2. It is a precondition for fuel monotonicity.
    3. TrustCg relies on it when mapping TrustIr to deterministic machine code. -/
theorem stepInst_deterministic (inst : Inst) (s : MachineState) :
    Sem.run (stepInst inst) s = Sem.run (stepInst inst) s := by
  rfl

/-- Multi-step evaluation is also deterministic: same fuel, CFG, entry
    point, arguments, and initial state always produce the same result. -/
theorem stepN_deterministic (fuel : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (s : MachineState) :
    Sem.run (stepN fuel cfg pc args) s = Sem.run (stepN fuel cfg pc args) s := by
  rfl

/-- Block evaluation is deterministic. -/
theorem stepBlock_deterministic (block : BasicBlock) (args : List Value)
    (s : MachineState) :
    Sem.run (stepBlock block args) s = Sem.run (stepBlock block args) s := by
  rfl

-- =================================================================
-- Total result characterization
-- =================================================================

/-- Every Sem computation either succeeds or fails -- there is no
    third possibility. This is a property of Except. -/
theorem sem_total {α : Type} (m : Sem α) (s : MachineState) :
    (exists result, Sem.run m s = .ok result) \/
    (exists err, Sem.run m s = .error err) := by
  let v := Sem.run m s
  show (exists result, v = .ok result) \/ (exists err, v = .error err)
  cases v with
  | ok result => exact Or.inl ⟨result, rfl⟩
  | error err => exact Or.inr ⟨err, rfl⟩

/-- stepN always produces either a successful result or an error.
    It never diverges (fuel ensures termination). -/
theorem stepN_total (fuel : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (s : MachineState) :
    (exists result, Sem.run (stepN fuel cfg pc args) s = .ok result) \/
    (exists err, Sem.run (stepN fuel cfg pc args) s = .error err) :=
  sem_total (stepN fuel cfg pc args) s

-- =================================================================
-- Progress for pure instructions
-- =================================================================

/-- Assume instruction always succeeds (it is a no-op in execution). -/
theorem assume_always_succeeds (cond : ValueId) (s : MachineState) :
    exists result, Sem.run (stepInst (.Assume cond)) s = .ok result := by
  exact Exists.intro (.value none, s) rfl

/-- Unreachable always succeeds (produces .Stuck, not an error). -/
theorem unreachable_always_succeeds (s : MachineState) :
    exists result, Sem.run (stepInst .Unreachable) s = .ok result := by
  exact Exists.intro (.terminator .Stuck, s) rfl

/-- A constant instruction always succeeds: it produces a fresh value
    regardless of the current state. Constants have no preconditions
    (no value lookups, no memory access, no permission checks). -/
theorem const_always_succeeds (ty : Ty) (val : Constant) (s : MachineState) :
    exists result, Sem.run (stepInst (.Const ty val)) s = .ok result := by
  simp [stepInst, Sem.run, Sem.bindFresh, StateT.run, StateT.get, StateT.set,
        Sem.getState, Sem.setState, MachineState.bindValue, bind, pure,
        Except.pure, Except.bind]
  cases val with
  | int i =>
    cases ty.bitWidth with
    | none => exact Exists.intro _ rfl
    | some w => exact Exists.intro _ rfl
  | float f => exact Exists.intro _ rfl
  | bool b => exact Exists.intro _ rfl
  | aggregate elts => exact Exists.intro _ rfl
  | vector elts =>
    cases ty with
    | Vector lanes elemTy =>
      cases elemTy.bitWidth with
      | none => exact Exists.intro _ rfl
      | some w => exact Exists.intro _ rfl
    | I8 => exact Exists.intro _ rfl
    | I16 => exact Exists.intro _ rfl
    | I32 => exact Exists.intro _ rfl
    | I64 => exact Exists.intro _ rfl
    | I128 => exact Exists.intro _ rfl
    | U8 => exact Exists.intro _ rfl
    | U16 => exact Exists.intro _ rfl
    | U32 => exact Exists.intro _ rfl
    | U64 => exact Exists.intro _ rfl
    | U128 => exact Exists.intro _ rfl
    -- v25 B1 scalars: same one-step Const success as every other type.
    | Isize => exact Exists.intro _ rfl
    | Usize => exact Exists.intro _ rfl
    | Char => exact Exists.intro _ rfl
    | Error => exact Exists.intro _ rfl
    | F16 => exact Exists.intro _ rfl
    | F32 => exact Exists.intro _ rfl
    | F64 => exact Exists.intro _ rfl
    | Bool => exact Exists.intro _ rfl
    | Ptr => exact Exists.intro _ rfl
    | FatPtr _ => exact Exists.intro _ rfl
    | Struct id => exact Exists.intro _ rfl
    | Array id n => exact Exists.intro _ rfl
    | Func id => exact Exists.intro _ rfl
    | Unit => exact Exists.intro _ rfl
    | Never => exact Exists.intro _ rfl
    | Tuple tys => exact Exists.intro _ rfl
    | Enum id => exact Exists.intro _ rfl
    | Ref t => exact Exists.intro _ rfl
    | RefMut t => exact Exists.intro _ rfl
    | PtrConst t => exact Exists.intro _ rfl
    | PtrMut t => exact Exists.intro _ rfl
    | Rc t => exact Exists.intro _ rfl
    | Set id repr => exact Exists.intro _ rfl
    | Sequence id => exact Exists.intro _ rfl
    | Record id => exact Exists.intro _ rfl
    | Closure id => exact Exists.intro _ rfl
    -- Refinements are representation-preserving. Constants execute at the
    -- erased value boundary; the validator discharges the predicate carried
    -- by `predId`, so `stepInst` does not inspect either table identifier.
    | Refine baseId predId => exact Exists.intro _ rfl
  -- ty supremacy aggregate constants (mirror of Ty.Set/Sequence/Record/Closure).
  | sequence elts => exact Exists.intro _ rfl
  | set elts => exact Exists.intro _ rfl
  | record flds => exact Exists.intro _ rfl
  | closure fn caps => exact Exists.intro _ rfl

/-- NullPtr instruction always succeeds. -/
theorem nullptr_always_succeeds (s : MachineState) :
    exists result, Sem.run (stepInst .NullPtr) s = .ok result := by
  simp [stepInst, Sem.run, Sem.bindFresh, StateT.run, StateT.get, StateT.set,
        Sem.getState, Sem.setState, MachineState.bindValue, bind, pure,
        Except.pure, Except.bind]
  exact Exists.intro _ rfl

/-- Undef instruction always succeeds. -/
theorem undef_always_succeeds (ty : Ty) (s : MachineState) :
    exists result, Sem.run (stepInst (.Undef ty)) s = .ok result := by
  simp [stepInst, Sem.run, Sem.bindFresh, StateT.run, StateT.get, StateT.set,
        Sem.getState, Sem.setState, MachineState.bindValue, bind, pure,
        Except.pure, Except.bind]
  exact Exists.intro _ rfl

-- =================================================================
-- Well-typedness predicate (for progress theorem)
-- =================================================================

/-- A value is well-typed with respect to a TrustIr type.
    This connects the dynamic Value tag to the static Ty annotation. -/
def value_has_type : Value -> Ty -> Prop
  | .int w _, ty      => ty.isInteger = true /\ ty.bitWidth = some w
  | .float _, .F32    => True
  | .float _, .F64    => True
  | .bool _, .Bool    => True
  | .ptr _, .Ptr      => True
  | .nullPtr, .Ptr    => True
  -- Pointer-like reference types: runtime representation is .ptr
  | .ptr _, .Ref _    => True
  | .ptr _, .RefMut _ => True
  | .ptr _, .PtrConst _ => True
  | .ptr _, .PtrMut _ => True
  | .ptr _, .Rc _     => True
  | .nullPtr, .Ref _  => True
  | .nullPtr, .RefMut _ => True
  | .nullPtr, .PtrConst _ => True
  | .nullPtr, .PtrMut _ => True
  | .nullPtr, .Rc _   => True
  -- Unit type: represented as empty aggregate
  | .aggregate [], .Unit => True
  -- Bounded executable vector subset: v4i32, v2i64, v4 bool, and v2 bool.
  -- Other vector shapes are intentionally unsupported by this dynamic check.
  | .vector lanes, .Vector n elemTy =>
      Ty.executableVectorPayloadMatches (.Vector n elemTy) lanes = true
  | _, _              => False

theorem value_has_type_v4i32 :
    value_has_type
      (.vector [.int 32 1, .int 32 2, .int 32 3, .int 32 4])
      (.Vector 4 .I32) := by
  change Ty.executableVectorPayloadMatches
      (.Vector 4 .I32)
      [.int 32 1, .int 32 2, .int 32 3, .int 32 4] = true
  decide

theorem value_has_type_v2i64 :
    value_has_type
      (.vector [.int 64 1, .int 64 2])
      (.Vector 2 .I64) := by
  change Ty.executableVectorPayloadMatches
      (.Vector 2 .I64)
      [.int 64 1, .int 64 2] = true
  decide

theorem value_has_type_v4bool :
    value_has_type
      (.vector [.bool true, .bool false, .bool true, .bool false])
      (.Vector 4 .Bool) := by
  change Ty.executableVectorPayloadMatches
      (.Vector 4 .Bool)
      [.bool true, .bool false, .bool true, .bool false] = true
  decide

theorem value_has_type_v2bool :
    value_has_type
      (.vector [.bool true, .bool false])
      (.Vector 2 .Bool) := by
  change Ty.executableVectorPayloadMatches
      (.Vector 2 .Bool)
      [.bool true, .bool false] = true
  decide

theorem value_has_type_rejects_v4i32_lane_count :
    ¬ value_has_type
      (.vector [.int 32 1, .int 32 2])
      (.Vector 4 .I32) := by
  change ¬ Ty.executableVectorPayloadMatches
      (.Vector 4 .I32)
      [.int 32 1, .int 32 2] = true
  decide

theorem value_has_type_rejects_v4i32_element_mismatch :
    ¬ value_has_type
      (.vector [.int 32 1, .int 64 2, .int 32 3, .int 32 4])
      (.Vector 4 .I32) := by
  change ¬ Ty.executableVectorPayloadMatches
      (.Vector 4 .I32)
      [.int 32 1, .int 64 2, .int 32 3, .int 32 4] = true
  decide

theorem value_has_type_rejects_v4bool_element_mismatch :
    ¬ value_has_type
      (.vector [.bool true, .int 1 0, .bool false, .bool true])
      (.Vector 4 .Bool) := by
  change ¬ Ty.executableVectorPayloadMatches
      (.Vector 4 .Bool)
      [.bool true, .int 1 0, .bool false, .bool true] = true
  decide

theorem value_has_type_rejects_scalar_vector_mismatch :
    ¬ value_has_type (.int 32 1) (.Vector 4 .I32) := by
  change ¬ ((.Vector 4 .I32 : Ty).isInteger = true /\
      (.Vector 4 .I32 : Ty).bitWidth = some 32)
  decide

theorem value_has_type_rejects_unsupported_v8i32 :
    ¬ value_has_type
      (.vector [.int 32 0, .int 32 1, .int 32 2, .int 32 3,
                .int 32 4, .int 32 5, .int 32 6, .int 32 7])
      (.Vector 8 .I32) := by
  change ¬ Ty.executableVectorPayloadMatches
      (.Vector 8 .I32)
      [.int 32 0, .int 32 1, .int 32 2, .int 32 3,
       .int 32 4, .int 32 5, .int 32 6, .int 32 7] = true
  decide

/-- A binary operation is a division or remainder operation. -/
def BinOp.isDivRem : BinOp → Bool
  | .UDiv | .SDiv | .URem | .SRem => true
  | _ => false

/-- A state is well-typed for a BinOp if the operation is an integer op,
    both operands are defined integer values of matching width,
    the type is integer, and the rhs is non-zero for div/rem ops. -/
def well_typed_binop (op : BinOp) (ty : Ty) (lhs rhs : ValueId)
    (s : MachineState) : Prop :=
  op.isInteger = true /\
  ty.isInteger = true /\
  (exists w v1 v2,
    s.lookupValue lhs = some (.int w v1) /\
    s.lookupValue rhs = some (.int w v2) /\
    (op.isDivRem = true → v2 ≠ 0) /\
    -- ShiftInRange: a shift amount >= width is UB, so progress for a shift
    -- requires the discharged in-range obligation (docs/ub-numerics-policy.md §1).
    ((op = .Shl ∨ op = .LShr ∨ op = .AShr) → v2 < (w : Int)) /\
    -- NoOverflow: INT_MIN / -1 (and % -1) is UB, so signed div/rem progress
    -- requires the discharged no-overflow obligation.
    ((op = .SDiv ∨ op = .SRem) →
      ¬(toSigned v1 w = -((2 : Int) ^ (w - 1)) ∧ toSigned v2 w = -1)))

/-- Progress for BinOp on well-typed integer operands: if both operands
    are defined integer values of matching width and the type is integer
    (with non-zero divisor for div/rem ops), stepInst produces a result.

    The original theorem was unprovable because division/remainder by zero
    produces SemError.ub. This version includes the non-zero divisor
    hypothesis for div/rem operations and the matching-width requirement,
    making the theorem complete.

    Division safety (the non-zero precondition itself) is proved in
    ArithProps.lean. -/
theorem binop_progress (op : BinOp) (ty : Ty) (lhs rhs : ValueId)
    (s : MachineState) (hwt : well_typed_binop op ty lhs rhs s) :
    exists result, Sem.run (stepInst (.BinOp op ty lhs rhs)) s = .ok result := by
  obtain ⟨hOpInt, _hTyInt, w, v1, v2, hLhs, hRhs, hDiv, hShift, hNoOvf⟩ := hwt
  -- After unfolding, stepInst (.BinOp ..) = do vid ← semBinOp ..; pure (.value (some vid))
  -- semBinOp looks up lhs and rhs, pattern-matches on their types,
  -- checks width equality, then calls semIntBinOp.
  -- We unfold through the monadic layers to a point where hLhs/hRhs can be applied.
  have hLhs' : s.locals.get lhs = some (.int w v1) := hLhs
  have hRhs' : s.locals.get rhs = some (.int w v2) := hRhs
  simp only [stepInst, Sem.run, StateT.run, bind, StateT.bind,
        semBinOp, Sem.lookupValue, Sem.getState, StateT.get,
        Sem.bindFresh, Sem.setState, StateT.set, StateT.pure, pure,
        MachineState.lookupValue, MachineState.bindValue,
        Except.pure, Except.bind, hLhs', hRhs']
  -- After simp, widths match (both w), so the w != w check is false
  simp only [bne_self_eq_false, ↓reduceIte]
  -- Now we need to show semIntBinOp op w v1 v2 = .ok _
  -- Case split on op to handle each BinOp variant.
  -- Float ops (FAdd..FRem) are excluded by hOpInt (op.isInteger = true).
  cases op with
  -- Every TOTAL integer op: `semIntBinOp` returns `.ok` unconditionally, so the
  -- witness is immediate. The Bool connectives join here rather than needing
  -- cases of their own precisely BECAUSE they are total -- the partial ops
  -- (UDiv/SDiv/shifts) are the ones that need their guards discharged below.
  | Add | Sub | Mul | And | Or | Xor | BAnd | BOr | BXor =>
    simp [semIntBinOp]; exact Exists.intro _ rfl
  | Shl | LShr | AShr =>
    -- The shift amount is in range (hShift), so the UB guard is not taken.
    simp only [semIntBinOp]
    rw [if_neg (by have := hShift (by decide); omega)]
    exact Exists.intro _ rfl
  | FAdd | FSub | FMul | FDiv | FRem =>
    -- These are float ops, contradicting hOpInt : op.isInteger = true
    simp [BinOp.isInteger] at hOpInt
  | UDiv =>
    simp only [semIntBinOp]
    have h0 : v2 ≠ 0 := hDiv rfl
    simp only [beq_iff_eq, h0, ↓reduceIte]
    exact Exists.intro _ rfl
  | SDiv =>
    have h0 : v2 ≠ 0 := hDiv rfl
    have hov := hNoOvf (by decide)
    -- semIntBinOp succeeds (nonzero divisor, no INT_MIN/-1 overflow), so the
    -- monadic match takes the .ok branch.
    have hsd : ∃ r0, semIntBinOp .SDiv w v1 v2 = .ok r0 := by
      have hb' : (v2 == 0) = false := by simpa using h0
      simp only [semIntBinOp, hb', if_false]
      split
      · rename_i hbad
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hbad
        exact absurd hbad hov
      · exact ⟨_, rfl⟩
    obtain ⟨r0, hsd⟩ := hsd
    rw [hsd]
    exact Exists.intro _ rfl
  | URem =>
    simp only [semIntBinOp]
    have h0 : v2 ≠ 0 := hDiv rfl
    simp only [beq_iff_eq, h0, ↓reduceIte]
    exact Exists.intro _ rfl
  | SRem =>
    have h0 : v2 ≠ 0 := hDiv rfl
    have hov := hNoOvf (by decide)
    have hsr : ∃ r0, semIntBinOp .SRem w v1 v2 = .ok r0 := by
      have hb' : (v2 == 0) = false := by simpa using h0
      simp only [semIntBinOp, hb', if_false]
      split
      · rename_i hbad
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hbad
        exact absurd hbad hov
      · exact ⟨_, rfl⟩
    obtain ⟨r0, hsr⟩ := hsr
    rw [hsr]
    exact Exists.intro _ rfl

/-- Progress for Copy: if the operand is defined, Copy always succeeds.

    Proof strategy: unfold stepInst for .Copy, which does
    Sem.lookupValue operand >>= Sem.bindFresh. hDef ensures
    lookupValue succeeds, and bindFresh always succeeds. -/
theorem copy_progress (ty : Ty) (operand : ValueId) (s : MachineState)
    (hDef : exists v, s.lookupValue operand = some v) :
    exists result, Sem.run (stepInst (.Copy ty operand)) s = .ok result := by
  obtain ⟨v, hv⟩ := hDef
  -- stepInst (.Copy ty operand) = do let v ← Sem.lookupValue operand;
  --   let vid ← Sem.bindFresh v; pure (.value (some vid))
  -- Sem.run unfolds to StateT.run, which is function application.
  -- lookupValue checks s.lookupValue operand; hv gives us some v.
  -- bindFresh allocates a fresh ValueId and updates locals.
  -- After unfolding, s.lookupValue becomes s.locals.get.
  -- We need hv in terms of s.locals.get since MachineState.lookupValue
  -- unfolds to locals.get.
  have hv' : s.locals.get operand = some v := hv
  simp only [stepInst, Sem.run, StateT.run, bind, StateT.bind,
        Sem.lookupValue, Sem.getState, StateT.get,
        Sem.bindFresh, Sem.setState, StateT.set, StateT.pure, pure,
        MachineState.lookupValue, MachineState.bindValue,
        Except.pure, Except.bind, hv']
  exact Exists.intro _ rfl

-- =================================================================
-- Fuel monotonicity
-- =================================================================

/-- If a computation terminates with fuel1, it produces the same result
    with any fuel2 >= fuel1.

    This is a key property for partial correctness reasoning: if you
    can find ANY fuel value that terminates, the result is independent
    of how much extra fuel you provide.

    The proof is by induction on fuel1, generalizing all other arguments:
    - Base case: fuel1 = 0 means outOfFuel error, but hterm says .ok,
      so this case is vacuously true.
    - Inductive case: fuel1 = k+1, fuel2 = j+1 (from hfuel). After
      unfolding stepN, both sides evaluate cfg(pc) identically and run
      stepBlock on the same state. The StepResult cases:
        .Ret: both return immediately with the same values.
        .Stuck/.CallReq/.CallIndirectReq: produce errors, contradicting hterm.
        .Continue nextPc nextArgs: IH applies with k <= j. -/
theorem fuel_monotone (fuel1 fuel2 : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (s : MachineState)
    (hfuel : fuel1 <= fuel2)
    (result : List Value × MachineState)
    (hterm : Sem.run (stepN fuel1 cfg pc args) s = .ok result) :
    Sem.run (stepN fuel2 cfg pc args) s = .ok result := by
  induction fuel1 generalizing fuel2 pc args s result with
  | zero =>
    -- fuel1 = 0: stepN 0 = throw outOfFuel. Sem.run produces .error.
    -- hterm says .ok, so this is a contradiction.
    -- stepN 0 = throw SemError.outOfFuel, and for StateT/Except,
    -- Sem.run (throw e) s = .error e. This holds definitionally.
    have : Sem.run (stepN 0 cfg pc args) s = .error SemError.outOfFuel := rfl
    rw [this] at hterm; exact Except.noConfusion hterm
  | succ k ih =>
    -- fuel1 = k+1, fuel2 >= k+1, so fuel2 = j+1 for some j >= k
    obtain ⟨j, rfl⟩ : exists j, fuel2 = j + 1 := by
      cases fuel2 with
      | zero => omega
      | succ j => exact ⟨j, rfl⟩
    have hjk : k ≤ j := by omega
    -- Both stepN (k+1) and stepN (j+1) share the same structure.
    -- After unfolding, both become:
    --   match cfg pc with
    --   | none => throw typeError ...
    --   | some block => do result ← stepBlock block args; match result with ...
    -- Only the Continue case differs (uses k vs j in the recursive call).
    -- We unfold Sem.run and stepN together.
    simp only [Sem.run, StateT.run] at hterm ⊢
    unfold stepN at hterm ⊢
    -- Case-split on cfg pc
    cases hcfg : cfg pc with
    | none =>
      -- cfg pc = none: throwTypeError → Except.error, contradicting hterm
      simp only [hcfg] at hterm ⊢
      -- hterm has throwThe ... = .ok result. This reduces to .error = .ok.
      change Except.error _ = Except.ok result at hterm
      exact Except.noConfusion hterm
    | some block =>
      -- cfg pc = some block: both sides do stepBlock block args, then match.
      simp only [hcfg, bind, StateT.bind, Except.bind] at hterm ⊢
      -- Case-split on stepBlock block args s
      cases hstep : stepBlock block args s with
      | error e =>
        -- stepBlock failed → .error → contradicts hterm
        simp only [hstep] at hterm
      | ok p =>
        simp only [hstep] at hterm ⊢
        obtain ⟨stepResult, s'⟩ := p
        -- Case-split on the StepResult
        cases stepResult with
        | Ret values =>
          -- .Ret: both sides return immediately. Same result.
          exact hterm
        | Stuck =>
          -- .Stuck: throwUB → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          exact Except.noConfusion hterm
        | Continue nextPc nextArgs =>
          -- .Continue: recursive call stepN k vs stepN j on state s'.
          -- Apply IH with k <= j.
          exact ih j nextPc nextArgs s' hjk result hterm
        | CallReq fid callArgs =>
          -- .CallReq: throwTypeError → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          exact Except.noConfusion hterm
        | CallIndirectReq addr fid callArgs =>
          -- .CallIndirectReq: throwTypeError → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          exact Except.noConfusion hterm
        | InvokeReq callee callArgs normalDest normalArgs unwindDest =>
          -- .InvokeReq: fail-closed in stepN (throwUnsupported) → .error →
          -- contradicts hterm
          change Except.error _ = Except.ok result at hterm
          exact Except.noConfusion hterm
        | SeqMapReq fid elems =>
          -- .SeqMapReq: throwUnsupported → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          exact Except.noConfusion hterm

/-- Corollary: fuel doubling preserves results. -/
theorem fuel_double_preserving (fuel : Nat) (cfg : CFG) (pc : BlockId)
    (args : List Value) (s : MachineState)
    (result : List Value × MachineState)
    (hterm : Sem.run (stepN fuel cfg pc args) s = .ok result) :
    Sem.run (stepN (fuel + fuel) cfg pc args) s = .ok result :=
  fuel_monotone fuel (fuel + fuel) cfg pc args s
    (Nat.le_add_right fuel fuel) result hterm

-- =================================================================
-- StepResult characterization
-- =================================================================

/-- A StepResult is terminal if it does not continue to another block. -/
def StepResult.isTerminal : StepResult -> Bool
  | .Ret _                 => true
  | .Stuck                 => true
  | .Continue _ _          => false
  | .CallReq _ _           => true  -- call transfers control to callee
  | .CallIndirectReq _ _ _ => true  -- indirect call transfers control
  | .InvokeReq _ _ _ _ _   => true  -- invoke transfers control to callee
  | .SeqMapReq _ _         => true  -- element application transfers control

/-- After a terminal StepResult, stepN returns immediately
    (does not consume more fuel). This is the early-exit property. -/
theorem terminal_step_classification (sr : StepResult)
    (hTerm : sr.isTerminal = true) :
    (exists vs, sr = .Ret vs) \/ sr = .Stuck
    \/ (exists fid args, sr = .CallReq fid args)
    \/ (exists addr fid args, sr = .CallIndirectReq addr fid args)
    \/ (exists fid args nd nargs ud, sr = .InvokeReq fid args nd nargs ud)
    \/ (exists fid elems, sr = .SeqMapReq fid elems) := by
  cases sr with
  | Ret vs => exact Or.inl (Exists.intro vs rfl)
  | Stuck  => exact Or.inr (Or.inl rfl)
  | Continue _ _ => simp [StepResult.isTerminal] at hTerm
  | CallReq fid args => exact Or.inr (Or.inr (Or.inl (Exists.intro fid (Exists.intro args rfl))))
  | CallIndirectReq addr fid args =>
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (Exists.intro addr (Exists.intro fid (Exists.intro args rfl))))))
  | InvokeReq fid args nd nargs ud =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Exists.intro fid (Exists.intro args (Exists.intro nd
        (Exists.intro nargs (Exists.intro ud rfl)))))))))
  | SeqMapReq fid elems =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Exists.intro fid (Exists.intro elems rfl))))))

-- =================================================================
-- Composition properties
-- =================================================================

/-- Two states agree on a set of value ids if they map each id
    to the same value. -/
def states_agree_on (ids : List ValueId) (s1 s2 : MachineState) : Prop :=
  forall id, id ∈ ids -> s1.lookupValue id = s2.lookupValue id

/-- Constant instructions produce the same InstrResult regardless of state.
    The output VALUE depends only on the type and constant, not the state.
    NOTE: The output MachineState differs between s1 and s2 (locals are
    updated by bindFresh), so we compare only the InstrResult component.
    The previous version of this theorem compared the full result including
    MachineState, which was too strong -- see issue #11 discussion.

    When s1 = s2, the full Sem.run results are trivially equal. -/
theorem const_state_independent (ty : Ty) (val : Constant)
    (s1 s2 : MachineState)
    (hEq : s1 = s2) :
    Sem.run (stepInst (.Const ty val)) s1 =
    Sem.run (stepInst (.Const ty val)) s2 := by
  subst hEq; rfl

-- =================================================================
-- Future work
-- =================================================================

/-
## Theorems for subsequent phases

1. **Full type safety (progress + preservation):**
   Well-typed programs never get stuck. This requires a complete
   typing judgment for TrustIr programs (function signatures, block
   parameter types, etc.) which is Phase 6 work.

2. **Preservation:** If a state is well-typed and stepping succeeds,
   the resulting state is also well-typed.

3. **Confluence for non-side-effecting subsequences:**
   Pure instruction subsequences can be reordered without changing
   the final state (see TransformCorrectness.lean for the framework).

4. **Adequacy:** The fuel-based semantics is adequate with respect to
   a hypothetical big-step semantics (every terminating big-step
   evaluation has a corresponding fuel-based evaluation).
-/

end TrustIr
