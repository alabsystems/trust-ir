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
import TrustIr.Proofs.ConstantTypingEquations

namespace TrustIr

set_option smartUnfolding false

attribute [local simp] exceptSem_pure exceptSem_ok_bind

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

mutual

/-- State-independent typing evidence for the scalar and inline constants
    the table-free converter supports. It states constructor/type matching,
    exact vector census and the direct-field Uninit role, rather than assuming
    that conversion or execution succeeds. Named types need module tables. -/
inductive ConstInlineAdmitted : Bool → Ty → Constant → Prop where
  | integer {allow ty value} (h : ty.isInteger = true) :
      ConstInlineAdmitted allow ty (.int value)
  | thinNull {allow} : ConstInlineAdmitted allow .Ptr (.int 0)
  | fatNull {allow kind} :
      ConstInlineAdmitted allow (.FatPtr kind) (.aggregate [.int 0, .int 0])
  | unsigned128 {allow value} : ConstInlineAdmitted allow .U128 (.u128 value)
  | boolean {allow value} : ConstInlineAdmitted allow .Bool (.bool value)
  | float16 {allow value} : ConstInlineAdmitted allow .F16 (.float value)
  | float32 {allow value} : ConstInlineAdmitted allow .F32 (.float value)
  | float64 {allow value} : ConstInlineAdmitted allow .F64 (.float value)
  | unit {allow} : ConstInlineAdmitted allow .Unit .phantomData
  | function {allow signature target} :
      ConstInlineAdmitted allow (.Func signature) (.fnDef target)
  | tuple {allow tys cs} (fields : ConstFieldsAdmitted allow tys cs) :
      ConstInlineAdmitted allow (.Tuple tys) (.aggregate cs)
  | vector {allow count elemTy cs} (nonzero : count ≠ 0)
      (census : cs.length = count) (scalar : (vectorScalarByteSize elemTy).isSome = true)
      (lanes : ConstLanesAdmitted elemTy cs) :
      ConstInlineAdmitted allow (.Vector count elemTy) (.vector cs)

inductive ConstFieldsAdmitted : Bool → List Ty → List Constant → Prop where
  | nil {allow} : ConstFieldsAdmitted allow [] []
  | uninit {ty tys cs} (rest : ConstFieldsAdmitted true tys cs) :
      ConstFieldsAdmitted true (ty :: tys) (.uninit :: cs)
  | cons {allow ty tys c cs} (head : ConstInlineAdmitted false ty c)
      (rest : ConstFieldsAdmitted allow tys cs) :
      ConstFieldsAdmitted allow (ty :: tys) (c :: cs)

inductive ConstLanesAdmitted : Ty → List Constant → Prop where
  | nil {elemTy} : ConstLanesAdmitted elemTy []
  | cons {elemTy c cs} (head : ConstInlineAdmitted false elemTy c)
      (rest : ConstLanesAdmitted elemTy cs) : ConstLanesAdmitted elemTy (c :: cs)

end

theorem ConstFieldsAdmitted.census {allow tys cs} (h : ConstFieldsAdmitted allow tys cs) :
    tys.length = cs.length := by
  cases h with
  | nil => rfl
  | uninit rest =>
    simpa only [List.length_cons] using congrArg Nat.succ (ConstFieldsAdmitted.census rest)
  | cons _ rest =>
    simpa only [List.length_cons] using congrArg Nat.succ (ConstFieldsAdmitted.census rest)

theorem ConstInlineAdmitted.not_uninit {allow ty c} (h : ConstInlineAdmitted allow ty c) :
    c ≠ .uninit := by
  cases h <;> intro eq <;> cases eq

mutual

theorem ConstInlineAdmitted.pointerForms {allow ty c} (h : ConstInlineAdmitted allow ty c) :
    constPointerFormsSupported ty c = true := by
  cases h with
  | integer h => cases ty <;> simp_all [Ty.isInteger, constPointerFormsSupported]
  | tuple fields =>
    unfold constPointerFormsSupported
    simp [fields.census, ConstFieldsAdmitted.pointerForms fields]
  | vector _ _ _ lanes =>
    unfold constPointerFormsSupported
    simp [ConstLanesAdmitted.pointerForms lanes]
  | _ => simp [constPointerFormsSupported]
termination_by sizeOf c
decreasing_by all_goals (simp_wf <;> omega)

theorem ConstFieldsAdmitted.pointerForms {allow tys cs} (h : ConstFieldsAdmitted allow tys cs) :
    constFieldPointerFormsSupported tys cs = true := by
  cases h with
  | nil => simp [constFieldPointerFormsSupported]
  | uninit rest =>
    unfold constFieldPointerFormsSupported
    exact ConstFieldsAdmitted.pointerForms rest
  | cons head rest =>
    have hh := ConstInlineAdmitted.pointerForms head
    have ht := ConstFieldsAdmitted.pointerForms rest
    rename_i c _
    cases c <;> unfold constFieldPointerFormsSupported <;> simp_all
termination_by sizeOf cs
decreasing_by all_goals (simp_wf <;> omega)

theorem ConstLanesAdmitted.pointerForms {elemTy cs} (h : ConstLanesAdmitted elemTy cs) :
    constLanePointerFormsSupported elemTy cs = true := by
  cases h with
  | nil => simp [constLanePointerFormsSupported]
  | cons head rest =>
    unfold constLanePointerFormsSupported
    simp [ConstInlineAdmitted.pointerForms head, ConstLanesAdmitted.pointerForms rest]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf <;> omega)

end

mutual

theorem ConstInlineAdmitted.checked {allow ty c} (h : ConstInlineAdmitted allow ty c)
    (model : ByteModel) : constValueAtChecked ty c model allow = .ok (constValueAt ty c model) := by
  have hp := h.pointerForms
  cases h with
  | integer h =>
    rw [constValueAtChecked_eq]
    cases ty <;> simp_all [Ty.isInteger]
  | tuple fields =>
    have hv := ConstFieldsAdmitted.checked fields model
    rw [constValueAtChecked_eq]
    simp [hp, fields.census, hv, constValueAt]
  | @vector allow count elemTy cs hn hc hs lanes =>
    have hv := ConstLanesAdmitted.checked lanes model
    have hSome : (vectorScalarByteSize elemTy).isNone = false := by
      cases hvv : vectorScalarByteSize elemTy <;> simp_all
    rw [constValueAtChecked_eq]
    simp [hp, hn, hc, hSome, hv, constValueAt]
  | _ => rw [constValueAtChecked_eq]; simp [hp, constValueAt, constFloatAt, Value.ofConstant]
termination_by sizeOf c
decreasing_by all_goals (simp_wf <;> omega)

theorem ConstFieldsAdmitted.checked {allow tys cs} (h : ConstFieldsAdmitted allow tys cs)
    (model : ByteModel) : constFieldsAtChecked tys cs model allow = .ok (constFieldsAt tys cs model) := by
  cases h with
  | nil => rw [constFieldsAtChecked_eq]; simp [constFieldsAt, Value.ofConstantList]
  | uninit rest =>
    have hv := ConstFieldsAdmitted.checked rest model
    rw [constFieldsAtChecked_eq]
    simp [hv, constFieldsAt, constValueAt, Value.ofConstant]
  | cons head rest =>
    have hf := ConstInlineAdmitted.checked head model
    have hv := ConstFieldsAdmitted.checked rest model
    have hne := head.not_uninit
    rw [constFieldsAtChecked_eq]
    rename_i c _
    cases c <;> simp_all [constFieldsAt]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf <;> omega)

theorem ConstLanesAdmitted.checked {elemTy cs} (h : ConstLanesAdmitted elemTy cs)
    (model : ByteModel) : constLanesAtChecked elemTy cs model = .ok (constLanesAt elemTy cs model) := by
  cases h with
  | nil => rw [constLanesAtChecked_eq]; simp [constLanesAt]
  | cons head rest =>
    have hf := ConstInlineAdmitted.checked head model
    have hv := ConstLanesAdmitted.checked rest model
    rw [constLanesAtChecked_eq]
    simp [hf, hv, constLanesAt]
termination_by sizeOf cs
decreasing_by all_goals (simp_wf <;> omega)

end

/-- Closed scalar equations keep downstream instruction proofs from
    regenerating the general checked matcher's equations. -/
theorem constValueAtChecked_i64 (value : Int) (model : ByteModel) (allow : Bool) :
    constValueAtChecked .I64 (.int value) model allow = .ok (Value.intAt 64 value) := by
  have h := ConstInlineAdmitted.checked
    (ConstInlineAdmitted.integer (allow := allow) (ty := .I64) (value := value) rfl) model
  cases model <;> simpa only [constValueAt, Ty.bitWidthFor, Ty.bitWidthAtModel, Ty.bitWidth] using h

theorem constValueAtChecked_i32 (value : Int) (model : ByteModel) (allow : Bool) :
    constValueAtChecked .I32 (.int value) model allow = .ok (Value.intAt 32 value) := by
  have h := ConstInlineAdmitted.checked
    (ConstInlineAdmitted.integer (allow := allow) (ty := .I32) (value := value) rfl) model
  cases model <;> simpa only [constValueAt, Ty.bitWidthFor, Ty.bitWidthAtModel, Ty.bitWidth] using h

/-- A statically admitted, symbol-free scalar/inline constant binds a fresh
    value in every state. The premise is syntax/type/role evidence above;
    there is no memory, value-lookup or permission precondition. -/
theorem const_always_succeeds (ty : Ty) (val : Constant) (s : MachineState)
    (hNoSym : val.hasSymbolAddr = false)
    (hTyped : ConstInlineAdmitted true ty val) :
    exists result, Sem.run (stepInst (.Const ty val)) s = .ok result := by
  have hChecked := hTyped.checked .le64
  simp only [stepInst, hNoSym, Bool.false_eq_true, ↓reduceIte, hChecked, pure_bind]
  exact Exists.intro _ rfl

/- The outer forms whose field/element widths require a declaration table.
   The available fixed census is checked even without that table. -/
inductive ConstDefinitionForm : Ty → Constant → Prop where
  | bytes {id count data utf8} (h : data.length = count) :
      ConstDefinitionForm (.Array id count) (.bytes data utf8)
  | array {id count cs} (h : cs.length = count) :
      ConstDefinitionForm (.Array id count) (.array cs)
  | arrayLegacy {id count cs} (h : cs.length = count) :
      ConstDefinitionForm (.Array id count) (.aggregate cs)
  | splat {id count c} : ConstDefinitionForm (.Array id count) (.splat c count)
  | structure {id cs} : ConstDefinitionForm (.Struct id) (.aggregate cs)
  | enumeration {id disc cs} : ConstDefinitionForm (.Enum id) (.aggregate (.int disc :: cs))
  | sequence {id cs} : ConstDefinitionForm (.Sequence id) (.sequence cs)
  | set {id repr cs} : ConstDefinitionForm (.Set id repr) (.set cs)
  | record {id fs} : ConstDefinitionForm (.Record id) (.record fs)
  | recordLegacy {id cs} : ConstDefinitionForm (.Record id) (.aggregate cs)
  | closure {id target cs} : ConstDefinitionForm (.Closure id) (.closure target cs)

/-- A well-shaped named form with no available table refuses an ambiguous
    float width explicitly. Malformed families/censuses no longer satisfy this
    claim merely because an unrelated float occurs in their payload. -/
theorem const_width_ambiguous_refused (ty : Ty) (val : Constant) (s : MachineState)
    (hNoSym : val.hasSymbolAddr = false)
    (hw : constWidthAmbiguous ty val = true)
    (hPointer : constPointerFormsSupported ty val = true)
    (hForm : ConstDefinitionForm ty val) :
    Sem.run (stepInst (.Const ty val)) s =
      .error (.unsupported .float constWidthAmbiguousMsg) := by
  cases hForm <;>
    simp only [stepInst, hNoSym, Bool.false_eq_true, ↓reduceIte] <;>
    rw [constValueAtChecked_eq] <;>
    simp_all [constMissingDefinition] <;> rfl

/-- The fail-closed half (WS2.18): a constant holding a link-time
    `symbolAddr` anywhere is refused with `unsupported.link_time_address`,
    never bound — mirroring the reference interpreter, whose
    `constant_to_value` has no arm for it. -/
theorem const_symbolAddr_refused (ty : Ty) (val : Constant) (s : MachineState)
    (hSym : val.hasSymbolAddr = true) :
    Sem.run (stepInst (.Const ty val)) s
      = .error (.unsupported .linkTimeAddress
          "Const: a link-time symbol address has no compile-time value") := by
  simp only [stepInst]
  rw [if_pos hSym]
  rfl

/-- NullPtr instruction always succeeds. -/
theorem nullptr_always_succeeds (s : MachineState) :
    exists result, Sem.run (stepInst .NullPtr) s = .ok result := by
  simp [stepInst, Sem.run, Sem.bindFresh, StateT.run, StateT.get, StateT.set,
        Sem.getState, Sem.setState, MachineState.bindValue, bind, pure,
        Except.pure, Except.bind]
  trustIrCompilerProof { exact Exists.intro _ rfl } { exact ⟨_, _, rfl⟩ }

/-- Undef instruction always succeeds: it binds a POISON value, it is not
    itself undefined behaviour (ub-numerics-policy §4, roadmap WS2.10). -/
theorem undef_always_succeeds (ty : Ty) (s : MachineState) :
    exists result, Sem.run (stepInst (.Undef ty)) s = .ok result := by
  simp [stepInst, Sem.run, Sem.bindFresh, StateT.run, StateT.get, StateT.set,
        Sem.getState, Sem.setState, MachineState.bindValue, bind, pure,
        Except.pure, Except.bind]
  trustIrCompilerProof { exact Exists.intro _ rfl } { exact ⟨_, _, rfl⟩ }

/-- INSPECTING an `Undef` is undefined behaviour (roadmap WS2.10): the poison
    guard every content-consuming instruction runs (`Sem.rejectPartial` —
    arithmetic, comparison, cast, branch/switch/select condition, field
    projection) throws `SemError.ub` on an `.undef` value of ANY type, exactly
    as on a partially-initialized `.partial` image. The companion of
    `undef_always_succeeds`: executing `undef` is fine, using it is not. -/
theorem undef_inspect_is_ub (ty : Ty) (op : String) (s : MachineState) :
    ∃ msg, Sem.run (Sem.rejectPartial (.undef ty) op) s = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Instruction-level instance of `undef_inspect_is_ub`: a `BinOp` whose left
    operand is an `Undef` is undefined behaviour, whatever the operator, the
    type and the right operand. -/
theorem undef_binop_operand_is_ub (op : BinOp) (ty : Ty) (lhs rhs : ValueId)
    (s : MachineState) (t : Ty) (v : Value)
    (hl : s.lookupValue lhs = some (.undef t))
    (hr : s.lookupValue rhs = some v) :
    ∃ msg, Sem.run (stepInst (.BinOp op ty lhs rhs)) s = .error (.ub msg) :=
  ⟨_, by
    cases choice : op.isMinMax <;>
      simp [stepInst, semBinOp, semBinOpDeterministic, semFloatMinMax,
          semFloatMinMaxValues, choice, Sem.lookupValue, Sem.rejectPartial, Sem.throwUB, hl, hr,
          Sem.getState, Sem.run, StateT.run, StateT.get, bind, StateT.bind,
          Except.bind, throw, throwThe, MonadExceptOf.throw, StateT.lift,
          pure, Except.pure, StateT.pure] <;>
      rfl⟩

/-- Branching on an `Undef` condition is undefined behaviour (policy §4:
    "branching on poison is UB"). -/
theorem undef_condbr_is_ub (cond : ValueId) (t : Ty)
    (thenTarget elseTarget : BlockId) (thenArgs elseArgs : List ValueId)
    (s : MachineState) (hc : s.lookupValue cond = some (.undef t)) :
    ∃ msg, Sem.run (semCondBr cond thenTarget thenArgs elseTarget elseArgs) s
      = .error (.ub msg) :=
  ⟨_, by
    simp [semCondBr, Sem.lookupValue, Sem.rejectPartial, Sem.throwUB, hc,
          Sem.getState, Sem.run, StateT.run, StateT.get, bind, StateT.bind,
          Except.bind, throw, throwThe, MonadExceptOf.throw, StateT.lift,
          pure, Except.pure, StateT.pure]
    rfl⟩

-- =================================================================
-- Well-typedness predicate (for progress theorem)
-- =================================================================

/-- A value is well-typed with respect to a TrustIr type.
    This connects the dynamic Value tag to the static Ty annotation. -/
def value_has_type : Value -> Ty -> Prop
  | .int w _, ty      => ty.isInteger = true /\ ty.bitWidth = some w
  -- An F32 value is a binary32 value (WS2.23: the executable model rounds
  -- every F32 result to binary32 and refuses an F32 operand that is not one).
  | .float f, .F32    => isExactIn .binary32 f = true
  | .float _, .F64    => True
  | .bool _, .Bool    => True
  | .ptr _ _, .Ptr      => True
  | .nullPtr, .Ptr    => True
  -- Pointer-like reference types: runtime representation is .ptr
  | .ptr _ _, .Ref _    => True
  | .ptr _ _, .RefMut _ => True
  | .ptr _ _, .PtrConst _ => True
  | .ptr _ _, .PtrMut _ => True
  | .ptr _ _, .Rc _     => True
  | .nullPtr, .Ref _  => True
  | .nullPtr, .RefMut _ => True
  | .nullPtr, .PtrConst _ => True
  | .nullPtr, .PtrMut _ => True
  | .nullPtr, .Rc _   => True
  -- Unit type: represented as empty aggregate
  | .aggregate [], .Unit => True
  -- Bounded executable vector subset (`Ty.executableVectorPayloadMatches`:
  -- the integer lanes of `Ty.executableIntLane?` and the bool masks). Other
  -- vector shapes are intentionally unsupported by this dynamic check.
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
  have noChoice : op.isMinMax = false := by
    cases op <;> simp_all [BinOp.isInteger, BinOp.isMinMax]
  simp only [stepInst, Sem.run, StateT.run, bind, StateT.bind,
        semBinOp, noChoice, Bool.false_eq_true, ↓reduceIte, semBinOpDeterministic,
        semBinOpValues, Sem.rejectPartial, Sem.lookupValue, Sem.getState, StateT.get,
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
  | Add | Sub | Mul | And | Or | Xor | BAnd | BOr | BXor | RotL | RotR =>
    simp [semIntBinOp]; trustIrCompilerProof { exact Exists.intro _ rfl } { exact ⟨_, _, rfl⟩ }
  | Shl | LShr | AShr =>
    -- The shift amount is in range (hShift), so the UB guard is not taken.
    simp only [semIntBinOp]
    rw [if_neg (show ¬ v2 ≥ (w : Int) from Int.not_le.mpr (hShift (by simp)))]
    exact Exists.intro _ rfl
  | FAdd | FSub | FMul | FDiv | FRem | FMin | FMax | FCopySign =>
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
      simp only [semIntBinOp, hb', Bool.false_eq_true, if_false]
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
      simp only [semIntBinOp, hb', Bool.false_eq_true, if_false]
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
    rw [this] at hterm; cases hterm
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
      cases hterm
    | some block =>
      -- cfg pc = some block: both sides do stepBlock block args, then match.
      simp only [hcfg, bind, StateT.bind, Except.bind] at hterm ⊢
      -- Case-split on stepBlock block args s
      cases hstep : stepBlock block args s with
      | error e =>
        -- stepBlock failed → .error → contradicts hterm
        simp only [hstep] at hterm <;> cases hterm
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
          cases hterm
        | Continue nextPc nextArgs =>
          -- .Continue: recursive call stepN k vs stepN j on state s'.
          -- Apply IH with k <= j.
          exact ih j nextPc nextArgs s' hjk result hterm
        | CallReq fid callArgs =>
          -- .CallReq: throwTypeError → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          cases hterm
        | CallIndirectReq addr fid callArgs =>
          -- .CallIndirectReq: throwTypeError → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          cases hterm
        | InvokeReq callee callArgs normalDest normalArgs unwindDest =>
          -- .InvokeReq: fail-closed in stepN (throwUnsupported) → .error →
          -- contradicts hterm
          change Except.error _ = Except.ok result at hterm
          cases hterm
        | InvokeIndirectReq addr sig callArgs normalDest normalArgs unwindDest =>
          -- .InvokeIndirectReq: fail-closed in stepN (throwUnsupported) →
          -- .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          cases hterm
        | SeqMapReq fid elems =>
          -- .SeqMapReq: throwUnsupported → .error → contradicts hterm
          change Except.error _ = Except.ok result at hterm
          cases hterm

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
  | .InvokeIndirectReq _ _ _ _ _ _ => true  -- indirect invoke transfers control
  | .SeqMapReq _ _         => true  -- element application transfers control

/-- After a terminal StepResult, stepN returns immediately
    (does not consume more fuel). This is the early-exit property. -/
theorem terminal_step_classification (sr : StepResult)
    (hTerm : sr.isTerminal = true) :
    (exists vs, sr = .Ret vs) \/ sr = .Stuck
    \/ (exists fid args, sr = .CallReq fid args)
    \/ (exists addr fid args, sr = .CallIndirectReq addr fid args)
    \/ (exists fid args nd nargs ud, sr = .InvokeReq fid args nd nargs ud)
    \/ (exists addr sig args nd nargs ud, sr = .InvokeIndirectReq addr sig args nd nargs ud)
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
  | InvokeIndirectReq addr sig args nd nargs ud =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Exists.intro addr (Exists.intro sig (Exists.intro args (Exists.intro nd
        (Exists.intro nargs (Exists.intro ud rfl)))))))))))
  | SeqMapReq fid elems =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Exists.intro fid (Exists.intro elems rfl)))))))

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

#trustIrAxiomsExact TrustIr.undef_inspect_is_ub == []
