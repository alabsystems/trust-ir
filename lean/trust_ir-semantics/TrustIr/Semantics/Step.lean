-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Instruction dispatch: stepInst routes each instruction to its semantics.

import TrustIr.Inst
import TrustIr.Semantics.Arith
import TrustIr.Semantics.Compare
import TrustIr.Semantics.Cast
import TrustIr.Semantics.Control
import TrustIr.Semantics.Memory
import TrustIr.Semantics.Borrow
import TrustIr.Semantics.ARC
import TrustIr.Semantics.Atomic
import TrustIr.Semantics.Aggregate
import TrustIr.Semantics.Call
import TrustIr.Semantics.Frame
import TrustIr.Semantics.Coroutine

namespace TrustIr

/-!
# Instruction Step

`stepInst` dispatches each instruction variant to its per-category
semantic function. This is the central routing function for the
TrustIr formalization.

For non-terminator instructions, `stepInst` returns the ValueId
of the result (if any), or the ordered component ValueIds of a
two-result instruction (`Overflow`, `CmpXchg`).
For terminator instructions, it returns `some StepResult`.

## Design note

This two-level dispatch (stepInst for individual instructions,
stepBlock for basic blocks) follows the design document's
recommendation for Phase 1 completeness.
-/

/-- Result of stepping a single instruction.
    Non-terminators produce an optional ValueId (`value`), or — for the
    two-result instructions `Overflow` and `CmpXchg` — the ordered list of
    their component ValueIds (`values`). Terminators produce a StepResult.

    `values` is the ONE spelling of a multi-result instruction (WS2.24): the
    components are bound as separate SSA values, positionally, exactly as the
    Rust reference interpreter binds `InstrNode.results`
    (interpret.rs `bind_results(.., [result, flag])`). The former
    packed-`Value.aggregate` convention is deleted, not kept beside it. -/
inductive InstrResult where
  | value      : Option ValueId → InstrResult   -- non-terminator, ≤ 1 result
  | values     : List ValueId → InstrResult     -- non-terminator, multi-result
  | terminator : StepResult → InstrResult        -- terminator
  deriving Repr

/-- Lane-wise vector select. The mask must be a logical bool vector; physical
    integer masks remain a lowering artifact and are rejected here. -/
def semVectorSelectLanes
    : List Value → List Value → List Value → Except SemError (List Value)
  | [], [], [] => .ok []
  | .bool true :: maskRest, thenLane :: thenRest, _ :: elseRest => do
    let rest ← semVectorSelectLanes maskRest thenRest elseRest
    pure (thenLane :: rest)
  | .bool false :: maskRest, _ :: thenRest, elseLane :: elseRest => do
    let rest ← semVectorSelectLanes maskRest thenRest elseRest
    pure (elseLane :: rest)
  | _ :: _, [], _ => .error (.typeError "Vector Select: then lane count mismatch")
  | _ :: _, _, [] => .error (.typeError "Vector Select: else lane count mismatch")
  | [], _ :: _, _ => .error (.typeError "Vector Select: mask lane count mismatch")
  | [], _, _ :: _ => .error (.typeError "Vector Select: mask lane count mismatch")
  | _ :: _, _ :: _, _ :: _ => .error (.typeError "Vector Select: non-bool mask lane")

/-- A general semantic vector select. Arm lanes are transported, including
    poison lanes; only mask lanes are inspected by the selection itself. -/
def semVectorSelectValues (ty : Ty) (mask : List Value) (thenV elseV : Value) :
    Except SemError Value := do
  match ty with
  | .Vector count elemTy =>
    checkVectorShape count .Bool mask
    if thenV.isPoison || thenV.isUninit || elseV.isPoison || elseV.isUninit then
      throw (.ub "Vector Select: an arm is an uninitialized vector")
    match thenV, elseV with
    | .vector thenLanes, .vector elseLanes =>
      checkVectorShape count elemTy thenLanes
      checkVectorShape count elemTy elseLanes
      checkVectorLanes elemTy true thenLanes
      checkVectorLanes elemTy true elseLanes
      return .vector (← semVectorSelectLanes mask thenLanes elseLanes)
    | _, _ => throw (.typeError "Vector Select: vector mask with non-vector values")
  | _ => throw (.typeError "Vector Select: result type is not a vector")

/-- Null wide pointers retain the metadata kind at the selected target width.
    Only the two-zero constant spelling may use this value constructor. -/
def constNullFatPointer (kind : FatPtrKind) (model : ByteModel := .le64) : Value :=
  let metadata := match kind with
    | .Slice _ | .Str | .ContainerLen => Value.intAt model.pointerBits 0
    | .TraitObject _ | .ContainerVtable => .nullPtr
  .fatPtr 0 none metadata

mutual

/-- Runtime value of a constant at its declared type, width-resolving every
    float leaf whose type the declared type determines: a float literal takes
    the float type's value (`constFloatAt`, `Semantics/FloatFormat.lean`), a
    TUPLE constant resolves each field at its field type, and a VECTOR
    constant resolves each lane at the element type (the Rust interpreter's
    `constant_to_value` recursion), and an INTEGER leaf takes the declared
    type's bit width (`Ty.bitWidth`; the historical 64-bit default only when
    the type has none) — until WS2.19 a tuple's integer lanes kept the
    default, so `Const (Tuple [I8, ..]) (aggregate [int 2, ..])` bound an
    `int 64` lane where the reference interpreter binds `i8`, which the
    Lean-execution oracle measured as a value disagreement. An integer leaf
    binds its RESIDUE at that width (`Value.intAt`), the one integer
    representation of the model. Thin/fat nulls use their pointer value
    constructors, with target/kind-correct metadata. Other shapes retain the
    untyped fallback. This pure denotation grants no typing authority: runtime
    doors use `constValueAtChecked` to refuse unsupported pointer spellings. A
    float leaf the declared type does NOT determine is `constWidthAmbiguous`,
    which the `Const` step refuses. -/
def constValueAt (ty : Ty) (c : Constant) (model : ByteModel := .le64) : Value :=
  match c with
  | .fnDef fn =>
    match ty with
    | .Func sig => .fnDef sig fn
    | _ => Value.ofConstant c
  | .int i =>
    match ty with
    | .Ptr => if i == 0 then .nullPtr else Value.intAt model.pointerBits i
    | _ =>
      match ty.bitWidthFor model with
      | some w => Value.intAt w i
      | none => Value.intAt 64 i
  | .float f => .float (constFloatAt ty f)
  | .aggregate cs =>
    match ty with
    | .FatPtr kind =>
      match cs with
      | [.int data, .int metadata] =>
        if data == 0 && metadata == 0 then constNullFatPointer kind model
        else Value.ofConstant (.aggregate cs)
      | _ => Value.ofConstant (.aggregate cs)
    | .Tuple tys =>
      if tys.length == cs.length then .aggregate (constFieldsAt tys cs model)
      else Value.ofConstant (.aggregate cs)
    | _ => Value.ofConstant (.aggregate cs)
  | .vector cs =>
    match ty with
    | .Vector _ elemTy => .vector (constLanesAt elemTy cs model)
    | _ => Value.ofConstant (.vector cs)
  | c => Value.ofConstant c

/-- Tuple fields at their field types (positional). -/
def constFieldsAt (tys : List Ty) (cs : List Constant) (model : ByteModel := .le64) : List Value :=
  match tys, cs with
  | t :: ts, c :: cs => constValueAt t c model :: constFieldsAt ts cs model
  | _, cs => Value.ofConstantList cs

/-- Vector lanes at the element type. -/
def constLanesAt (elemTy : Ty) (cs : List Constant) (model : ByteModel := .le64) : List Value :=
  match cs with
  | [] => []
  | c :: cs => constValueAt elemTy c model :: constLanesAt elemTy cs model

end

mutual

/-- The pointer spellings the typed constant converter can materialize without
    inventing addresses. Inline tuple/vector positions recurse at their actual
    types; named positions are resolved by the contextual converter. This is
    deliberately not a replacement for complete constant/type validation. -/
def constPointerFormsSupported (ty : Ty) (c : Constant) : Bool :=
  match ty, c with
  | .Ptr, .int i => i == 0
  | .Ptr, _ => false
  | .FatPtr _, .aggregate [.int data, .int metadata] => data == 0 && metadata == 0
  | .FatPtr _, _ => false
  | .Tuple tys, .aggregate cs =>
    if tys.length == cs.length then constFieldPointerFormsSupported tys cs
    else false
  | .Vector _ elemTy, .vector cs => constLanePointerFormsSupported elemTy cs
  | _, _ => true

def constFieldPointerFormsSupported (tys : List Ty) (cs : List Constant) : Bool :=
  match tys, cs with
  | _ :: ts, .uninit :: cs => constFieldPointerFormsSupported ts cs
  | t :: ts, c :: cs => constPointerFormsSupported t c && constFieldPointerFormsSupported ts cs
  | _, _ => true

def constLanePointerFormsSupported (elemTy : Ty) (cs : List Constant) : Bool :=
  match cs with
  | [] => true
  | c :: cs => constPointerFormsSupported elemTy c && constLanePointerFormsSupported elemTy cs

end

mutual

/-- Does the constant hold a float leaf that is not exactly a binary32 value?
    Such a leaf has a DIFFERENT value at `F32` than at `F64`, so it cannot be
    materialized without knowing its width. -/
def constHasInexactFloat : Constant → Bool
  | .float f => !isExactIn .binary32 f
  | .aggregate cs | .vector cs | .sequence cs | .set cs => constListHasInexactFloat cs
  | .record fs => constFieldListHasInexactFloat fs
  | .closure _ caps => constListHasInexactFloat caps
  | _ => false

def constListHasInexactFloat : List Constant → Bool
  | [] => false
  | c :: cs => constHasInexactFloat c || constListHasInexactFloat cs

def constFieldListHasInexactFloat : List (String × Constant) → Bool
  | [] => false
  | (_, c) :: fs => constHasInexactFloat c || constFieldListHasInexactFloat fs

end

mutual

/-- Is a float leaf of `c` at a position whose float WIDTH the declared type
    `ty` does not determine (a struct / array / enum / sequence / set / record
    / closure field — those types name their element types by id, which the
    step rule cannot resolve), and not exactly binary32? Such a constant is
    refused (`unsupported.float`): materializing it unrounded would hand an
    `F32` field a value that is not a binary32 value (the Rust interpreter
    rounds it through the `StructDef`), and a pass-through (`Return`, `Copy`,
    `Call`) would carry that wrong value out unchecked. A binary32-exact leaf
    has the same value at `F32` and at `F64`, so it is admitted. -/
def constWidthAmbiguous (ty : Ty) (c : Constant) : Bool :=
  match c with
  | .float _ => false
  | .aggregate cs =>
    match ty with
    | .Tuple tys =>
      if tys.length == cs.length then constFieldsAmbiguous tys cs
      else constListHasInexactFloat cs
    | _ => constListHasInexactFloat cs
  | .vector cs =>
    match ty with
    | .Vector _ _ => false
    | _ => constListHasInexactFloat cs
  | c => constHasInexactFloat c

def constFieldsAmbiguous : List Ty → List Constant → Bool
  | t :: ts, c :: cs => constWidthAmbiguous t c || constFieldsAmbiguous ts cs
  | _, cs => constListHasInexactFloat cs

end

/-- The detail `Const` refuses a width-ambiguous float constant with. -/
def constWidthAmbiguousMsg : String :=
  "float constant of unresolved width (field of a struct/array/sequence/set/record/enum/closure constant) is not exactly binary32"

/-- Without a declaration table, a named aggregate's float widths remain
    unresolved. Preserve that explicit boundary before reporting the absent
    definition; no untyped aggregate value is manufactured. -/
def constMissingDefinition (ty : Ty) (c : Constant) (feature : UnsupportedFeature)
    (message : String) : Except SemError Value :=
  if constWidthAmbiguous ty c then
    .error (.unsupported .float constWidthAmbiguousMsg)
  else .error (.unsupported feature message)

mutual

/-- Checked constant conversion at a declared type. The pointer grammar is
    checked before other shape/width checks. An `Uninit` is admitted only by
    the direct-field helper of a root instruction tuple; recursive calls and
    global initializers pass `false`. Named types need the contextual door.

    This is constant/type conversion, not full module validation: integer
    literals retain the interpreter's residue semantics, and function target
    ownership/signatures and codec canonicality remain separate checks. -/
def constValueAtChecked (ty : Ty) (c : Constant) (model : ByteModel := .le64)
    (allowUninitFields : Bool := true) : Except SemError Value := do
  if !constPointerFormsSupported ty c then
    throw (.typeError "constant requires null pointer spellings and matching inline field census")
  match ty, c with
  -- The preceding grammar check proves the exact zero spelling in these
  -- branches; nonzero words and malformed pairs have already been refused.
  | .Ptr, .int _ => pure .nullPtr
  | .FatPtr kind, .aggregate _ => pure (constNullFatPointer kind model)
  | ty, .int i =>
    if ty.isInteger then pure (constValueAt ty (.int i) model)
    else throw (.typeError "integer constant requires an integer declared type")
  | .U128, .u128 value => pure (.int 128 (Int.ofNat value))
  | .Bool, .bool value => pure (.bool value)
  | .F16, .float value => pure (.float (constFloatAt .F16 value))
  | .F32, .float value => pure (.float (constFloatAt .F32 value))
  | .F64, .float value => pure (.float value)
  | .Unit, .phantomData => pure (.aggregate [])
  | .Func signature, .fnDef target => pure (.fnDef signature target)
  | .Tuple tys, .aggregate cs =>
    if tys.length != cs.length then
      throw (.typeError "tuple constant field count does not match its declared type")
    let fields ← constFieldsAtChecked tys cs model allowUninitFields
    pure (.aggregate fields)
  | .Vector count elemTy, .vector cs =>
    if (vectorScalarByteSize elemTy).isNone then
      throw (.typeError "vector constant requires an admitted scalar lane type")
    if count == 0 || cs.length != count then
      throw (.unsupported .vectorShape "vector constant lane count does not match its declared type")
    let lanes ← constLanesAtChecked elemTy cs model
    pure (.vector lanes)
  | .Array _ count, .bytes data _ =>
    if data.length != count then
      throw (.typeError "bytes constant length does not match its declared array type")
    constMissingDefinition ty c .enumDefTable
      "Const: a bytes constant's U8 element type needs the module's type table"
  | .Array _ count, .array cs | .Array _ count, .aggregate cs =>
    if cs.length != count then
      throw (.typeError "array constant length does not match its declared type")
    constMissingDefinition ty c .enumDefTable
      "Const: an array constant's element type needs the module's type table"
  | .Array _ count, .splat _ actual =>
    if actual != count then
      throw (.typeError "splat constant length does not match its declared array type")
    constMissingDefinition ty c .enumDefTable
      "Const: a splat constant's element type needs the module's type table"
  | .Struct _, .aggregate _ =>
    constMissingDefinition ty c .enumDefTable
      "Const: a struct constant's fields need the module's struct table"
  | .Enum _, .aggregate (.int _ :: _) =>
    constMissingDefinition ty c .enumDefTable
      "Const: an enum constant's fields need the module's enum table"
  | .Sequence _, .sequence _ | .Set _ _, .set _ | .Record _, .record _
  | .Record _, .aggregate _ =>
    constMissingDefinition ty c .enumDefTable
      "Const: named aggregate constants need the module's definition tables"
  | .Closure _, .closure _ _ =>
    constMissingDefinition ty c .closureDefTable
      "Const: a closure constant's captures need the module's closure table"
  | _, _ => throw (.typeError "constant does not match its declared type")

/-- Only direct root tuple fields may denote an unwritten lane. Every other
    field recurses with that permission revoked, even through nested tuples. -/
def constFieldsAtChecked (tys : List Ty) (cs : List Constant) (model : ByteModel)
    (allowUninit : Bool) : Except SemError (List Value) :=
  match tys, cs with
  | [], [] => pure []
  | _ :: tys, .uninit :: cs => do
    if !allowUninit then
      throw (.typeError "uninit is only a direct field of an instruction tuple/struct constant")
    let rest ← constFieldsAtChecked tys cs model allowUninit
    pure (.uninit :: rest)
  | ty :: tys, c :: cs => do
    let first ← constValueAtChecked ty c model false
    let rest ← constFieldsAtChecked tys cs model allowUninit
    pure (first :: rest)
  | _, _ => throw (.typeError "constant field count does not match its declared type")

def constLanesAtChecked (elemTy : Ty) (cs : List Constant) (model : ByteModel) :
    Except SemError (List Value) :=
  match cs with
  | [] => pure []
  | c :: cs => do
    let first ← constValueAtChecked elemTy c model false
    let rest ← constLanesAtChecked elemTy cs model
    pure (first :: rest)

end

/-- One operand of a failed assert's kind, as the unsigned value its panic
    message prints (plan item P). Read only on failure, exactly as the Rust
    reference interpreter reads it (`interpret.rs`, `assert_panic`): poison is
    UB, a non-integer is a type error (a validated module types it `usize`). -/
def assertOperandNat (v : ValueId) (role : String) : Sem Nat := do
  let x ← Sem.lookupValue v
  Sem.rejectPartial x "Assert"
  match x with
  | .int w i => pure (i % ((2 : Int) ^ w)).toNat
  | _ => Sem.throwTypeError s!"Assert: kind operand `{role}` is not an integer"

/-- Rust's `{:#x}`: `0x` and lowercase hex digits. -/
def hexAlt (n : Nat) : String := "0x" ++ String.mk (Nat.toDigits 16 n)

/-- The panic message of a FAILED assert of `kind` — byte-identical to the
    Rust reference interpreter's (`AssertKind::panic_message`), which is
    `core`'s text for every kind but `Unspecified`. -/
def assertFailMessage : AssertKind → Sem String
  | .BoundsCheck index len => do
    let i ← assertOperandNat index "index"
    let n ← assertOperandNat len "len"
    pure s!"index out of bounds: the len is {n} but the index is {i}"
  | .MisalignedPtr required found => do
    let r ← assertOperandNat required "required"
    let f ← assertOperandNat found "found"
    pure s!"misaligned pointer dereference: address must be a multiple of {hexAlt r} but is {hexAlt f}"
  | k => pure k.constantMessage

/-- The allocation a panic-location pointer names: the one it was DERIVED
    from (its provenance), and only while that allocation is live and the
    pointer lies inside the bytes it requested — the interpreter's
    `allocation.alive && pointer.offset < allocation.requested`. Never found
    by address, so a neighbour is never named. -/
def panicLocationAllocation (mem : Memory) (a : Addr) : Option AllocId → Option Allocation
  | some id =>
    match mem.lookup id with
    | some alloc =>
      if alloc.alive && alloc.base ≤ a && a - alloc.base < alloc.requested then some alloc
      else none
    | none => none
  | none => none

/-- Resolve a FAILED sited check's location (amendment P, wire v54;
    `docs/SPEC_RATIFICATIONS.md` §19.1 rule 4), exactly as the Rust reference
    interpreter does (`interpret.rs`, `resolve_panic_location`):

    * `global g` is `.global g 0` with NO state change: the global is not
      materialized (no `semGlobalAddr`, so the link-time-address refusal of a
      relocated initializer is never reached);
    * `value v` reads `v` (poison is UB); a pointer whose provenance names a
      live allocation it lies inside (`panicLocationAllocation`) is `.global
      g (a - base)` when that allocation backs a materialized global (the
      cache entry's allocation, as the interpreter matches
      `base.allocation == pointer.allocation`), else `.other`; null, a
      no-provenance pointer, or one outside its live allocation's requested
      bytes is UB; a non-pointer is a type error. -/
def resolvePanicLocation : PanicLocation → Sem PanicLoc
  | .global g => pure (.global g 0)
  | .value v => do
    let x ← Sem.lookupValue v
    Sem.rejectPartial x "Assert"
    match x with
    | .ptr a prov =>
      let s ← Sem.getState
      match panicLocationAllocation s.memory a prov with
      | some alloc =>
        match s.globals.find? (fun p => p.snd.snd == alloc.id) with
        | some (g, base, _) => pure (.global g (a - base))
        | none => pure .other
      | none => Sem.throwUB "Assert: panic location is null or dangling"
    | .nullPtr => Sem.throwUB "Assert: panic location is null or dangling"
    | _ => Sem.throwTypeError "Assert: panic location is not a pointer"

/-- A FAILED assert of `kind` with panic site `site`: compute its panic
    message (reading the kind's operands), then resolve the site's location
    (amendment P), then panic with both. The run is terminal and the entry is
    never executed. Every run ends in an error (`semAssertFail_run_not_ok` in
    `Proofs/TransformCorrectness.lean`). -/
def semAssertFail {α : Type} (kind : AssertKind) (site : Option PanicSite) : Sem α := do
  let msg ← assertFailMessage kind
  match site with
  | none => Sem.throwPanic msg
  | some site =>
    let loc ← resolvePanicLocation site.location
    Sem.throwPanic msg (some ⟨site.entry, loc⟩)

/-- Step a single TrustIr instruction.
    Routes to the appropriate per-category semantic function. -/
def stepInst (inst : Inst) (model : ByteModel := .le64) : Sem InstrResult := do
  match inst with
  -- Arithmetic
  | .BinOp op ty lhs rhs => do
    let vid ← semBinOp op ty lhs rhs
    pure (.value (some vid))

  | .UnOp op ty operand => do
    let vid ← semUnOp op ty operand
    pure (.value (some vid))

  | .Overflow op ty lhs rhs => do
    -- Two results, in Rust `result_tys` order: the wrapped value, then the
    -- overflow flag (bridge.rs `Inst::Overflow => [ty, Bool]`).
    let ids ← semOverflow op ty lhs rhs
    pure (.values [ids.1, ids.2])

  -- Comparison
  | .ICmp op ty lhs rhs => do
    let vid ← semICmpInst op ty lhs rhs model
    pure (.value (some vid))

  | .FCmp op ty lhs rhs => do
    let vid ← semFCmpInst op ty lhs rhs
    pure (.value (some vid))

  -- Casts
  | .Cast op srcTy dstTy operand => do
    let vid ← semCast op srcTy dstTy operand model
    pure (.value (some vid))

  -- Constants
  | .Const ty val =>
    -- A link-time address (`Constant.symbolAddr`, at any nesting depth) has
    -- no compile-time value: refuse it fail-closed, exactly as the reference
    -- interpreter's `constant_to_value` does (WS2.18).
    if val.hasSymbolAddr then
      Sem.throwUnsupported .linkTimeAddress
        "Const: a link-time symbol address has no compile-time value"
    else do
    -- One typed conversion door handles scalar, inline aggregate and vector
    -- values alike, including null pointers and their typed metadata. No
    -- integer fast path may bypass its explicit nonzero-pointer refusal.
    let v ← match constValueAtChecked ty val model with
      | .ok value => pure value
      | .error error => throw error
    let vid ← Sem.bindFresh v
    pure (.value (some vid))

  | .NullPtr => do
    let vid ← Sem.bindFresh .nullPtr
    pure (.value (some vid))

  | .Undef ty => do
    let vid ← Sem.bindFresh (.undef ty)
    pure (.value (some vid))

  -- Pseudo instructions
  | .Copy _ty operand => do
    let v ← Sem.lookupValue operand
    let vid ← Sem.bindFresh v
    pure (.value (some vid))

  | .Select ty cond thenVal elseVal => do
    -- Scalar Bool gates the whole value. A same-lane `<N x Bool>` mask selects
    -- lane-wise for every positive validator-admitted scalar-vector shape.
    let condV ← Sem.lookupValue cond
    -- The condition is inspected; the arms are transported (either may itself
    -- be a poison value passed through unchanged), so only `cond` is gated.
    Sem.rejectPartial condV "Select"
    let chosen ← match condV with
      | .bool true  => Sem.lookupValue thenVal
      | .bool false => Sem.lookupValue elseVal
      | .vector mask =>
        do
          let thenV ← Sem.lookupValue thenVal
          let elseV ← Sem.lookupValue elseVal
          match semVectorSelectValues ty mask thenV elseV with
          | .ok result => pure result
          | .error error => throw error
      | _ => Sem.throwTypeError "Select: condition is not bool"
    let vid ← Sem.bindFresh chosen
    pure (.value (some vid))

  -- Proof instructions
  | .Assume _cond =>
    -- Assume: add to assumption set (no-op in execution semantics)
    pure (.value none)

  | .Assert cond kind site => do
    -- Assert requires a Bool condition; anything else (including integers) is
    -- a type error, NOT a truthiness test. Matches the Rust reference
    -- interpreter (interpret.rs Inst::Assert: `as_bool` else TypeError) and
    -- validation (validate.rs: check_predicate_is_bool). A former int-accepting
    -- branch here ("nonzero passes") was a Lean-only relaxation; locked out by
    -- assert_int_condition_type_error_stable in ExecutableFixtures.lean.
    let condV ← Sem.lookupValue cond
    -- Inspecting a poison condition is UB (copy-propagates-poison use site).
    Sem.rejectPartial condV "Assert"
    match condV with
    | .bool true  => pure (.value none)
    -- Plan item P (wire v52): the panic names its kind; an `Unspecified`
    -- (pre-v52) assert keeps the historical "assertion failed". Amendment P
    -- (wire v54): a sited one also names its entry and resolved location.
    | .bool false => semAssertFail kind site
    | _           => Sem.throwTypeError "Assert: non-boolean condition"

  | .Unreachable =>
    pure (.terminator .Stuck)

  -- Control flow terminators
  | .Br target args => do
    let result ← semBr target args
    pure (.terminator result)

  | .CondBr cond thenTarget thenArgs elseTarget elseArgs => do
    let result ← semCondBr cond thenTarget thenArgs elseTarget elseArgs
    pure (.terminator result)

  | .Return values => do
    let result ← semReturn values
    pure (.terminator result)

  -- Memory (Phase 2)
  | .Load ty ptr volatile align => do
    -- A VOLATILE load keeps the strict all-initialized discipline
    -- (`strict := volatile`); a plain load participates in copy-propagates-
    -- poison. `align` is the declared alignment (checked by semLoad).
    let vid ← semLoad ty ptr volatile align model
    pure (.value (some vid))

  | .Store ty ptr value volatile align => do
    -- A VOLATILE store keeps the strict discipline (a poison value may not be
    -- stored volatilely); a plain store transports a `.partial` image verbatim.
    -- `align` is the declared alignment (checked by semStore).
    semStore ty ptr value volatile align model
    pure (.value none)

  | .Alloca ty count align => do
    let vid ← semAlloca ty count align model
    pure (.value (some vid))

  | .HeapAlloc ty count align origin => do
    let vid ← semHeapAlloc ty count origin align model
    pure (.value (some vid))

  | .GlobalAddr global => do
    let vid ← semGlobalAddr global model
    pure (.value (some vid))

  | .GEP pointeeTy base indices _inbounds => do
    -- `_inbounds` is the no-wrap claim; the poison-on-OOB refinement is deferred
    -- (MemoryProps §"GEP in-bounds"). semGEP computes the address either way.
    let vid ← semGEP pointeeTy base indices model
    pure (.value (some vid))

  | .PtrData ptrTy ptr => do
    let vid ← semPtrData ptrTy ptr model
    pure (.value (some vid))

  | .PtrMetadata ptrTy metadataTy ptr => do
    let vid ← semPtrMetadata ptrTy metadataTy ptr model
    pure (.value (some vid))

  | .PtrFromParts ptrTy metadataTy data metadata => do
    let vid ← semPtrFromParts ptrTy metadataTy data metadata model
    pure (.value (some vid))

  -- Atomics (Phase 4)
  | .AtomicLoad ty ptr ordering => do
    let vid ← semAtomicLoad ty ptr ordering model
    pure (.value (some vid))

  | .AtomicStore ty ptr value ordering => do
    semAtomicStore ty ptr value ordering model
    pure (.value none)

  | .AtomicRMW op ty ptr value ordering => do
    let vid ← semAtomicRMW op ty ptr value ordering model
    pure (.value (some vid))

  | .CmpXchg ty ptr expected desired success failure weak => do
    if weak then
      -- Crystal lane (D3): a weak compare-exchange may fail spuriously even
      -- when the comparison succeeds: a nondeterministic choice this
      -- executable model cannot make. Structured unsupported, never the strong
      -- step -- exactly what the reference interpreter does (interpret.rs:
      -- "Inst::CmpXchg weak: a spurious failure is nondeterministic and the
      -- reference interpreter has no oracle"). Refused BEFORE any operand is
      -- read, so the refusal is independent of the state, as the
      -- interpreter's is.
      Sem.throwUnsupported .weakCmpXchg
        "CmpXchg weak: a spurious failure is nondeterministic; the executable model has no oracle"
    else
      -- Two results, in Rust `result_tys` order: the loaded (old) value, then
      -- the success flag (bridge.rs `Inst::CmpXchg => [ty, Bool]`).
      let ids ← semCmpXchg ty ptr expected desired success failure model
      pure (.values [ids.1, ids.2])

  | .Fence ordering => do
    semFence ordering
    pure (.value none)

  -- Switch (Phase 4)
  | .Switch value default_ defaultArgs cases _exhaustive => do
    let result ← semSwitch value default_ defaultArgs cases
    pure (.terminator result)

  -- Calls (Phase 4): resolve arguments and produce a CallReq for
  -- the evaluator to handle frame push/pop.
  | .Call calleeId argIds => do
    let args ← argIds.mapM Sem.lookupValue
    pure (.terminator (.CallReq calleeId args))

  | .CallCannotUnwind _ _ | .CallIndirectCannotUnwind _ _ _ _ =>
    Sem.throwUnsupported .callUnwindBoundary
      "the executable model cannot enforce a host-unwind call boundary"

  | .CallIndirect calleeValId sig argIds _conv => do
    let calleeVal ← Sem.lookupValue calleeValId
    let addr ← match calleeVal with
      | .ptr a _ => pure a
      | .nullPtr => Sem.throwUB "CallIndirect: null function pointer"
      | _        => Sem.throwTypeError "CallIndirect: callee is not a pointer"
    let args ← argIds.mapM Sem.lookupValue
    -- The evaluator resolves addr to a FuncId via the function pointer table
    -- and checks that the callee matches sig.
    pure (.terminator (.CallIndirectReq addr sig args))

  -- Sequence element-op map (give-back loop instruction). Applying the
  -- element function per element is INTERPROCEDURAL, so stepInst validates
  -- the operand and returns a SeqMapReq for the contextual evaluator
  -- (mirrors the Call/CallReq split). The bare single-function evaluators
  -- fail closed with a structured unsupported error.
  | .SeqMap _ty seq fwd => do
    let seqVal ← Sem.lookupValue seq
    match seqVal with
    | .sequence elems => pure (.terminator (.SeqMapReq fwd elems))
    | _ => Sem.throwTypeError "SeqMap: operand is not a sequence"

  -- Aggregates (Phase 4)
  | .ExtractField ty aggregate field => do
    let vid ← semExtractField ty aggregate field
    pure (.value (some vid))

  | .InsertField ty aggregate field value => do
    let vid ← semInsertField ty aggregate field value
    pure (.value (some vid))

  | .MakeClosure _ _ _ =>
    Sem.throwUnsupported .closureDefTable "MakeClosure: operational closure tables and physical signatures are not modeled"

  | .MakeAggregate ty variant fields => do
    let vid ← semMakeAggregate ty variant fields
    pure (.value (some vid))

  | .ArraySplat ty value => do
    let vid ← semArraySplat ty value
    pure (.value (some vid))

  | .ExtractElement ty array index => do
    let vid ← semExtractElement ty array index
    pure (.value (some vid))

  | .InsertElement ty array index value => do
    let vid ← semInsertElement ty array index value
    pure (.value (some vid))

  -- Sequence element-op loops (give-back / Aeneas loopFwd)
  | .SeqMapAddK ty seq k => do
    let vid ← semSeqMapAddK ty seq k
    pure (.value (some vid))

  | .SeqMapNot ty seq => do
    let vid ← semSeqMapNot ty seq
    pure (.value (some vid))

  -- Borrow (Phase 3)
  | .Borrow ptr     => do
    let vid ← semBorrow ptr
    pure (.value (some vid))
  | .BorrowMut ptr  => do
    let vid ← semBorrowMut ptr
    pure (.value (some vid))
  | .EndBorrow ptr  => do
    semEndBorrow ptr
    pure (.value none)

  -- ARC (Phase 3)
  | .Retain ptr     => do
    semRetain ptr
    pure (.value none)
  | .Release ptr    => do
    semRelease ptr
    pure (.value none)
  | .IsUnique ptr   => do
    let vid ← semIsUnique ptr
    pure (.value (some vid))

  -- Binding frames (TrustIr#32): typed quantifier lowering.
  | .OpenFrame def_ => do
    let vid ← semOpenFrame def_
    pure (.value (some vid))
  | .BindSlot frame slot value => do
    let vid ← semBindSlot frame slot value
    pure (.value (some vid))
  | .LoadSlot frame slot ty => do
    let vid ← semLoadSlot frame slot ty
    pure (.value (some vid))
  | .CloseFrame frame => do
    semCloseFrame frame
    pure (.value none)

  -- Heap deallocation (TrustIr#54). Mirrors Rust Inst::Dealloc.
  | .Dealloc ptr => do
    semDealloc ptr
    pure (.value none)

  -- Bulk memory (WS3.20, F-057). Mirrors Rust Inst::MemCopy / Inst::MemSet.
  | .MemCopy dst src bytes overlap => do
    semMemCopy dst src bytes overlap model
    pure (.value none)
  | .MemSet dst byte bytes => do
    semMemSet dst byte bytes model
    pure (.value none)

  -- Coroutine suspend: store the resume state index into the frame, then
  -- return the yielded value (a terminator; the resumer sees a plain Ret).
  | .CoroSuspend frame stateSlot nextState value => do
    let result ← semCoroSuspend frame stateSlot nextState value model
    pure (.terminator result)

  -- Exception handling. This bare step is the panic=abort projection
  -- (`PanicStrategy.abort`): an Invoke requests the call exactly like Call and
  -- the evaluator takes the normal edge. Under `PanicStrategy.unwind` the
  -- contextual evaluator (`Semantics/Eval.lean`, amendment D Part 2) catches
  -- an unwinding at the invoke-family terminators, binds a landing pad's
  -- results and re-raises at `Resume`.
  | .Invoke callee argIds normalDest normalArgs unwindDest => do
    let args ← argIds.mapM Sem.lookupValue
    pure (.terminator (.InvokeReq callee args normalDest normalArgs unwindDest))

  -- Amendment D, Part 2 (wire v56): `CallIndirect`'s unwinding twin. The
  -- callee value is resolved exactly as `CallIndirect`'s; the evaluator
  -- resolves the address, checks the signature, runs the call and takes the
  -- normal edge (panic=abort projection), exactly as for `InvokeReq`.
  | .InvokeIndirect calleeValId sig argIds _conv normalDest normalArgs unwindDest => do
    let calleeVal ← Sem.lookupValue calleeValId
    let addr ← match calleeVal with
      | .ptr a _ => pure a
      | .nullPtr => Sem.throwUB "InvokeIndirect: null function pointer"
      | _        => Sem.throwTypeError "InvokeIndirect: callee is not a pointer"
    let args ← argIds.mapM Sem.lookupValue
    pure (.terminator (.InvokeIndirectReq addr sig args normalDest normalArgs unwindDest))

  -- Amendment P (wire v54): a sited check with an unwind edge. A passing
  -- check continues to `normalDest`; a failing one is the sited panic. Like
  -- `Invoke` under the panic=abort projection, the unwind edge is never
  -- taken (`assertInvoke_is_sited_assert_then_br`).
  | .AssertInvoke cond kind site normalDest normalArgs _unwindDest => do
    let condV ← Sem.lookupValue cond
    Sem.rejectPartial condV "Assert"
    match condV with
    | .bool true  => pure (.terminator (← semBr normalDest normalArgs))
    | .bool false => semAssertFail kind (some site)
    | _           => Sem.throwTypeError "Assert: non-boolean condition"

  | .LandingPad _isCleanup _catchTypeIndices =>
    -- A landing pad is only entered via an `Invoke`'s unwind edge, which the
    -- panic=abort projection never takes. Reaching one any other way is a
    -- module the validator refuses (`MisplacedLandingPad`), and the pad's two
    -- results (exception pointer, type selector) would read registers no
    -- unwinder loaded. FAIL CLOSED, mirroring interpret.rs (WS2.5): binding a
    -- fabricated `(null, 0)` would fill a missing value and let execution
    -- continue as if an exception were in hand (WS2.24 retired the packed
    -- aggregate that used to carry that fabrication).
    Sem.throwUnsupported .hostUnwind
      "landingpad entered without an unwind edge (unwinding is not modelled; panic=abort)"

  | .Drop _ty _ptr =>
    -- Running a destructor is outside the executable model: it frees, and it can
    -- run arbitrary user code. Structured unsupported, not silent success --
    -- exactly what the reference interpreter does (interpret.rs: "Inst::Drop: no
    -- destructor model in the reference interpreter"), and for the same reason:
    -- a no-op here would evaluate a DIFFERENT program than the one written, in
    -- the direction that invents agreement.
    Sem.throwUnsupported .destructor
      "Drop: the executable model does not model destructors"

  | .DropInvoke _ty _ptr _normalDest _normalArgs _unwindDest =>
    -- The unwinding twin of `Drop` (amendment D), refused exactly as `Drop`.
    Sem.throwUnsupported .destructor
      "DropInvoke: the executable model does not model destructors"

  | .Resume _exn =>
    -- Re-raising to the host unwinder is outside the executable model: a
    -- resume is only reachable after an unwind edge was taken, which never
    -- happens under evaluation. Structured unsupported, not silent success.
    Sem.throwUnsupported .hostUnwind
      "Resume: the executable model does not model in-flight host exceptions"

  -- Dialect op (TrustIr#54). Core TrustIr semantics do not interpret dialect
  -- ops: dialect-aware passes must lower them to core instructions
  -- before evaluation. Running stepInst on a DialectOp is a structured
  -- unsupported-subset error
  -- (the lowering-correctness obligation in TrustIr.Semantics.Dialect is
  -- what producer repos discharge). The op payload is preserved in the
  -- error message for diagnosability.
  | .DialectOp op =>
    Sem.throwUnsupported .dialectOp
      ("stepInst: DialectOp " ++ op.qualifiedName
        ++ " must be lowered to core TrustIr instructions before evaluation")

/-- Transport a computed value through the actual fresh-value binding and
instruction result constructor. This holds for every machine state: only the
local map and next-value cursor change, while every error remains an error.
It does not assert a state well-formedness or fresh-id invariant. -/
theorem stepinst_value_result_transport (r : Except TrustIr.SemError TrustIr.Value)
    (state : TrustIr.MachineState) :
    TrustIr.Sem.run
      (@StateT.bind TrustIr.MachineState (Except TrustIr.SemError) (@Except.instMonad TrustIr.SemError)
        TrustIr.ValueId TrustIr.InstrResult
        (match r with
          | .ok value => TrustIr.Sem.bindFresh value
          | .error e => (fun _ => Except.error e))
        (fun vid => @StateT.pure TrustIr.MachineState (Except TrustIr.SemError)
          (@Except.instMonad TrustIr.SemError) TrustIr.InstrResult
          (TrustIr.InstrResult.value (some vid)))) state =
    (match r with
      | .ok value =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk state.nextValueId)),
          { state with
              locals := state.locals.set (TrustIr.ValueId.mk state.nextValueId) value,
              nextValueId := Nat.add state.nextValueId 1 })
      | .error e => Except.error e) := Except.rec
  (fun e => @Eq.refl (Except TrustIr.SemError (TrustIr.InstrResult × TrustIr.MachineState))
    (Except.error e))
  (fun value => @Eq.refl (Except TrustIr.SemError (TrustIr.InstrResult × TrustIr.MachineState))
    (Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk state.nextValueId)),
      { state with
          locals := state.locals.set (TrustIr.ValueId.mk state.nextValueId) value,
          nextValueId := Nat.add state.nextValueId 1 }))) r

end TrustIr
