-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Aggregate operation semantics: struct/array construction and access.
-- Phase 4 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 4
--
-- Struct/tuple products retain Value.aggregate; arrays use compact
-- Value.array trees. Field and element access remain distinct operations.

import TrustIr.Inst
import TrustIr.Semantics.Arith
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Aggregate Operation Semantics

## Overview

TrustIr aggregates (structs, arrays, tuples) are represented uniformly
as field products or compact `Value.array` values.  The instruction set provides
four operations:

1. **ExtractField**: get a field from a struct aggregate by index
2. **InsertField**: set a field in a struct aggregate by index
3. **ExtractElement**: get an element from an array aggregate by
   dynamic index
4. **InsertElement**: set an element in an array aggregate by
   dynamic index

## Struct vs Array

Both structs and arrays use the same `Value.aggregate` representation.
The distinction is in the instruction used:

- `ExtractField`/`InsertField` use a **static** field index (Nat).
  They are intended for struct access where the field index is known
  at compile time.
- `ExtractElement`/`InsertElement` use a **dynamic** index (ValueId).
  They are intended for array access where the index may be computed.

Both produce bounds-checking errors for out-of-range indices.

## MakeAggregate (StructInit)

Since WS3.5 `MakeAggregate` is the explicit register-level constructor:
`semMakeAggregate` looks up its lanes and binds `buildAggregate lanes`
for a struct / tuple / array (enum and record construction are an honest
partial, see there). Before it, struct construction was done by composing
InsertField operations on an initial `undef` aggregate, or by the Const
instruction with an aggregate constant; both spellings remain.

## Design note

The aggregate semantics are pure functions on field products and compact
array values.  No memory access is involved -- aggregate values
live in SSA registers.  Memory-backed aggregates are handled by
Load/Store with byte encoding in `Memory.lean`.
-/

-- =================================================================
-- Aggregate helpers (pure functions)
-- =================================================================

/-- Get a field from an aggregate or named record by static index.
    Returns none if the index is out of bounds or the value is not
    an aggregate/record. Record labels remain attached to the container. -/
def getField (v : Value) (field : Nat) : Option Value :=
  match v with
  | .aggregate fields => trustIrListGet? fields field
  | .record fields => (trustIrListGet? fields field).map Prod.snd
  | _ => none

/-- Set a field in an aggregate or named record by static index.
    Returns none if the index is out of bounds or the value is not
    an aggregate/record. A record update preserves its declaration labels and
    field order, changing only the selected value. -/
def setField (v : Value) (field : Nat) (newVal : Value) : Option Value :=
  match v with
  | .aggregate fields =>
    if field < fields.length then
      some (.aggregate (fields.set field newVal))
    else none
  | .record fields =>
    match trustIrListGet? fields field with
    | some (name, _) => some (.record (fields.set field (name, newVal)))
    | none => none
  | _ => none

/-- Get an element from an aggregate or a sequence by dynamic index.

    WS3.17 (F-051): the `.sequence` arm mirrors the reference interpreter,
    whose `eval_extract_element` reads `Vector | Array | Sequence | Aggregate`
    payloads alike (crates/trust-ir/src/interpret.rs). Until this arm existed
    the Lean model TYPE-ERRORED on a sequence read that the Rust engine
    executed, so the two engines disagreed on a construct both the format and
    `lowering-target-subset.md` admit. -/
def getElement (v : Value) (index : Nat) : Option Value :=
  match v with
  | .array elems => elems.get? index
  | .aggregate elems => trustIrListGet? elems index
  | .sequence elems => trustIrListGet? elems index
  | _ => none

/-- Set an element in an aggregate or a sequence by dynamic index. The result
    keeps the operand's OWN constructor — a sequence write yields a sequence,
    never an aggregate — so the nominal distinctness the step relation relies
    on (see `Value`) survives the update. -/
def setElement (v : Value) (index : Nat) (newVal : Value) : Option Value :=
  match v with
  | .array elems => (elems.set? index newVal).map Value.array
  | .aggregate elems =>
    if index < elems.length then
      some (.aggregate (elems.set index newVal))
    else none
  | .sequence elems =>
    if index < elems.length then
      some (.sequence (elems.set index newVal))
    else none
  | _ => none

/-- Runtime payload check for vector ExtractElement, whose declared type is
    the lane result type.  The executable subset is the integer lanes of
    `Ty.executableIntLane?` (Arith.lean, the one statement of the integer
    shapes: the lane types of the x86-64 vector-compare cells, signed and
    unsigned) and the logical bool masks v16bool / v8bool / v4bool / v2bool.
    The bool lane counts match the `vector.mask_to_bits` dialect contract
    (which accepts <16/8/4/2 x bool>), so the dialect's `mask_to_bits`
    lowering — a per-lane `ExtractElement .Bool` chain — is executable at every
    mask shape the dialect admits. (Until 2026-09-30 this check, the lane-value
    check and the payload check each listed their own integer shapes, and they
    drifted twice: the i8 / i16 rows were missing here while the payload check
    admitted those shapes, and every check omitted the unsigned lane types.) -/
def Ty.executableVectorLanePayloadMatches (elemTy : Ty)
    (lanes : List Value) : _root_.Bool :=
  match elemTy.executableIntLane? with
  | some (n, width) => lanes.length == n && lanes.all (Value.isIntWidth width)
  | none =>
    match elemTy with
    | .Bool =>
      (lanes.length == 16 || lanes.length == 8 || lanes.length == 4 || lanes.length == 2)
        && lanes.all Value.isBool
    | _ => false

/-- Runtime lane-value check for vector InsertElement: a lane of
    `Ty.executableIntLane?`'s width, or a bool. -/
def Ty.executableVectorLaneValueMatches (elemTy : Ty)
    (v : Value) : _root_.Bool :=
  match elemTy.executableIntLane? with
  | some (_, width) => Value.isIntWidth width v
  | none =>
    match elemTy with
    | .Bool => Value.isBool v
    | _ => false

/-- Extract only the selected lane of an admitted scalar vector. The
    instruction carries the result lane type, not a declared vector census;
    bounds therefore use the actual list. Unselected lanes are not inspected.
    The backend-shaped `executable*` classifiers above stay unchanged. -/
def getVectorElement (elemTy : Ty) (v : Value) (index : Nat)
    : Except SemError Value :=
  match v with
  | .vector lanes =>
    if !elemTy.semanticVectorLane || lanes.isEmpty then
      .error (.unsupported .vectorShape "ExtractElement: unadmitted or empty vector")
    else do
      let lane ← match trustIrListGet? lanes index with
        | some lane => pure lane
        | none => throw (.ub "ExtractElement: vector index out of bounds")
      checkVectorLaneType elemTy true lane
      pure lane
  | _ => .error (.typeError "ExtractElement: operand is not a vector")

/-- Set a lane of any positive admitted scalar-vector shape.
    InsertElement declares the vector result/source type, so the lane type is
    derived from `Ty.Vector lanes elemTy`. -/
def setVectorElement (vectorTy : Ty) (v : Value) (index : Nat)
    (newVal : Value) : Except SemError Value :=
  match v with
  | .vector lanes => do
    match vectorTy with
    | .Vector count elemTy =>
      checkVectorShape count elemTy lanes
      checkVectorLaneType elemTy false newVal
      let previous ← match trustIrListGet? lanes index with
        | some lane => pure lane
        | none => throw (.ub "InsertElement: vector index out of bounds")
      checkVectorLaneType elemTy true previous
      pure (.vector (lanes.set index newVal))
    | _ => throw (.typeError "InsertElement: declared type is not a vector")
  | _ => .error (.typeError "InsertElement: operand is not a vector")

/-- Build an aggregate value from a list of values.
    This is the pure constructor for struct/array initialization. -/
def buildAggregate (fields : List Value) : Value :=
  .aggregate fields

/-- Get the number of fields/elements in an aggregate. -/
def aggregateLength (v : Value) : Option Nat :=
  match v with
  | .aggregate fields => some fields.length
  | _ => none

-- =================================================================
-- ExtractField semantics
-- =================================================================

/-- Evaluate an ExtractField instruction.
    Extracts a field from a struct aggregate by static index.

    The `ty` parameter is the expected type of the extracted field
    (used for type checking in future phases).

    Mirrors Rust `Inst::ExtractField`. -/
def semExtractField (_ty : Ty) (aggregateId : ValueId) (field : Nat)
    : Sem ValueId := do
  let aggVal ← Sem.lookupValue aggregateId
  -- Projecting a field inspects the aggregate: a poison operand is UB.
  Sem.rejectPartial aggVal "ExtractField"
  match getField aggVal field with
  | some v =>
    -- Crystal lane (E3b): reading an UNWRITTEN lane (`.uninit`) is undefined behaviour,
    -- exactly the Rust reference interpreter's `eval_extract_field`, which faults on that
    -- lane and on no other; every other lane binds as before. (The lane spelled this
    -- `Sem.rejectPartial v`, which on main would ALSO fault a `.undef` lane -- main's WS2.10
    -- made `.undef` poison there -- while the interpreter transports it.)
    if v.isUninit then
      Sem.throwUB "ExtractField: read of an unwritten aggregate lane (uninit)"
    else
      Sem.bindFresh v
  | none   =>
    match aggVal with
    | .aggregate _ | .record _ =>
      Sem.throwUB "ExtractField: field index out of bounds"
    | _ =>
      Sem.throwTypeError "ExtractField: operand is not an aggregate"

-- =================================================================
-- InsertField semantics
-- =================================================================

/-- Evaluate an InsertField instruction.
    Creates a new aggregate with the given field replaced.

    This is a non-destructive update: the original aggregate is
    not modified (SSA form).

    Lane 0 of an ENUM value is its discriminant (the `[tag, fields..]` value
    model). Rewriting it would leave the old variant's payload under the new
    tag, so it throws UB — the mirror of the Rust validator's
    `FieldAccessInvalid` "insert_field cannot rewrite an enum discriminant" and
    of the reference interpreter's `UndefinedBehavior` (roadmap WS2.2 item 2).
    A variant is constructed whole with `Const`.

    NOT mirrored (B3 depth ledger): the lane TYPE. `MachineState` carries no
    `EnumDef` table and there is no value-against-type conformance predicate,
    so neither this nor `semExtractField` checks that the lane has the declared
    type, for any aggregate kind. A lane beyond the ACTIVE variant's arity is
    already UB, because the flat `.aggregate` has `1 + |fields(active)|`
    elements.

    Mirrors Rust `Inst::InsertField`. -/
def semInsertField (ty : Ty) (aggregateId : ValueId) (field : Nat)
    (valueId : ValueId) : Sem ValueId := do
  let aggVal ← Sem.lookupValue aggregateId
  let newFieldVal ← Sem.lookupValue valueId
  -- Both the aggregate and the inserted value are inspected: poison is UB.
  Sem.rejectPartial aggVal "InsertField"
  Sem.rejectPartial newFieldVal "InsertField"
  -- `InsertField`'s `ty` is the AGGREGATE (result) type (Rust `inst.rs`,
  -- `Inst::InsertField`), so an enum write sees `.Enum _`.
  match ty, field with
  | .Enum _, 0 =>
    Sem.throwUB "InsertField: cannot rewrite an enum discriminant (lane 0); construct the variant with Const"
  | _, _ =>
    match setField aggVal field newFieldVal with
    | some v => Sem.bindFresh v
    | none   =>
      match aggVal with
      | .aggregate _ | .record _ =>
        Sem.throwUB "InsertField: field index out of bounds"
      | _ =>
        Sem.throwTypeError "InsertField: operand is not an aggregate"

-- =================================================================
-- MakeAggregate semantics (WS3.5)
-- =================================================================

/-- The aggregate types whose `MakeAggregate` the executable model BUILDS as
    a plain `Value.aggregate` of its lanes: structs and tuples. Arrays use
    their own compact element-addressable carrier. Enum and
    record construction are the honest partial named in `semMakeAggregate`;
    everything else is not a type the instruction builds at all. -/
def Ty.fieldAggregate : Ty → _root_.Bool
  | .Struct _  => true
  | .Tuple _   => true
  | _          => false

/-- Look up every lane operand in order, rejecting poison at each: the result
    of a `MakeAggregate` is documented as FULLY initialised, so it may not be
    assembled out of an uninitialised part (the Rust reference interpreter's
    `reject_partial` per lane). Structurally recursive rather than `mapM` so
    the nonlocal-state proof (`TransformCorrectness`) decomposes by
    induction on the lane list. -/
def lookupLanes : List ValueId → Sem (List Value)
  | [] => pure []
  | id :: rest => do
    let v ← Sem.lookupValue id
    Sem.rejectPartial v "MakeAggregate"
    let vs ← lookupLanes rest
    pure (v :: vs)

/-- Evaluate a MakeAggregate instruction: a fresh aggregate VALUE out of
    register lanes.

    For a struct / tuple / array (`variant = none`) the result is
    `buildAggregate lanes` — byte-for-byte the value `Const` would produce
    for the same lanes, so `ExtractField` reads it identically
    (`extract_make_aggregate`, `Proofs/AggregateProps.lean`).

    HONEST PARTIAL (B3 depth ledger): the machine state carries no module
    definition tables, so
    * an ENUM construction cannot compute its tag lane
      (`discriminants[variant]` at the canonical tag repr), and
    * a RECORD construction cannot name its lanes (`Value.record` is
      field-name keyed),
    and both fail closed as `unsupported.enum_def_table` rather than
    fabricate a tag or a name. The Rust reference interpreter resolves both
    through the module. A `variant` on a non-enum, or its absence on an enum,
    is a type error, exactly as `validate_module` refuses it
    (`InvalidMakeAggregate`), and so is any type the instruction does not
    build (a scalar, `Vector`, `FatPtr`, `Closure`, `Sequence`, `Set`, …).

    NOT mirrored (same ledger line as `semInsertField`): the lane TYPES and
    the lane COUNT against the definition — there is no value-against-type
    conformance predicate here.

    Mirrors Rust `Inst::MakeAggregate`. -/
def semMakeAggregate (ty : Ty) (variant : Option Nat) (fieldIds : List ValueId)
    : Sem ValueId := do
  let lanes ← lookupLanes fieldIds
  match ty, variant with
  | .Enum _, some _ =>
    Sem.throwUnsupported .enumDefTable
      "MakeAggregate: enum construction needs the module's discriminant table, which the executable model does not carry"
  | .Enum _, none =>
    Sem.throwTypeError "MakeAggregate: an enum construction needs a variant index"
  | .Record _, none =>
    Sem.throwUnsupported .enumDefTable
      "MakeAggregate: record construction needs the module's record definition (field names), which the executable model does not carry"
  | _, some _ =>
    Sem.throwTypeError "MakeAggregate: a variant index is only meaningful for an enum"
  | .Struct _, none => Sem.bindFresh (buildAggregate lanes)
  | .Tuple _, none => Sem.bindFresh (buildAggregate lanes)
  | .Array _ count, none =>
    if lanes.length != count then
      Sem.throwTypeError "MakeAggregate: array lane count does not match its type"
    else Sem.bindFresh (.array (CompactArray.Packed.ofArray lanes.toArray))
  -- Vectors keep InsertElement, fat pointers PtrFromParts; closures,
  -- sequences, sets, dialects, handles and every scalar have no lane rule
  -- (mirrors the validator's `InvalidMakeAggregate`).
  | _, none =>
    Sem.throwTypeError "MakeAggregate: not a type make_aggregate builds (struct, tuple, record, array or enum)"

-- =================================================================
-- ArraySplat semantics (v50)
-- =================================================================

/-- Evaluate an ArraySplat instruction: `n` copies of one register value,
    the array `[v; n]` of type `ty = Array e n`.

    The element is embedded in every lane, which INSPECTS it (a poison
    element is refused, as `MakeAggregate` refuses a poison lane and
    `semInsertElement` a poison element). The result is
    one compact uniform `Value.array`, so
    `ExtractElement` reads `v` at every in-bounds index
    (`extract_array_splat`, Proofs/AggregateProps.lean). A type that is not an
    array is a type error, as `validate_module` refuses it
    (`InvalidArraySplat`).

    The contextual step checks the operand's exact original declaration against
    the element type. Bare stepping lacks that table. The validator separately
    enforces register canonicality (`n ≥ 1`).

    Mirrors Rust `Inst::ArraySplat`. -/
def semArraySplat (ty : Ty) (valueId : ValueId) : Sem ValueId := do
  let v ← Sem.lookupValue valueId
  Sem.rejectPartial v "ArraySplat"
  match ty with
  | .Array _ n => Sem.bindFresh (.array (CompactArray.Packed.uniform n v))
  | _ => Sem.throwTypeError "ArraySplat: not an array type"

-- =================================================================
-- ExtractElement semantics
-- =================================================================

/-- Evaluate an ExtractElement instruction.
    Extracts an element from an array aggregate by dynamic index.

    The index is a runtime value (ValueId), so bounds checking is
    a runtime safety check.

    Mirrors Rust `Inst::ExtractElement`. -/
def semExtractElementUsing (indexOf : Value → Sem Nat)
    (ty : Ty) (arrayId indexId : ValueId) : Sem ValueId := do
  let arrVal ← Sem.lookupValue arrayId
  let idxVal ← Sem.lookupValue indexId
  let idx ← indexOf idxVal
  match arrVal with
  | .vector _ =>
    match getVectorElement ty arrVal idx with
    | .ok v => Sem.bindFresh v
    | .error e => throw e
  | _ =>
    match getElement arrVal idx with
    | some v => Sem.bindFresh v
    | none   =>
      match arrVal with
      | .array _ | .aggregate _ =>
        Sem.throwUB "ExtractElement: index out of bounds"
      -- WS3.17: an out-of-range SEQUENCE read is run-time UB, exactly as for
      -- an aggregate — not a type error. The reference interpreter answers
      -- `UndefinedBehavior "element {i} is out of bounds"` here.
      | .sequence _ =>
        Sem.throwUB "ExtractElement: index out of bounds"
      | _ =>
        Sem.throwTypeError "ExtractElement: operand is not an aggregate or vector"

/-- The historical bare helper has no source declarations; contextual
    execution supplies the declared integer reader to `semExtractElementUsing`. -/
def semExtractElement (ty : Ty) (arrayId indexId : ValueId) : Sem ValueId :=
  semExtractElementUsing (fun idxVal => do
    Sem.rejectPartial idxVal "ExtractElement index"
    match idxVal with
    | .int _ n =>
      if n < 0 then Sem.throwUB "ExtractElement: negative index" else pure n.toNat
    | _ => Sem.throwTypeError "ExtractElement: index is not an integer") ty arrayId indexId

-- =================================================================
-- InsertElement semantics
-- =================================================================

/-- Evaluate an InsertElement instruction.
    Creates a new array with the given element replaced.

    This is a non-destructive update: the original array is not
    modified (SSA form).

    Mirrors Rust `Inst::InsertElement`. -/
def semInsertElementUsing (indexOf : Value → Sem Nat)
    (ty : Ty) (arrayId indexId valueId : ValueId) : Sem ValueId := do
  let arrVal ← Sem.lookupValue arrayId
  let idxVal ← Sem.lookupValue indexId
  let newElemVal ← Sem.lookupValue valueId
  let idx ← indexOf idxVal
  match arrVal with
  | .vector _ =>
    -- A vector lane is checked by `setVectorElement`, which refuses any
    -- value that is not a lane of the declared type (poison included).
    match setVectorElement ty arrVal idx newElemVal with
    | .ok v => Sem.bindFresh v
    | .error e => throw e
  | _ => do
    -- Embedding an element INSPECTS it, exactly as `semInsertField` does: a
    -- poison element inside a defined array would carry poison past every
    -- top-level check (a call/return boundary sees only the array). Mirror
    -- of interpret.rs `eval_insert_element` (roadmap WS2.10 review).
    Sem.rejectPartial newElemVal "InsertElement"
    match setElement arrVal idx newElemVal with
    | some v => Sem.bindFresh v
    | none   =>
      match arrVal with
      | .array _ | .aggregate _ =>
        Sem.throwUB "InsertElement: index out of bounds"
      -- WS3.17: as for the read, an out-of-range sequence WRITE is UB.
      | .sequence _ =>
        Sem.throwUB "InsertElement: index out of bounds"
      | _ =>
        Sem.throwTypeError "InsertElement: operand is not an aggregate or vector"

/-- Bare insertion retains its untyped index contract. -/
def semInsertElement (ty : Ty) (arrayId indexId valueId : ValueId) : Sem ValueId :=
  semInsertElementUsing (fun idxVal => do
    Sem.rejectPartial idxVal "InsertElement index"
    match idxVal with
    | .int _ n =>
      if n < 0 then Sem.throwUB "InsertElement: negative index" else pure n.toNat
    | _ => Sem.throwTypeError "InsertElement: index is not an integer") ty arrayId indexId valueId

-- =================================================================
-- Aggregate predicates (for theorem statements)
-- =================================================================

/-- Predicate: a value is an aggregate with at least `n` fields. -/
def hasFields (v : Value) (n : Nat) : Prop :=
  match v with
  | .aggregate fields => fields.length >= n
  | _ => False

/-- Predicate: a value is an aggregate (any number of fields). -/
def isAggregate (v : Value) : Prop :=
  match v with
  | .aggregate _ => True
  | _ => False

/-- Predicate: ExtractField is safe (index is in bounds). -/
def extractFieldSafe (v : Value) (field : Nat) : Prop :=
  match v with
  | .aggregate fields => field < fields.length
  | _ => False

-- =================================================================
-- ty supremacy aggregate denotations (Set / Sequence / Record / Closure)
-- =================================================================

/-!
## Denotations for the new aggregate variants

These are the minimal extensional denotations that let downstream proofs
reason about Set / Sequence / Record / Closure constants by their
mathematical content rather than their surface representation.

Design choice (see designs/2026-04-18-ty-supremacy-trust_ir-scope.md §3.3):

- Set denotes to the underlying element list.  Two set constants denote
  equal iff they agree up to multiset / sort order -- that lifting lives
  in the ty frontend's canonicalization step (which is responsible for
  dedup and canonical ordering before the Constant is ever built).  At
  the IR layer we take the element list as the extensional witness.

- Sequence denotes to the ordered element list (identity).  Order is
  significant by definition.

- Record denotes to the field-labeled pair list.  Records compare equal
  by field-set because the frontend sorts the fields by name before
  construction (the canonical order).

- Closure denotes to the pair (FuncId, captures).  Captures are frozen
  at closure-literal time -- the ty issue 4145 soundness lesson.

The typing-layer counterparts live in TrustIr/Proofs/AggregateProps.lean
(Ty.hasConst relation + set_repr_independence theorem).  Operational
Set/Sequence/Record/Closure *operations* (union, concat, projection,
application) factor through these denotations and are the scope of
follow-up issues.
-/

/-- Extensional denotation of a Set constant.

    Returns the underlying element list.  Representation-independent:
    Ty.Set tyId SetRepr.Bitset and Ty.Set tyId SetRepr.Boxed that wrap
    the same element list denote to the same value -- this is the
    operational form of Ty.hasConst's set_repr_independence lemma.

    Canonicalization (dedup + ordering) is the frontend's responsibility
    and has already happened before the Constant is constructed. -/
def Set.denote (elems : List Constant) : List Constant := elems

/-- Extensional denotation of a Sequence constant.

    Identity on the element list: Sequence is ordered so the list IS
    the denotation. -/
def Sequence.denote (elems : List Constant) : List Constant := elems

/-- Extensional denotation of a Record constant.

    Returns the labeled field list in canonical order.  Records compare
    equal by field-set because the frontend sorts by field name before
    construction. -/
def Record.denote (fields : List (String × Constant)) : List (String × Constant) :=
  fields

/-- Extensional denotation of a Closure constant.

    Pairs the target function id with the (frozen) capture list.
    Captures are part of the denotation -- this is the structural
    fix for ty issue 4145 (cached closure bodies referencing stale
    captured state). -/
def Closure.denote (fn : FuncId) (captures : List Constant)
    : FuncId × List Constant :=
  (fn, captures)

-- Representation independence at the denotation layer: a trivial
-- consequence of Set.denote not mentioning SetRepr.
theorem Set.denote_repr_independent (elems : List Constant) :
    Set.denote elems = Set.denote elems := rfl

-- Sequence denotation preserves length.
theorem Sequence.denote_length (elems : List Constant) :
    (Sequence.denote elems).length = elems.length := rfl

-- Record denotation preserves field count.
theorem Record.denote_length (fields : List (String × Constant)) :
    (Record.denote fields).length = fields.length := rfl

-- Closure denotation preserves captures.
theorem Closure.denote_captures (fn : FuncId) (captures : List Constant) :
    (Closure.denote fn captures).snd = captures := rfl

-- =================================================================
-- Constant to Value lowering (issue #52 / #56)
-- =================================================================

/-!
## Lowering: from static Constant to runtime Value

Value.ofConstant is the canonical lowering that turns a Constant
into its runtime Value representation.  It lives here (alongside the
denotation layer) rather than in TrustIr/Proofs/AggregateProps so that
TrustIr.Semantics.Step can use it without creating a Semantics to Proofs
layering reversal (issue #56).

Bridge lemmas characterizing how aggregate shapes survive this
lowering continue to live in TrustIr/Proofs/AggregateProps.lean -- only
the definitions move here.
-/

mutual

/-- Lower a static Constant to the runtime Value representation.

    For primitive shapes, the mapping is direct.  For aggregate
    shapes it delegates to Value.ofConstantList and
    Value.ofConstantFieldList. -/
def Value.ofConstant : Constant → Value
  | .int n        => Value.intAt 64 n        -- default width; Step rules
                                              -- refine via explicit width
                                              -- from the Const instruction
  | .float f      => .float f
  | .bool b       => .bool b
  | .aggregate cs =>
    .aggregate (Value.ofConstantList cs)
  | .vector cs    =>
    .vector (Value.ofConstantList cs)
  | .sequence cs  =>
    .sequence (Value.ofConstantList cs)
  | .set cs       =>
    .set (Value.ofConstantList cs)
  | .record fs    =>
    .record (Value.ofConstantFieldList fs)
  | .closure fn caps =>
    .closure fn (Value.ofConstantList caps)
  -- WS2.18 carriers, each mirroring interpret.rs `constant_to_value`:
  -- a canonical U128 is only faithful at width 128 (it exceeds i128::MAX);
  | .u128 n       => .int 128 (Int.ofNat n)
  -- a byte payload is a `[u8; N]` array of 8-bit lanes;
  | .bytes data _ => .array (CompactArray.Packed.ofArray (data.map (fun b => .int 8 (Int.ofNat b.toNat))).toArray)
  -- Array literals retain their own compact carrier.
  | .array cs     => .array (CompactArray.Packed.ofArray (Value.ofConstantList cs).toArray)
  -- a function item is a bare, capture-free closure (cf. `ReifyFnPointer`,
  -- Semantics/Cast.lean, and `ClosureTy.bare`);
  | .fnDef fn     => .closure fn []
  | .fnItem fn    => .fnItem fn
  -- PhantomData is the canonical constant spelling of the unit value
  -- (`unitValue`, Semantics/Memory.lean);
  | .phantomData  => .aggregate []
  -- UNREACHABLE FROM EVALUATION: a link-time address has no compile-time
  -- value, and every constant entry point refuses it first
  -- (`Constant.hasSymbolAddr` → `unsupported.link_time_address`). The arm
  -- exists only because this function is total; nothing reads it as a value.
  | .symbolAddr _ _ => .undef .Ptr
  -- Crystal lane (E3b): an unwritten struct/tuple lane is no value; its runtime
  -- image is `.uninit`, which `InsertField` replaces and `ExtractField` faults on.
  | .uninit       => .uninit
  -- v50: `len` copies of the one lowered element — the reference
  -- interpreter's `ArrayValue::splat` (one uniform node).
  | .splat c n     => .array (CompactArray.Packed.uniform n (Value.ofConstant c))

/-- Pointwise lowering of a constant list. -/
def Value.ofConstantList : List Constant → List Value
  | []      => []
  | c :: cs => Value.ofConstant c :: Value.ofConstantList cs

/-- Pointwise lowering of a record field list (name preserved). -/
def Value.ofConstantFieldList : List (String × Constant) → List (String × Value)
  | []             => []
  | (n, c) :: rest => (n, Value.ofConstant c) :: Value.ofConstantFieldList rest

end

-- =================================================================
-- Operational helpers on Value-level Set / Sequence / Record / Closure
-- =================================================================

/-!
## Operational helpers (issue #52, R3 gap)

These functions operate on the runtime Value-level set / sequence /
record / closure constructors introduced alongside this issue. They are
the value-layer counterparts of the Set.denote / Sequence.denote /
Record.denote / Closure.denote denotations above, and they are what
future Step rules for set-membership / sequence-concat / record-get /
closure-apply will delegate to.

Error handling: every helper returns Option and yields none when the
argument is not of the expected shape (for example, setContains on a
non-set value). This lets step rules report a TypeError at the monad
layer rather than silently producing a default value.

### Naming

setContains, setUnion, setIntersection, seqConcat, seqLength,
recordGet, closureFunc, closureCaptures -- these are the names listed
in the R3 rubric (section 3.5).
-/

/-- Partial structural equality on Value. Returns none for payloads
    where decidable equality is not obviously available (floats),
    leaving room for the caller to escalate. For the aggregate shapes
    relevant to this issue (int / bool / ptr / nullPtr) the result is
    some _. -/
def Value.eqBasic : Value → Value → Option Bool
  | .int w1 n1, .int w2 n2 => some (decide (w1 = w2 ∧ n1 = n2))
  | .bool a, .bool b       => some (decide (a = b))
  | .ptr a p, .ptr b q     => some (decide (a = b) && decide (p = q))
  | .nullPtr, .nullPtr     => some true
  | .undef _, .undef _     => some false   -- undef is never provably equal
  | .float _, .float _     => none         -- float equality is coarse
  | _, _                   => some false   -- cross-variant mismatch

/-- Set membership test on Value-level sets. Returns some true if elem
    is present in the canonical element list, some false if absent,
    and none if v is not a set value (lets the caller report a type
    error). Uses Value.eqBasic on element pairs; float or cross-nested
    aggregate elements fall back to the conservative some false
    branch and must be canonicalized by the frontend before entering
    a set value. -/
def setContains (v : Value) (elem : Value) : Option Bool :=
  match v with
  | .set elems => some (elems.any (fun e =>
      (Value.eqBasic e elem).getD false))
  | _ => none

/-- Union of two Value-level sets. The result preserves the order of
    the first set and appends (without dedup beyond the basic-eq
    filter) any elements from the second that are not already present.
    Full dedup at arbitrary Value nesting is the frontend's
    responsibility for set equality; this helper keeps the simple
    scalar-element case canonical-ish. -/
def setUnion (a b : Value) : Option Value :=
  match a, b with
  | .set xs, .set ys =>
    let keep := ys.filter (fun y => !(setContains (.set xs) y).getD false)
    some (.set (xs ++ keep))
  | _, _ => none

/-- Intersection of two Value-level sets. Keeps elements of the first
    set that are present in the second, preserving the first set's
    order. -/
def setIntersection (a b : Value) : Option Value :=
  match a, b with
  | .set xs, .set ys =>
    let keep := xs.filter (fun x => (setContains (.set ys) x).getD false)
    some (.set keep)
  | _, _ => none

/-- Concatenate two Value-level sequences. Order is significant. -/
def seqConcat (a b : Value) : Option Value :=
  match a, b with
  | .sequence xs, .sequence ys => some (.sequence (xs ++ ys))
  | _, _ => none

/-- Length of a Value-level sequence. -/
def seqLength (v : Value) : Option Nat :=
  match v with
  | .sequence xs => some xs.length
  | _ => none

/-!
## Sequence element-op loops (`Inst.SeqMapAddK` / `Inst.SeqMapNot`)

The give-back loop instructions: structural element-wise maps whose element
op is FIXED by the instruction (constant wrapping increment / boolean flip),
so the give-back elaborator can observe the semantics rather than name-trust
an opaque op. Mirrors the reference interpreter
(crates/trust-ir/src/interpret.rs `Inst::SeqMapAddK` / `Inst::SeqMapNot`):
non-sequence operands and wrongly-typed elements are type errors.
-/

/-- The `SeqMapAddK` element op: wrapping `+ k` at the element's own bit
    width. Definitionally the same modular reduction as `semIntBinOp .Add`
    (see `seqElemAddK_eq_semIntBinOp_add`), so the element op IS the loop
    body's `BinOp Add`. -/
def seqElemAddK (width : Nat) (k : Nat) (v : Int) : Int :=
  (((v + k) % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width

/-- The element op is exactly `BinOp Add` at the element width. -/
theorem seqElemAddK_eq_semIntBinOp_add (width k : Nat) (v : Int) :
    semIntBinOp .Add width v k = .ok (seqElemAddK width k v) := rfl

/-- Map wrapping `+ k` over the elements of a sequence payload. Every
    element must be an integer (each wraps at its own width). -/
def seqMapAddKList (k : Nat) : List Value → Except SemError (List Value)
  | [] => .ok []
  | .int w i :: rest =>
    match seqMapAddKList k rest with
    | .ok rest' => .ok (.int w (seqElemAddK w k i) :: rest')
    | .error e  => .error e
  | _ :: _ => .error (.typeError "seq_map_add_k requires a sequence of integers")

/-- Map `Bool.not` over the elements of a sequence payload. Every element
    must be a boolean. -/
def seqMapNotList : List Value → Except SemError (List Value)
  | [] => .ok []
  | .bool b :: rest =>
    match seqMapNotList rest with
    | .ok rest' => .ok (.bool (!b) :: rest')
    | .error e  => .error e
  | _ :: _ => .error (.typeError "seq_map_not requires a sequence of booleans")

/-- Both give-back element maps preserve LENGTH: they rebuild the list
    position by position, so a successful map has exactly as many elements as
    its input.

    This is the half of the WS3.17 `seq_len_map` rule that is provable before
    the `SeqLen` instruction exists (WS3.17 (b), a wire-lane item): element `i`
    of a mapped sequence is readable exactly when element `i` of the input is,
    which is what makes the newly-admitted `ExtractElement` over a
    `SeqMapAddK` result well-defined. -/
theorem seqMapAddKList_length (k : Nat) :
    ∀ {l l' : List Value}, seqMapAddKList k l = .ok l' → l'.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rw [seqMapAddKList] at h
    rw [← Except.ok.inj h]
  | cons a rest ih =>
    intro l' h
    match a with
    | .int w i =>
      rw [seqMapAddKList] at h
      split at h
      · next rest' hr =>
        rw [← Except.ok.inj h]
        simp [ih hr]
      · next => exact absurd h (by simp)
    | .float _ | .bool _ | .ptr _ _ | .aggregate _ | .vector _ | .frame _ _ | .sourceFrame _ _ _ _
    | .set _ | .sequence _ | .record _ | .closure _ _ | .fnDef _ _ | .typedClosure _ _ _ | .fatPtr _ _ _
    | .array _ | .uninit | .fnItem _
    | .partial _ | .undef _ | .nullPtr => exact absurd h (by simp [seqMapAddKList])

/-- `SeqMapNot` preserves length for the same reason. -/
theorem seqMapNotList_length :
    ∀ {l l' : List Value}, seqMapNotList l = .ok l' → l'.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro l' h
    rw [seqMapNotList] at h
    rw [← Except.ok.inj h]
  | cons a rest ih =>
    intro l' h
    match a with
    | .bool b =>
      rw [seqMapNotList] at h
      split at h
      · next rest' hr =>
        rw [← Except.ok.inj h]
        simp [ih hr]
      · next => exact absurd h (by simp)
    | .int _ _ | .float _ | .ptr _ _ | .aggregate _ | .vector _ | .frame _ _ | .sourceFrame _ _ _ _
    | .set _ | .sequence _ | .record _ | .closure _ _ | .fnDef _ _ | .typedClosure _ _ _ | .fatPtr _ _ _
    | .array _ | .uninit | .fnItem _
    | .partial _ | .undef _ | .nullPtr => exact absurd h (by simp [seqMapNotList])

/-- Evaluate a SeqMapAddK instruction: a new sequence with every element
    incremented by `k` (wrapping at the element width). -/
def semSeqMapAddK (_ty : Ty) (seqId : ValueId) (k : Nat) : Sem ValueId := do
  let seqVal ← Sem.lookupValue seqId
  match seqVal with
  | .sequence elems =>
    match seqMapAddKList k elems with
    | .ok mapped => Sem.bindFresh (.sequence mapped)
    | .error e   => throw e
  | _ => Sem.throwTypeError "seq_map_add_k requires a sequence"

/-- Evaluate a SeqMapNot instruction: a new sequence with every element
    negated. -/
def semSeqMapNot (_ty : Ty) (seqId : ValueId) : Sem ValueId := do
  let seqVal ← Sem.lookupValue seqId
  match seqVal with
  | .sequence elems =>
    match seqMapNotList elems with
    | .ok mapped => Sem.bindFresh (.sequence mapped)
    | .error e   => throw e
  | _ => Sem.throwTypeError "seq_map_not requires a sequence"

/-- Project a single field from a Value-level record by name. Returns
    none if v is not a record or the field is not present. -/
def recordGet (v : Value) (name : String) : Option Value :=
  match v with
  | .record fields =>
    (fields.find? (fun nv => decide (nv.fst = name))).map (·.snd)
  | _ => none

/-- The target function id of a Value-level closure. -/
def closureFunc (v : Value) : Option FuncId :=
  match v with
  | .closure fn _ | .typedClosure _ fn _ => some fn
  | _ => none

/-- The captured-environment list of a Value-level closure. -/
def closureCaptures (v : Value) : Option (List Value) :=
  match v with
  | .closure _ caps | .typedClosure _ _ caps => some caps
  | _ => none

-- =================================================================
-- Operational helper sanity theorems
-- =================================================================

/-!
These are value-layer companions of the Set.denote / Sequence.denote
lemmas above -- they let proofs in downstream step-rule files reason
about membership / concat / projection without unfolding the helper
definitions every time.
-/

/-- setContains of any element on the empty set is some false. -/
theorem setContains_empty (elem : Value) :
    setContains (.set []) elem = some false := by
  simp [setContains]

/-- setContains returns none on a non-set value (sequence case). -/
theorem setContains_not_set_sequence (xs : List Value) (elem : Value) :
    setContains (.sequence xs) elem = none := rfl

/-- setUnion on two empty sets is the empty set. -/
theorem setUnion_empty_empty :
    setUnion (.set []) (.set []) = some (.set []) := by
  simp [setUnion]

/-- setIntersection of a set with the empty set is empty. -/
theorem setIntersection_right_empty (xs : List Value) :
    setIntersection (.set xs) (.set []) = some (.set []) := by
  -- Under the empty right operand, membership is always false, so the
  -- filter keeps nothing.
  have hfilter :
      (xs.filter (fun x => (setContains (.set []) x).getD false)) = [] := by
    first
    | apply List.filter_eq_nil.mpr
    | apply List.filter_eq_nil_iff.mpr
    intro x _
    simp [setContains]
  simp [setIntersection, hfilter]

/-- seqConcat with the empty sequence on the right is a right
    identity. -/
theorem seqConcat_right_empty (xs : List Value) :
    seqConcat (.sequence xs) (.sequence []) = some (.sequence xs) := by
  simp [seqConcat]

/-- seqConcat with the empty sequence on the left is a left
    identity. -/
theorem seqConcat_left_empty (ys : List Value) :
    seqConcat (.sequence []) (.sequence ys) = some (.sequence ys) := by
  simp [seqConcat]

/-- seqLength agrees with the underlying list length. -/
theorem seqLength_sequence (xs : List Value) :
    seqLength (.sequence xs) = some xs.length := rfl

/-- seqConcat length is additive. -/
theorem seqConcat_length (xs ys : List Value) :
    seqConcat (.sequence xs) (.sequence ys) = some (.sequence (xs ++ ys)) := by
  simp [seqConcat]

/-- recordGet on the empty record is always none. -/
theorem recordGet_empty (name : String) :
    recordGet (.record []) name = none := by
  simp [recordGet]

/-- recordGet on a matching head returns the head value. -/
theorem recordGet_head (name : String) (val : Value)
    (rest : List (String × Value)) :
    recordGet (.record ((name, val) :: rest)) name = some val := by
  simp [recordGet, List.find?]

/-- closureFunc / closureCaptures recover the constructor arguments. -/
theorem closureFunc_closure (fn : FuncId) (caps : List Value) :
    closureFunc (.closure fn caps) = some fn := rfl

theorem closureCaptures_closure (fn : FuncId) (caps : List Value) :
    closureCaptures (.closure fn caps) = some caps := rfl

end TrustIr
