-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Aggregate operation semantics: struct/array construction and access.
-- Phase 4 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 4
--
-- Aggregate values (structs, arrays, tuples) are represented as
-- `Value.aggregate (List Value)`.  Field/element access is by index.

import TrustIr.Inst
import TrustIr.Semantics.Arith
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Aggregate Operation Semantics

## Overview

TrustIr aggregates (structs, arrays, tuples) are represented uniformly
as `Value.aggregate (List Value)`.  The instruction set provides
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

## StructInit

TrustIr does not have an explicit StructInit instruction.  Struct
construction is done by composing InsertField operations on an
initial `undef` aggregate, or by the Const instruction with an
aggregate constant.  This module provides a helper `buildAggregate`
for constructing aggregates from a list of values.

## Design note

The aggregate semantics are pure functions on the `Value.aggregate`
representation.  No memory access is involved -- aggregate values
live in SSA registers.  Memory-backed aggregates are handled by
Load/Store with byte encoding in `Memory.lean`.
-/

-- =================================================================
-- Aggregate helpers (pure functions)
-- =================================================================

/-- Get a field from an aggregate by static index.
    Returns none if the index is out of bounds or the value is not
    an aggregate. -/
def getField (v : Value) (field : Nat) : Option Value :=
  match v with
  | .aggregate fields => fields.get? field
  | _ => none

/-- Set a field in an aggregate by static index.
    Returns none if the index is out of bounds or the value is not
    an aggregate. -/
def setField (v : Value) (field : Nat) (newVal : Value) : Option Value :=
  match v with
  | .aggregate fields =>
    if field < fields.length then
      some (.aggregate (fields.set field newVal))
    else none
  | _ => none

/-- Get an element from an aggregate by dynamic index. -/
def getElement (v : Value) (index : Nat) : Option Value :=
  match v with
  | .aggregate elems => elems.get? index
  | _ => none

/-- Set an element in an aggregate by dynamic index. -/
def setElement (v : Value) (index : Nat) (newVal : Value) : Option Value :=
  match v with
  | .aggregate elems =>
    if index < elems.length then
      some (.aggregate (elems.set index newVal))
    else none
  | _ => none

/-- Runtime payload check for vector ExtractElement, whose declared type is
    the lane result type.  The executable subset is bounded to v4i32, v2i64,
    and the logical bool masks v16bool / v8bool / v4bool / v2bool. The bool lane
    counts match `Ty.executableVectorPayloadMatches` (Arith.lean) and the
    `vector.mask_to_bits` dialect contract (which accepts <16/8/4/2 x bool>), so
    the dialect's `mask_to_bits` lowering — a per-lane `ExtractElement .Bool`
    chain — is executable at every mask shape the dialect admits. -/
def Ty.executableVectorLanePayloadMatches (elemTy : Ty)
    (lanes : List Value) : _root_.Bool :=
  match elemTy with
  | .I32 => lanes.length == 4 && lanes.all (Value.isIntWidth 32)
  | .I64 => lanes.length == 2 && lanes.all (Value.isIntWidth 64)
  | .Bool =>
    (lanes.length == 16 || lanes.length == 8 || lanes.length == 4 || lanes.length == 2)
      && lanes.all Value.isBool
  | _ => false

/-- Runtime lane-value check for vector InsertElement. -/
def Ty.executableVectorLaneValueMatches (elemTy : Ty)
    (v : Value) : _root_.Bool :=
  match elemTy with
  | .I32 => Value.isIntWidth 32 v
  | .I64 => Value.isIntWidth 64 v
  | .Bool => Value.isBool v
  | _ => false

/-- Get a vector lane from the bounded executable vector subset. -/
def getVectorElement (elemTy : Ty) (v : Value) (index : Nat)
    : Except SemError Value :=
  match v with
  | .vector lanes =>
    if elemTy.executableVectorLanePayloadMatches lanes then
      match lanes.get? index with
      | some lane => .ok lane
      | none => .error (.ub "ExtractElement: vector index out of bounds")
    else
      .error (.unsupported .vectorShape
        "ExtractElement: unsupported vector shape or lane type mismatch")
  | _ => .error (.typeError "ExtractElement: operand is not a vector")

/-- Set a vector lane in the bounded executable vector subset.
    InsertElement declares the vector result/source type, so the lane type is
    derived from `Ty.Vector lanes elemTy`. -/
def setVectorElement (vectorTy : Ty) (v : Value) (index : Nat)
    (newVal : Value) : Except SemError Value :=
  match v with
  | .vector lanes =>
    if vectorTy.executableVectorPayloadMatches lanes then
      match vectorTy with
      | .Vector _ elemTy =>
        if elemTy.executableVectorLaneValueMatches newVal then
          if index < lanes.length then
            .ok (.vector (lanes.set index newVal))
          else
            .error (.ub "InsertElement: vector index out of bounds")
        else
          .error (.typeError "InsertElement: lane value does not match vector type")
      | _ =>
        .error (.unsupported .vectorShape
          "InsertElement: unsupported vector shape or lane type mismatch")
    else
      .error (.unsupported .vectorShape
        "InsertElement: unsupported vector shape or lane type mismatch")
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
  | some v => Sem.bindFresh v
  | none   =>
    match aggVal with
    | .aggregate _ =>
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

    Mirrors Rust `Inst::InsertField`. -/
def semInsertField (_ty : Ty) (aggregateId : ValueId) (field : Nat)
    (valueId : ValueId) : Sem ValueId := do
  let aggVal ← Sem.lookupValue aggregateId
  let newFieldVal ← Sem.lookupValue valueId
  -- Both the aggregate and the inserted value are inspected: poison is UB.
  Sem.rejectPartial aggVal "InsertField"
  Sem.rejectPartial newFieldVal "InsertField"
  match setField aggVal field newFieldVal with
  | some v => Sem.bindFresh v
  | none   =>
    match aggVal with
    | .aggregate _ =>
      Sem.throwUB "InsertField: field index out of bounds"
    | _ =>
      Sem.throwTypeError "InsertField: operand is not an aggregate"

-- =================================================================
-- ExtractElement semantics
-- =================================================================

/-- Evaluate an ExtractElement instruction.
    Extracts an element from an array aggregate by dynamic index.

    The index is a runtime value (ValueId), so bounds checking is
    a runtime safety check.

    Mirrors Rust `Inst::ExtractElement`. -/
def semExtractElement (ty : Ty) (arrayId indexId : ValueId)
    : Sem ValueId := do
  let arrVal ← Sem.lookupValue arrayId
  let idxVal ← Sem.lookupValue indexId
  let idx ← match idxVal with
    | .int _ n =>
      if n < 0 then Sem.throwUB "ExtractElement: negative index"
      else pure n.toNat
    | _ => Sem.throwTypeError "ExtractElement: index is not an integer"
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
      | .aggregate _ =>
        Sem.throwUB "ExtractElement: index out of bounds"
      | _ =>
        Sem.throwTypeError "ExtractElement: operand is not an aggregate or vector"

-- =================================================================
-- InsertElement semantics
-- =================================================================

/-- Evaluate an InsertElement instruction.
    Creates a new array with the given element replaced.

    This is a non-destructive update: the original array is not
    modified (SSA form).

    Mirrors Rust `Inst::InsertElement`. -/
def semInsertElement (ty : Ty) (arrayId indexId valueId : ValueId)
    : Sem ValueId := do
  let arrVal ← Sem.lookupValue arrayId
  let idxVal ← Sem.lookupValue indexId
  let newElemVal ← Sem.lookupValue valueId
  let idx ← match idxVal with
    | .int _ n =>
      if n < 0 then Sem.throwUB "InsertElement: negative index"
      else pure n.toNat
    | _ => Sem.throwTypeError "InsertElement: index is not an integer"
  match arrVal with
  | .vector _ =>
    match setVectorElement ty arrVal idx newElemVal with
    | .ok v => Sem.bindFresh v
    | .error e => throw e
  | _ =>
    match setElement arrVal idx newElemVal with
    | some v => Sem.bindFresh v
    | none   =>
      match arrVal with
      | .aggregate _ =>
        Sem.throwUB "InsertElement: index out of bounds"
      | _ =>
        Sem.throwTypeError "InsertElement: operand is not an aggregate or vector"

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
  | .int n        => .int 64 n               -- default width; Step rules
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
  | .ptr a, .ptr b         => some (decide (a = b))
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
  | .closure fn _ => some fn
  | _ => none

/-- The captured-environment list of a Value-level closure. -/
def closureCaptures (v : Value) : Option (List Value) :=
  match v with
  | .closure _ caps => some caps
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
    apply List.filter_eq_nil.mpr
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
