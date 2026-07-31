-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Declared semantics for the portable vector dialect.
-- Mirrors: crates/trust_ir/src/dialect/vector.rs

import TrustIr.Semantics.Dialect
import TrustIr.Semantics.Aggregate

namespace TrustIr
namespace VectorDialect

/-!
# Portable Vector Dialect Semantics

Core `stepInst (.DialectOp ...)` remains unsupported.  This module supplies
declared denotations packaged as `DialectOpSem` values for dialect-aware
lowering proofs and executable fixtures.

The first slice intentionally mirrors the Rust v1 vector dialect contract used
by TrustCg x86 SIMD:

* `vector.pack_lanes`, `vector.extract_lane`, `vector.insert_lane`,
  `vector.reduce`, and `vector.shuffle` support `<4 x i32>` and `<2 x i64>`
  lane vectors (the executable subset; the Rust decoder additionally admits
  `<16 x i8>` and `<8 x i16>`, covered Rust-side by interpreter cross-checks).
* `vector.mask_to_bits` supports logical `<16 x bool>`, `<8 x bool>`,
  `<4 x bool>`, and `<2 x bool>` masks, with lane 0 mapped to bit 0.
* `vector.fma` is deliberately NOT modelled: the ratified policy
  (docs/roadmap/fast-4-vector-crosslane-ops.md) gives it no trust-ir lowering
  (an unfused `FMul`+`FAdd` expansion double-rounds), so there is no
  refinement obligation to state at this layer.
* Other dialect payloads fail closed before producing a denotation.
-/

def dialectName : String := "vector"
def packLanesOp : String := "pack_lanes"
def extractLaneOp : String := "extract_lane"
def insertLaneOp : String := "insert_lane"
def maskToBitsOp : String := "mask_to_bits"
def reduceOp : String := "reduce"
def shuffleOp : String := "shuffle"
def bitOrderAttr : String := "bit_order"
def lsbLane0 : String := "lsb_lane0"
def reduceKindAttr : String := "kind"
def shuffleIndicesAttr : String := "indices"
def reduceAddKind : String := "add"
def reduceOrKind : String := "or"

/-- Associative, bounded horizontal reduction kinds supported by
    `vector.reduce`. Mirrors Rust `ReduceKind`: both fold with a well-defined
    identity element `0`. -/
inductive ReduceKind where
  | add
  | or
  deriving Repr, DecidableEq

/-- The core integer `BinOp` that folds one lane for each reduction kind.
    This is the exact op the Rust `VectorLoweringPass::lower_reduce` emits. -/
def reduceKindOp : ReduceKind → BinOp
  | .add => .Add
  | .or  => .Or

structure PackLanesSpec where
  vectorTy : Ty
  elemTy   : Ty
  lanes    : Nat
  deriving Repr

structure ExtractLaneSpec where
  vectorTy : Ty
  elemTy   : Ty
  lanes    : Nat
  lane     : Nat
  deriving Repr

structure InsertLaneSpec where
  vectorTy : Ty
  elemTy   : Ty
  lanes    : Nat
  lane     : Nat
  deriving Repr

structure MaskToBitsSpec where
  maskTy   : Ty
  lanes    : Nat
  resultTy : Ty
  deriving Repr

/-- Decoded `vector.reduce`: a horizontal fold of an integer lane vector to a
    single scalar of the element type. Mirrors Rust `ReduceSpec`. -/
structure ReduceSpec where
  vectorTy : Ty
  elemTy   : Ty
  lanes    : Nat
  kind     : ReduceKind
  deriving Repr

/-- Decoded `vector.shuffle`: a static lane permutation. `indices[j]` is the
    source lane copied into result lane `j`. Mirrors Rust `ShuffleSpec`. -/
structure ShuffleSpec where
  vectorTy : Ty
  elemTy   : Ty
  lanes    : Nat
  indices  : List Nat
  deriving Repr

inductive VectorSpec where
  | packLanes  : PackLanesSpec → VectorSpec
  | extractLane : ExtractLaneSpec → VectorSpec
  | insertLane : InsertLaneSpec → VectorSpec
  | maskToBits : MaskToBitsSpec → VectorSpec
  | reduce : ReduceSpec → VectorSpec
  | shuffle : ShuffleSpec → VectorSpec
  deriving Repr

def unsupported {α : Type} (msg : String) : Except SemError α :=
  .error (.unsupported .dialectOp msg)

def vectorShapeUnsupported {α : Type} (msg : String) : Except SemError α :=
  .error (.unsupported .vectorShape msg)

def typeError {α : Type} (msg : String) : Except SemError α :=
  .error (.typeError msg)

def ub {α : Type} (msg : String) : Except SemError α :=
  .error (.ub msg)

def attr? (inst : DialectInst) (name : String) : Option AttrValue :=
  match inst.attrs.find? (fun attr => attr.name == name) with
  | some attr => some attr.value
  | none => none

def attrTy (inst : DialectInst) (name : String) : Except SemError Ty :=
  match attr? inst name with
  | some (.ty ty) => .ok ty
  | some _ => typeError s!"{inst.qualifiedName} requires Ty attribute {name}"
  | none => typeError s!"{inst.qualifiedName} requires Ty attribute {name}"

def attrLane (inst : DialectInst) (lanes : Nat) : Except SemError Nat :=
  match attr? inst "lane" with
  | some (.u64 lane) =>
    if lane < lanes then
      .ok lane
    else
      ub s!"{inst.qualifiedName} lane {lane} is out of range for {lanes} lane vector"
  | some _ => typeError s!"{inst.qualifiedName} requires U64 attribute lane"
  | none => typeError s!"{inst.qualifiedName} requires U64 attribute lane"

def checkHeader (inst : DialectInst) (expectedOp : String) : Except SemError Unit := do
  if inst.dialect != dialectName then
    unsupported s!"expected vector dialect op, got {inst.dialect}"
  else if inst.op != expectedOp then
    unsupported s!"expected vector.{expectedOp}, got {inst.qualifiedName}"
  else if inst.version != 1 then
    unsupported s!"{inst.qualifiedName} version {inst.version} is unsupported; expected version 1"
  else
    .ok ()

def requireOperandCount (inst : DialectInst) (expected : Nat) : Except SemError Unit :=
  if inst.operands.length == expected then
    .ok ()
  else
    typeError s!"{inst.qualifiedName} expects {expected} operand(s), got {inst.operands.length}"

def requireResultCount (inst : DialectInst) (expected : Nat) : Except SemError Unit :=
  if inst.resultTys.length == expected then
    .ok ()
  else
    typeError s!"{inst.qualifiedName} expects {expected} result type(s), got {inst.resultTys.length}"

def supportedLaneVectorShape : Ty → Option (Ty × Nat)
  | .Vector 4 .I32 => some (.I32, 4)
  | .Vector 2 .I64 => some (.I64, 2)
  | _ => none

def supportedLaneVectorTy (inst : DialectInst) (ty : Ty) :
    Except SemError (Ty × Nat) :=
  match supportedLaneVectorShape ty with
  | some spec => .ok spec
  | none =>
    vectorShapeUnsupported
      s!"{inst.qualifiedName} supports only <4 x i32> and <2 x i64> lane vectors"

def supportedBoolMaskTy (inst : DialectInst) (ty : Ty) :
    Except SemError Nat :=
  match ty with
  | .Vector 16 .Bool => .ok 16
  | .Vector 8 .Bool => .ok 8
  | .Vector 4 .Bool => .ok 4
  | .Vector 2 .Bool => .ok 2
  | _ =>
    vectorShapeUnsupported
      s!"{inst.qualifiedName} supports only logical <16 x bool>, <8 x bool>, <4 x bool>, and <2 x bool> masks"

def validateMaskResultTy (inst : DialectInst) (lanes : Nat) (resultTy : Ty) :
    Except SemError Unit :=
  match lanes, resultTy with
  | 16, .I32 => .ok ()
  | 8, .I32 => .ok ()
  | 4, .I32 => .ok ()
  | 2, .I32 => .ok ()
  | 2, .I64 => .ok ()
  | 16, _ => typeError s!"{inst.qualifiedName} <16 x bool> mask_to_bits result must be i32"
  | 8, _ => typeError s!"{inst.qualifiedName} <8 x bool> mask_to_bits result must be i32"
  | 4, _ => typeError s!"{inst.qualifiedName} <4 x bool> mask_to_bits result must be i32"
  | 2, _ => typeError s!"{inst.qualifiedName} <2 x bool> mask_to_bits result must be i32 or i64"
  | _, _ => vectorShapeUnsupported s!"{inst.qualifiedName} unsupported mask lane count"

def validateBitOrder (inst : DialectInst) : Except SemError Unit :=
  match attr? inst bitOrderAttr with
  | none => .ok ()
  | some (.str value) =>
    if value == lsbLane0 then
      .ok ()
    else
      typeError s!"{inst.qualifiedName} unsupported bit_order {value}"
  | some _ => typeError s!"{inst.qualifiedName} requires Str attribute bit_order"

def decodePackLanes (inst : DialectInst) : Except SemError PackLanesSpec := do
  checkHeader inst packLanesOp
  requireResultCount inst 1
  let vectorTy ← match inst.resultTys with
    | [ty] => .ok ty
    | _ => typeError s!"{inst.qualifiedName} expects one result type"
  let (elemTy, lanes) ← supportedLaneVectorTy inst vectorTy
  if inst.operands.length == lanes then
    .ok { vectorTy := vectorTy, elemTy := elemTy, lanes := lanes }
  else
    typeError s!"{inst.qualifiedName} expects {lanes} lane operand(s)"

def decodeExtractLane (inst : DialectInst) : Except SemError ExtractLaneSpec := do
  checkHeader inst extractLaneOp
  requireOperandCount inst 1
  requireResultCount inst 1
  let vectorTy ← attrTy inst "vector_ty"
  let (elemTy, lanes) ← supportedLaneVectorTy inst vectorTy
  let lane ← attrLane inst lanes
  match inst.resultTys with
  | [resultTy] =>
    if resultTy == elemTy then
      .ok { vectorTy := vectorTy, elemTy := elemTy, lanes := lanes, lane := lane }
    else
      typeError s!"{inst.qualifiedName} result type does not match vector element type"
  | _ => typeError s!"{inst.qualifiedName} expects one result type"

def decodeInsertLane (inst : DialectInst) : Except SemError InsertLaneSpec := do
  checkHeader inst insertLaneOp
  requireOperandCount inst 2
  requireResultCount inst 1
  let vectorTy ← match inst.resultTys with
    | [ty] => .ok ty
    | _ => typeError s!"{inst.qualifiedName} expects one result type"
  let (elemTy, lanes) ← supportedLaneVectorTy inst vectorTy
  let lane ← attrLane inst lanes
  .ok { vectorTy := vectorTy, elemTy := elemTy, lanes := lanes, lane := lane }

def decodeMaskToBits (inst : DialectInst) : Except SemError MaskToBitsSpec := do
  checkHeader inst maskToBitsOp
  requireOperandCount inst 1
  requireResultCount inst 1
  let maskTy ← attrTy inst "mask_ty"
  let lanes ← supportedBoolMaskTy inst maskTy
  let resultTy ← match inst.resultTys with
    | [ty] => .ok ty
    | _ => typeError s!"{inst.qualifiedName} expects one result type"
  validateMaskResultTy inst lanes resultTy
  validateBitOrder inst
  .ok { maskTy := maskTy, lanes := lanes, resultTy := resultTy }

def attrReduceKind (inst : DialectInst) : Except SemError ReduceKind :=
  match attr? inst reduceKindAttr with
  | some (.str value) =>
    if value == reduceAddKind then .ok .add
    else if value == reduceOrKind then .ok .or
    else unsupported s!"{inst.qualifiedName} unsupported reduce kind {value}"
  | some _ => typeError s!"{inst.qualifiedName} requires Str attribute kind"
  | none => typeError s!"{inst.qualifiedName} requires Str attribute kind"

def attrShuffleIndices (inst : DialectInst) (lanes : Nat) : Except SemError (List Nat) :=
  match attr? inst shuffleIndicesAttr with
  | some (.bytes raw) =>
    let indices := raw.map (·.toNat)
    if indices.length != lanes then
      typeError s!"{inst.qualifiedName} expects {lanes} shuffle index/indices"
    else if indices.all (fun index => decide (index < lanes)) then
      .ok indices
    else
      ub s!"{inst.qualifiedName} shuffle index out of range for {lanes} lane vector"
  | some _ => typeError s!"{inst.qualifiedName} requires Bytes attribute indices"
  | none => typeError s!"{inst.qualifiedName} requires Bytes attribute indices"

def decodeReduce (inst : DialectInst) : Except SemError ReduceSpec := do
  checkHeader inst reduceOp
  requireOperandCount inst 1
  requireResultCount inst 1
  let vectorTy ← attrTy inst "vector_ty"
  let (elemTy, lanes) ← supportedLaneVectorTy inst vectorTy
  let kind ← attrReduceKind inst
  match inst.resultTys with
  | [resultTy] =>
    if resultTy == elemTy then
      .ok { vectorTy := vectorTy, elemTy := elemTy, lanes := lanes, kind := kind }
    else
      typeError s!"{inst.qualifiedName} result type does not match vector element type"
  | _ => typeError s!"{inst.qualifiedName} expects one result type"

def decodeShuffle (inst : DialectInst) : Except SemError ShuffleSpec := do
  checkHeader inst shuffleOp
  requireOperandCount inst 1
  requireResultCount inst 1
  let vectorTy ← match inst.resultTys with
    | [ty] => .ok ty
    | _ => typeError s!"{inst.qualifiedName} expects one result type"
  let (elemTy, lanes) ← supportedLaneVectorTy inst vectorTy
  let indices ← attrShuffleIndices inst lanes
  .ok { vectorTy := vectorTy, elemTy := elemTy, lanes := lanes, indices := indices }

def decode (inst : DialectInst) : Except SemError VectorSpec :=
  match inst.op with
  | "pack_lanes" => VectorSpec.packLanes <$> decodePackLanes inst
  | "extract_lane" => VectorSpec.extractLane <$> decodeExtractLane inst
  | "insert_lane" => VectorSpec.insertLane <$> decodeInsertLane inst
  | "mask_to_bits" => VectorSpec.maskToBits <$> decodeMaskToBits inst
  | "reduce" => VectorSpec.reduce <$> decodeReduce inst
  | "shuffle" => VectorSpec.shuffle <$> decodeShuffle inst
  | _ => unsupported s!"unknown vector op {inst.op}"

def laneValueMatches (elemTy : Ty) (value : Value) : Bool :=
  elemTy.executableVectorLaneValueMatches value

def lookupOperands : List ValueId → MachineState → Except SemError (List Value)
  | [], _ => .ok []
  | id :: rest, state =>
    match state.lookupValue id with
    | some value => do
      let values ← lookupOperands rest state
      .ok (value :: values)
    | none => typeError s!"undefined SSA value: {repr id}"

def bindFreshValue (state : MachineState) (value : Value) : MachineState :=
  (state.bindValue value).snd

def runPackLanes (inst : DialectInst) (spec : PackLanesSpec)
    (state : MachineState) : Except SemError MachineState := do
  let lanes ← lookupOperands inst.operands state
  if lanes.all (laneValueMatches spec.elemTy) && lanes.length == spec.lanes then
    .ok (bindFreshValue state (.vector lanes))
  else
    typeError s!"{inst.qualifiedName} lane operand type mismatch"

def runExtractLane (inst : DialectInst) (spec : ExtractLaneSpec)
    (state : MachineState) : Except SemError MachineState := do
  let vectorId ← match inst.operands with
    | [id] => .ok id
    | _ => typeError s!"{inst.qualifiedName} expects one vector operand"
  let vectorValue ← match state.lookupValue vectorId with
    | some value => .ok value
    | none => typeError s!"undefined SSA value: {repr vectorId}"
  let lane ← getVectorElement spec.elemTy vectorValue spec.lane
  .ok (bindFreshValue state lane)

def runInsertLane (inst : DialectInst) (spec : InsertLaneSpec)
    (state : MachineState) : Except SemError MachineState := do
  let (vectorId, laneId) ← match inst.operands with
    | [vectorId, laneId] => .ok (vectorId, laneId)
    | _ => typeError s!"{inst.qualifiedName} expects vector and lane operands"
  let vectorValue ← match state.lookupValue vectorId with
    | some value => .ok value
    | none => typeError s!"undefined SSA value: {repr vectorId}"
  let laneValue ← match state.lookupValue laneId with
    | some value => .ok value
    | none => typeError s!"undefined SSA value: {repr laneId}"
  let result ← setVectorElement spec.vectorTy vectorValue spec.lane laneValue
  .ok (bindFreshValue state result)

def maskBitsAux : List Value → Nat → Nat → Except SemError Nat
  | [], _, acc => .ok acc
  | .bool bit :: rest, index, acc =>
    let next := if bit then acc + (2 ^ index) else acc
    maskBitsAux rest (index + 1) next
  | _ :: _, _, _ => typeError "vector.mask_to_bits requires bool mask lanes"

def maskBits (lanes : List Value) : Except SemError Nat :=
  maskBitsAux lanes 0 0

def boolMaskPayloadMatches (spec : MaskToBitsSpec) (lanes : List Value) : _root_.Bool :=
  lanes.length == spec.lanes && lanes.all Value.isBool

def resultWidth (ty : Ty) : Nat :=
  match ty with
  | .I64 => 64
  | _ => 32

def runMaskToBits (inst : DialectInst) (spec : MaskToBitsSpec)
    (state : MachineState) : Except SemError MachineState := do
  let maskId ← match inst.operands with
    | [id] => .ok id
    | _ => typeError s!"{inst.qualifiedName} expects one mask operand"
  let maskValue ← match state.lookupValue maskId with
    | some value => .ok value
    | none => typeError s!"undefined SSA value: {repr maskId}"
  match maskValue with
  | .vector lanes =>
    if boolMaskPayloadMatches spec lanes then
      let bits ← maskBits lanes
      .ok (bindFreshValue state (.int (resultWidth spec.resultTy) bits))
    else
      vectorShapeUnsupported s!"{inst.qualifiedName} mask lanes do not match declared mask_ty"
  | _ => typeError s!"{inst.qualifiedName} operand is not a vector mask"

/-- One fold step of `vector.reduce`: the fixed-width modular reduction of the
    kind's integer operation. Definitionally equal to the core
    `semIntBinOp (reduceKindOp kind)` success payload (see
    `semIntBinOp_reduceStep` in the refinement proofs), so the dialect fold and
    the Rust pass's per-lane `BinOp` chain compute the identical accumulator
    representation step for step. -/
def reduceStep (kind : ReduceKind) (w : Nat) (acc lane : Int) : Int :=
  let modulus := (2 : Int) ^ w
  let wrap (v : Int) : Int := ((v % modulus) + modulus) % modulus
  match kind with
  | .add => wrap (acc + lane)
  | .or  => wrap (Int.lor acc lane)

/-- Identity-seeded left fold over the integer lane payloads. Mirrors the Rust
    reference interpreter's `VectorSpec::Reduce` accumulator loop
    (`crates/trust-ir/src/interpret.rs`): both `add` (wrapping) and `or` are
    associative and commutative with identity `0`. -/
def reduceAux (kind : ReduceKind) (w : Nat) : List Value → Int → Except SemError Int
  | [], acc => .ok acc
  | .int _ lane :: rest, acc => reduceAux kind w rest (reduceStep kind w acc lane)
  | _ :: _, _ => typeError "vector.reduce requires integer lanes"

def runReduce (inst : DialectInst) (spec : ReduceSpec)
    (state : MachineState) : Except SemError MachineState := do
  let vectorId ← match inst.operands with
    | [id] => .ok id
    | _ => typeError s!"{inst.qualifiedName} expects one vector operand"
  let vectorValue ← match state.lookupValue vectorId with
    | some value => .ok value
    | none => typeError s!"undefined SSA value: {repr vectorId}"
  match vectorValue with
  | .vector lanes =>
    if spec.vectorTy.executableVectorPayloadMatches lanes then
      let acc ← reduceAux spec.kind (resultWidth spec.elemTy) lanes 0
      .ok (bindFreshValue state (.int (resultWidth spec.elemTy) acc))
    else
      vectorShapeUnsupported s!"{inst.qualifiedName} vector lanes do not match declared vector_ty"
  | _ => typeError s!"{inst.qualifiedName} operand is not a vector"

/-- Static gather for `vector.shuffle`: result lane `j` is source lane
    `indices[j]`. The decoder range-checks every index, so on decoded specs the
    out-of-range arm is unreachable; it keeps the denotation total on
    hand-built specs (mirroring the Rust interpreter's explicit error). -/
def shuffleGather (lanes : List Value) : List Nat → Except SemError (List Value)
  | [] => .ok []
  | index :: rest =>
    match lanes.get? index with
    | some lane => do
      let others ← shuffleGather lanes rest
      .ok (lane :: others)
    | none => ub "vector.shuffle index out of range for runtime vector value"

def runShuffle (inst : DialectInst) (spec : ShuffleSpec)
    (state : MachineState) : Except SemError MachineState := do
  let vectorId ← match inst.operands with
    | [id] => .ok id
    | _ => typeError s!"{inst.qualifiedName} expects one vector operand"
  let vectorValue ← match state.lookupValue vectorId with
    | some value => .ok value
    | none => typeError s!"undefined SSA value: {repr vectorId}"
  match vectorValue with
  | .vector lanes =>
    if spec.vectorTy.executableVectorPayloadMatches lanes then
      let shuffled ← shuffleGather lanes spec.indices
      .ok (bindFreshValue state (.vector shuffled))
    else
      vectorShapeUnsupported s!"{inst.qualifiedName} vector lanes do not match declared vector_ty"
  | _ => typeError s!"{inst.qualifiedName} operand is not a vector"

def runSpec (inst : DialectInst) : VectorSpec → MachineState → Except SemError MachineState
  | .packLanes spec => runPackLanes inst spec
  | .extractLane spec => runExtractLane inst spec
  | .insertLane spec => runInsertLane inst spec
  | .maskToBits spec => runMaskToBits inst spec
  | .reduce spec => runReduce inst spec
  | .shuffle spec => runShuffle inst spec

/-- Decode a vector dialect payload into a declared denotation. -/
def opSem (inst : DialectInst) : Except SemError DialectOpSem := do
  let spec ← decode inst
  .ok { inst := inst, runOp := runSpec inst spec }

/-! ## Fixture constructors -/

def v (index : Nat) : ValueId := ValueId.mk index

def attr (name : String) (value : AttrValue) : AttrEntry :=
  { name := name, value := value }

def packLanes (vectorTy : Ty) (operands : List ValueId) : DialectInst :=
  { dialect := dialectName
    op := packLanesOp
    operands := operands
    resultTys := [vectorTy]
    attrs := []
    version := 1 }

def extractLane (vectorTy elemTy : Ty) (vector : ValueId) (lane : Nat) : DialectInst :=
  { dialect := dialectName
    op := extractLaneOp
    operands := [vector]
    resultTys := [elemTy]
    attrs := [attr "vector_ty" (.ty vectorTy), attr "lane" (.u64 lane)]
    version := 1 }

def insertLane (vectorTy : Ty) (vector laneValue : ValueId) (lane : Nat) : DialectInst :=
  { dialect := dialectName
    op := insertLaneOp
    operands := [vector, laneValue]
    resultTys := [vectorTy]
    attrs := [attr "lane" (.u64 lane)]
    version := 1 }

def maskToBits (maskTy : Ty) (mask : ValueId) (resultTy : Ty) : DialectInst :=
  { dialect := dialectName
    op := maskToBitsOp
    operands := [mask]
    resultTys := [resultTy]
    attrs := [attr "mask_ty" (.ty maskTy), attr bitOrderAttr (.str lsbLane0)]
    version := 1 }

/-- Canonical attribute spelling for a reduction kind (Rust `ReduceKind::as_str`). -/
def reduceKindStr : ReduceKind → String
  | .add => reduceAddKind
  | .or => reduceOrKind

def reduce (vectorTy elemTy : Ty) (vector : ValueId) (kind : ReduceKind) : DialectInst :=
  { dialect := dialectName
    op := reduceOp
    operands := [vector]
    resultTys := [elemTy]
    attrs := [attr "vector_ty" (.ty vectorTy),
              attr reduceKindAttr (.str (reduceKindStr kind))]
    version := 1 }

def shuffle (vectorTy : Ty) (vector : ValueId) (indices : List UInt8) : DialectInst :=
  { dialect := dialectName
    op := shuffleOp
    operands := [vector]
    resultTys := [vectorTy]
    attrs := [attr shuffleIndicesAttr (.bytes indices)]
    version := 1 }

end VectorDialect
end TrustIr
