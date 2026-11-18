-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- serde-JSON → Lean IR decoder for the W5b Lean-execution oracle (roadmap
-- WS2.19). Reads the `trust-ir` crate's serde JSON module encoding (the
-- externally-tagged `serde` derive shape: `"Ptr"`, `{"Ref": "I64"}`,
-- `{"Const": {"ty": ..., "value": ...}}`) into the Lean `Inst` / `Ty` /
-- `Constant` mirrors and the evaluator's `BasicBlock` / `EvalFunction`
-- records.
--
-- FAIL CLOSED. Every construct the decoder has no arm for is a structured
-- `DecodeError.unsupported <feature>`, never a default value: a JSON key it
-- does not know makes the affected function body `unsupported`, which the
-- Rust harness COUNTS and RATCHETS rather than compares when reached. A `malformed`
-- error means the input is not the serde schema at all — the harness treats
-- that as a broken oracle, never as a verdict.
--
-- This module is outside the `TrustIr` semantics library (it imports
-- `Lean.Data.Json`, which the axiom-audited library never does) and is only
-- linked into the `trustir_eval` executable.

import Lean.Data.Json
import TrustIr.DecodedModule
import TrustIr.Semantics.FloatFormat
import TrustIr.Semantics.TypedInteger

namespace TrustIrEval

open Lean (Json JsonNumber)
open TrustIr

/-- Lift a `Json` accessor's `Except String`. -/
def lift {α : Type} (ctx : String) : Except String α → D α
  | .ok a => pure a
  | .error e => malformed s!"{ctx}: {e}"

def field (j : Json) (k : String) : D Json := lift k (j.getObjVal? k)
def arr (ctx : String) (j : Json) : D (List Json) := do
  pure (← lift ctx j.getArr?).toList
def nat (ctx : String) (j : Json) : D Nat := lift ctx j.getNat?
def int (ctx : String) (j : Json) : D Int := lift ctx j.getInt?
def str (ctx : String) (j : Json) : D String := lift ctx j.getStr?
def bool (ctx : String) (j : Json) : D Bool := lift ctx j.getBool?

def natField (j : Json) (k : String) : D Nat := do nat k (← field j k)
def boolField (j : Json) (k : String) : D Bool := do bool k (← field j k)
def strField (j : Json) (k : String) : D String := do str k (← field j k)
def listField (j : Json) (k : String) : D (List Json) := do arr k (← field j k)

/-- `null` → `none`. -/
def optional {α : Type} (j : Json) (f : Json → D α) : D (Option α) :=
  if j.isNull then pure none else do pure (some (← f j))

/-- A `wide_i128` / `wide_u128` serde field: a bare JSON number in the
    i64/u64 range, or the decimal STRING serde falls back to outside it. -/
def wideInt (ctx : String) (j : Json) : D Int :=
  match j with
  | .str s =>
    match s.toInt? with
    | some i => pure i
    | none => malformed s!"{ctx}: not a decimal integer string: {s}"
  | .num _ => int ctx j
  | _ => malformed s!"{ctx}: expected an integer or its decimal string"

/-- Select the pinned compiler's native ordered-object fold before elaboration.
The complete original declaration is returned unchanged on the legacy pin. -/
macro "trustIrDecodeCompilerCommand " "{" legacyCommand:command "}" "{" modernCommand:command "}" : command => do
  if Lean.versionString == "4.8.0" then pure legacyCommand
  else if Lean.versionString == "4.30.0-rc2" then pure modernCommand
  else Lean.Macro.throwError "unsupported Lean compiler for TrustIR JSON-object fold"

trustIrDecodeCompilerCommand {
/-- An externally-tagged serde enum: `"Name"` (unit variant, payload `null`)
    or the one-key object `{"Name": payload}`. -/
def tagged (ctx : String) (j : Json) : D (String × Json) :=
  match j with
  | .str s => pure (s, .null)
  | .obj kvs =>
    match trustIrJsonObjectFold kvs (fun acc k v => (k, v) :: acc) [] with
    | [(k, v)] => pure (k, v)
    | _ => malformed s!"{ctx}: expected a single-variant object"
  | _ => malformed s!"{ctx}: expected an enum tag"
} {
/-- An externally-tagged serde enum: `"Name"` (unit variant, payload `null`)
    or the one-key object `{"Name": payload}`. -/
def tagged (ctx : String) (j : Json) : D (String × Json) :=
  match j with
  | .str s => pure (s, .null)
  | .obj kvs =>
    match kvs.foldl (fun acc k v => (k, v) :: acc) [] with
    | [(k, v)] => pure (k, v)
    | _ => malformed s!"{ctx}: expected a single-variant object"
  | _ => malformed s!"{ctx}: expected an enum tag"
}

/-- A two-element JSON array (a serde tuple variant). -/
def pair (ctx : String) (j : Json) : D (Json × Json) := do
  match ← arr ctx j with
  | [a, b] => pure (a, b)
  | _ => malformed s!"{ctx}: expected a 2-tuple"

def valueId (ctx : String) (j : Json) : D ValueId := do pure ⟨← nat ctx j⟩
def blockId (ctx : String) (j : Json) : D BlockId := do pure ⟨← nat ctx j⟩
def funcId (ctx : String) (j : Json) : D FuncId := do pure ⟨← nat ctx j⟩

def fnItemId (ctx : String) (j : Json) : D FuncId := do
  let id ← nat ctx j
  if id ≥ 2 ^ 32 then malformed s!"{ctx}: function item id outside u32"
  pure ⟨id⟩
def valueIds (ctx : String) (j : Json) : D (List ValueId) := do
  (← arr ctx j).mapM (valueId ctx)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

def setRepr (j : Json) : D SetRepr := do
  match ← str "SetRepr" j with
  | "Bitset" => pure .Bitset
  | "Boxed" => pure .Boxed
  | other => unsupported s!"set_repr.{other}"

def fatPtrKind (j : Json) : D FatPtrKind := do
  let (tag, p) ← tagged "FatPtrKind" j
  match tag with
  | "Slice" => pure (.Slice ⟨← nat "Slice" p⟩)
  | "Str" => pure .Str
  | "TraitObject" => pure (.TraitObject (← natField p "trait_id").toUInt32)
  | "ContainerLen" => pure .ContainerLen
  | "ContainerVtable" => pure .ContainerVtable
  | other => unsupported s!"fat_ptr_kind.{other}"

/-- Raw serde StorageLayout fields are u64 type data. Substitution transports
    them exactly, including geometry that later layout/use validation refuses.
    Parsing this type grants no initialized image or by-value storage authority. -/
private def storageTy (j : Json) : D Ty := do
  -- Derived serde accepts both the named-field object and the exact two-field
  -- sequence. Unknown object fields are ignored by the Rust StorageLayout too.
  let (sizeJson, alignJson) ← match j with
    | .arr _ => pair "Storage" j
    | _ => pure (← field j "size_bytes", ← field j "align_bytes")
  let size ← nat "Storage.size_bytes" sizeJson
  if size ≥ 2 ^ 64 then malformed "Storage.size_bytes: outside u64 range"
  let alignment ← nat "Storage.align_bytes" alignJson
  if alignment ≥ 2 ^ 64 then malformed "Storage.align_bytes: outside u64 range"
  pure (.Storage size alignment)

/-- One grammar layer, parameterized by the parser used for recursive children. -/
private def tyLayer (recurse : Json → D Ty) (j : Json) : D Ty := do
  let (tag, p) ← tagged "Ty" j
  match tag with
  | "I8" => pure .I8
  | "I16" => pure .I16
  | "I32" => pure .I32
  | "I64" => pure .I64
  | "I128" => pure .I128
  | "U8" => pure .U8
  | "U16" => pure .U16
  | "U32" => pure .U32
  | "U64" => pure .U64
  | "U128" => pure .U128
  | "Isize" => pure .Isize
  | "Usize" => pure .Usize
  | "Char" => pure .Char
  | "Error" => pure .Error
  | "F16" => pure .F16
  | "F32" => pure .F32
  | "F64" => pure .F64
  | "Bool" => pure .Bool
  | "Ptr" => pure .Ptr
  | "FatPtr" => pure (.FatPtr (← fatPtrKind p))
  | "Struct" => pure (.Struct ⟨← nat "Struct" p⟩)
  | "Array" =>
    let (e, n) ← pair "Array" p
    pure (.Array ⟨← nat "Array.elem" e⟩ (← nat "Array.len" n))
  | "Func" => pure (.Func ⟨← nat "Func" p⟩)
  | "FnItem" => pure (.FnItem (← fnItemId "FnItem" p))
  | "Storage" => storageTy p
  | "Unit" => pure .Unit
  | "Never" => pure .Never
  | "Tuple" => pure (.Tuple (← (← arr "Tuple" p).mapM recurse))
  | "Enum" => pure (.Enum ⟨← nat "Enum" p⟩)
  | "Vector" =>
    -- Rust `Vector(Box<Ty>, u32)` is (elem, lanes); Lean is `Vector lanes elem`.
    let (e, n) ← pair "Vector" p
    pure (.Vector (← nat "Vector.lanes" n) (← recurse e))
  | "Ref" => pure (.Ref (← recurse p))
  | "RefMut" => pure (.RefMut (← recurse p))
  | "PtrConst" => pure (.PtrConst (← recurse p))
  | "PtrMut" => pure (.PtrMut (← recurse p))
  | "Rc" => pure (.Rc (← recurse p))
  | "Set" =>
    let (e, r) ← pair "Set" p
    pure (.Set ⟨← nat "Set.elem" e⟩ (← setRepr r))
  | "Sequence" => pure (.Sequence ⟨← nat "Sequence" p⟩)
  | "Record" => pure (.Record ⟨← nat "Record" p⟩)
  | "Closure" => pure (.Closure ⟨← nat "Closure" p⟩)
  | "Refine" =>
    let (b, q) ← pair "Refine" p
    pure (.Refine ⟨← nat "Refine.base" b⟩ ⟨← nat "Refine.pred" q⟩)
  | "Dialect" =>
    pure (.Dialect (← strField p "namespace") (← strField p "name")
      (← natField p "version").toUInt32)
  | "Handle" => pure (.Handle (← strField p "name") (← strField p "runtime"))
  | other => unsupported s!"ty.{other}"


private partial def tyRecursive (j : Json) : D Ty :=
  tyLayer tyRecursive j

/-- Decode one type layer transparently; recursive children retain the same partial parser. -/
def ty (j : Json) : D Ty :=
  tyLayer tyRecursive j

def tyList (ctx : String) (j : Json) : D (List Ty) := do (← arr ctx j).mapM ty

/-- A level-S type (amendment S): Rust `TyG<TemplateRef>` serde JSON — every
    `Ty` spelling, plus `{"Ext": {"Param": i}}` and `{"Ext": {"Hole": h}}`.
    A constructor with `Ty` children recurses at level S; every other
    constructor is a level-R leaf, decoded by `ty` and embedded. -/
partial def templateTy (j : Json) : D TemplateTy := do
  let (tag, p) ← tagged "TemplateTy" j
  match tag with
  | "Ext" =>
    let (r, n) ← tagged "TemplateRef" p
    match r with
    | "Param" => pure (.param (← nat "Param" n))
    | "Hole" => pure (.hole (← nat "Hole" n))
    | other => unsupported s!"template_ref.{other}"
  | "Tuple" => pure (.Tuple (← (← arr "Tuple" p).mapM templateTy))
  | "Vector" =>
    let (e, n) ← pair "Vector" p
    pure (.Vector (← nat "Vector.lanes" n) (← templateTy e))
  | "Ref" => pure (.Ref (← templateTy p))
  | "RefMut" => pure (.RefMut (← templateTy p))
  | "PtrConst" => pure (.PtrConst (← templateTy p))
  | "PtrMut" => pure (.PtrMut (← templateTy p))
  | "Rc" => pure (.Rc (← templateTy p))
  | _ => pure (embed (← ty j))

-- ---------------------------------------------------------------------------
-- Constants
-- ---------------------------------------------------------------------------

/-- A `Constant::Float` is serialized as `{"bits": <binary64 bits>}` (the
    crate's `float_bits` serde helper), decoded through the model's own IEEE
    decoder so the literal is bit-exact. -/
def floatConst (j : Json) : D Float := do
  pure (decodeBits .binary64 (← natField j "bits"))

def constantLayer (recurse : Json → D Constant) (j : Json) : D Constant := do
  let (tag, p) ← tagged "Constant" j
  match tag with
  | "Int" => pure (.int (← wideInt "Int" p))
  | "U128" =>
    let v ← wideInt "U128" p
    if v < 0 then malformed "U128: negative" else pure (.u128 v.toNat)
  | "Bytes" =>
    let data ← (← listField p "data").mapM (fun b => do
      let n ← nat "Bytes.data" b
      if n < 256 then pure (UInt8.ofNat n) else malformed "Bytes.data: byte > 255")
    pure (.bytes data (← boolField p "utf8"))
  | "Float" => pure (.float (← floatConst p))
  | "Bool" => pure (.bool (← bool "Bool" p))
  | "Aggregate" => pure (.aggregate (← (← arr "Aggregate" p).mapM recurse))
  | "Array" => pure (.array (← (← arr "Array" p).mapM recurse))
  | "Splat" =>
    let count ← natField p "len"
    if count < 2 then malformed "Splat: length must be at least two"
    pure (.splat (← recurse (← field p "elem")) count)
  | "Vector" => pure (.vector (← (← arr "Vector" p).mapM recurse))
  | "Sequence" => pure (.sequence (← (← arr "Sequence" p).mapM recurse))
  | "Set" => pure (.set (← (← arr "Set" p).mapM recurse))
  | "Record" =>
    pure (.record (← (← arr "Record" p).mapM (fun e => do
      let (n, c) ← pair "Record.field" e
      pure (← str "Record.name" n, ← recurse c))))
  | "Closure" =>
    pure (.closure (← funcId "Closure.func" (← field p "func"))
      (← (← listField p "captures").mapM recurse))
  | "FnDef" => pure (.fnDef (← funcId "FnDef" p))
  | "FnItem" => pure (.fnItem (← fnItemId "FnItem" p))
  | "SymbolAddr" =>
    pure (.symbolAddr (← strField p "symbol") (← wideInt "addend" (← field p "addend")))
  | "PhantomData" => pure .phantomData
  -- Crystal lane (E3b): an unwritten struct/tuple lane (a unit variant in serde).
  | "Uninit" => pure .uninit
  | other => unsupported s!"constant.{other}"


/-- Logical transparency of the new public constant proofs belongs only to
    the modern proof compiler. The pinned legacy executable oracle retains its
    previously qualified partial parser boundary and gains no proof cohort. -/
macro "trustIrDecodeModernOnly " declaration:command : command => do
  let empty : Lean.TSyntax `command := ⟨Lean.mkNullNode #[]⟩
  `(trustIrDecodeCompilerCommand { $empty } { $declaration })

trustIrDecodeModernOnly
private partial def constantRecursive (j : Json) : D Constant :=
  constantLayer constantRecursive j

trustIrDecodeCompilerCommand {
/-- Original legacy test-oracle boundary, using the one shared grammar. -/
partial def constant (j : Json) : D Constant :=
  constantLayer constant j
} {
/-- Decode one original constant layer transparently. Recursive children keep
    the same partial parser, as in the existing type-layer interface. -/
def constant (j : Json) : D Constant :=
  constantLayer constantRecursive j
}

trustIrDecodeModernOnly
/-- A scalar integer never obtains meaning from an opaque recursive child.
    This theorem is intentionally unavailable on the legacy test oracle. -/
theorem constant_int (j payload : Json) (value : Int)
    (tag : tagged "Constant" j = .ok ("Int", payload))
    (decoded : wideInt "Int" payload = .ok value) : constant j = .ok (.int value) := by
  simp [constant, constantLayer, tag, decoded, bind, pure, Except.bind, Except.pure]

-- ---------------------------------------------------------------------------
-- Sub-op enums
-- ---------------------------------------------------------------------------

def binOp (j : Json) : D BinOp := do
  match ← str "BinOp" j with
  | "Add" => pure .Add | "Sub" => pure .Sub | "Mul" => pure .Mul
  | "UDiv" => pure .UDiv | "SDiv" => pure .SDiv
  | "URem" => pure .URem | "SRem" => pure .SRem
  | "FAdd" => pure .FAdd | "FSub" => pure .FSub | "FMul" => pure .FMul
  | "FDiv" => pure .FDiv | "FRem" => pure .FRem
  | "FMin" => pure .FMin | "FMax" => pure .FMax
  | "And" => pure .And | "Or" => pure .Or | "Xor" => pure .Xor
  | "Shl" => pure .Shl | "LShr" => pure .LShr | "AShr" => pure .AShr
  | "BAnd" => pure .BAnd | "BOr" => pure .BOr | "BXor" => pure .BXor
  | "RotL" => pure .RotL | "RotR" => pure .RotR | "FCopySign" => pure .FCopySign
  | other => unsupported s!"binop.{other}"

def unOp (j : Json) : D UnOp := do
  match ← str "UnOp" j with
  | "Neg" => pure .Neg | "FNeg" => pure .FNeg | "Not" => pure .Not
  | "FAbs" => pure .FAbs | "FSqrt" => pure .FSqrt
  | "FFloor" => pure .FFloor | "FCeil" => pure .FCeil | "FTrunc" => pure .FTrunc
  | "CtPop" => pure .CtPop | "CtLz" => pure .CtLz | "CtTz" => pure .CtTz
  | "BSwap" => pure .BSwap | "BitReverse" => pure .BitReverse
  | other => unsupported s!"unop.{other}"

def overflowOp (j : Json) : D OverflowOp := do
  match ← str "OverflowOp" j with
  | "AddOverflow" => pure .AddOverflow
  | "SubOverflow" => pure .SubOverflow
  | "MulOverflow" => pure .MulOverflow
  | other => unsupported s!"overflow_op.{other}"

def assertOverflowOp (j : Json) : D AssertOverflowOp := do
  match ← str "AssertOverflowOp" j with
  | "Add" => pure .Add | "Sub" => pure .Sub | "Mul" => pure .Mul | "Div" => pure .Div
  | "Rem" => pure .Rem | "Shl" => pure .Shl | "Shr" => pure .Shr | "Neg" => pure .Neg
  | other => malformed s!"AssertOverflowOp: unknown variant {other}"

/-- Plan item P (wire v52): an `Inst::Assert` kind. Before amendment P serde
    SKIPPED an `Unspecified` kind, so the caller maps an absent key to
    `.Unspecified`; since wire v54 serde always writes it, and the explicit
    `"Unspecified"` reads the same. -/
def assertKind (j : Json) : D AssertKind := do
  let (tag, p) ← tagged "AssertKind" j
  match tag with
  | "Unspecified" => pure .Unspecified
  | "Overflow" => pure (.Overflow (← assertOverflowOp p))
  | "DivByZero" => pure .DivByZero
  | "RemByZero" => pure .RemByZero
  | "BoundsCheck" =>
    pure (.BoundsCheck (← valueId "index" (← field p "index")) (← valueId "len" (← field p "len")))
  | "MisalignedPtr" =>
    pure (.MisalignedPtr (← valueId "required" (← field p "required"))
      (← valueId "found" (← field p "found")))
  | "NullPtr" => pure .NullPtr
  | other => malformed s!"AssertKind: unknown variant {other}"

/-- Amendment P (wire v54): a panic site, serde's `{"entry": E, "location":
    {"Global": G} | {"Value": V}}`. -/
def panicSite (j : Json) : D PanicSite := do
  let entry ← funcId "entry" (← field j "entry")
  let (tag, p) ← tagged "PanicLocation" (← field j "location")
  let location ← match tag with
    | "Global" => pure (PanicLocation.global ⟨← nat "Global" p⟩)
    | "Value" => pure (PanicLocation.value (← valueId "Value" p))
    | other => malformed s!"PanicLocation: unknown variant {other}"
  pure { entry, location }

def icmpOp (j : Json) : D ICmpOp := do
  match ← str "ICmpOp" j with
  | "Eq" => pure .Eq | "Ne" => pure .Ne
  | "Ult" => pure .Ult | "Ule" => pure .Ule | "Ugt" => pure .Ugt | "Uge" => pure .Uge
  | "Slt" => pure .Slt | "Sle" => pure .Sle | "Sgt" => pure .Sgt | "Sge" => pure .Sge
  | other => unsupported s!"icmp_op.{other}"

def fcmpOp (j : Json) : D FCmpOp := do
  match ← str "FCmpOp" j with
  | "OEq" => pure .OEq | "ONe" => pure .ONe | "OLt" => pure .OLt
  | "OLe" => pure .OLe | "OGt" => pure .OGt | "OGe" => pure .OGe
  | "UEq" => pure .UEq | "UNe" => pure .UNe | "ULt" => pure .ULt
  | "ULe" => pure .ULe | "UGt" => pure .UGt | "UGe" => pure .UGe
  | other => unsupported s!"fcmp_op.{other}"

def castOp (j : Json) : D CastOp := do
  match ← str "CastOp" j with
  | "Trunc" => pure .Trunc | "ZExt" => pure .ZExt | "SExt" => pure .SExt
  | "FPTrunc" => pure .FPTrunc | "FPExt" => pure .FPExt
  | "FPToUI" => pure .FPToUI | "FPToSI" => pure .FPToSI
  | "FPToUISat" => pure .FPToUISat | "FPToSISat" => pure .FPToSISat
  | "UIToFP" => pure .UIToFP | "SIToFP" => pure .SIToFP
  | "PtrToInt" => pure .PtrToInt | "IntToPtr" => pure .IntToPtr
  | "PtrToPtr" => pure .PtrToPtr | "Bitcast" => pure .Bitcast
  | "Transmute" => pure .Transmute | "ReifyFnPointer" => pure .ReifyFnPointer
  | other => unsupported s!"cast_op.{other}"

def ordering (j : Json) : D MemOrdering := do
  match ← str "Ordering" j with
  | "Relaxed" => pure .Relaxed | "Acquire" => pure .Acquire
  | "Release" => pure .Release | "AcqRel" => pure .AcqRel
  | "SeqCst" => pure .SeqCst
  | other => unsupported s!"ordering.{other}"

def rmwOp (j : Json) : D AtomicRMWOp := do
  match ← str "AtomicRMWOp" j with
  | "Xchg" => pure .Xchg | "Add" => pure .Add | "Sub" => pure .Sub
  | "And" => pure .And | "Or" => pure .Or | "Xor" => pure .Xor
  | "Max" => pure .Max | "Min" => pure .Min
  | "UMax" => pure .UMax | "UMin" => pure .UMin
  | other => unsupported s!"atomic_rmw_op.{other}"

def allocOrigin (j : Json) : D AllocOrigin := do
  match ← str "AllocOrigin" j with
  | "RustHeap" => pure .RustHeap | "SwiftHeap" => pure .SwiftHeap
  | "CMalloc" => pure .CMalloc | "CleanHeap" => pure .CleanHeap
  | other => unsupported s!"alloc_origin.{other}"

def callingConv (j : Json) : D CallingConv := do
  match ← str "CallingConv" j with
  | "C" => pure .C | "Fast" => pure .Fast | "Cold" => pure .Cold
  | "Rust" => pure .Rust | "Swift" => pure .Swift
  | "CUnwind" => pure .CUnwind | "SysV64" => pure .SysV64
  | "Win64" => pure .Win64 | "Aapcs" => pure .Aapcs
  | "EfiApi" => pure .EfiApi | "VectorCall" => pure .VectorCall
  | "RustCold" => pure .RustCold
  | other => unsupported s!"calling_conv.{other}"

-- ---------------------------------------------------------------------------
-- Instructions
-- ---------------------------------------------------------------------------

def optValueId (j : Json) (k : String) : D (Option ValueId) := do
  optional (← field j k) (valueId k)

def optNat (j : Json) (k : String) : D (Option Nat) := do
  optional (← field j k) (nat k)

/-- Box wire integer carriers mirror Rust serde u32/u64 fields exactly. -/
private def boxUnsignedNat (bits : Nat) (ctx : String) (j : Json) : D Nat := do
  let n ← nat ctx j
  if n < 2 ^ bits then pure n else malformed s!"{ctx}: outside u{bits} range"

/-- Only this serde(default) field accepts omission. Its payload must still be
an object; present nonnull alignments retain the Rust u64 range. -/
private def boxOptionalAlign (j : Json) : D (Option Nat) :=
  match j with
  | .obj _ =>
    match j.getObjVal? "align" with
    | .ok value => optional value (boxUnsignedNat 64 "DominatingCheck.align")
    | .error _ => pure none
  | _ => malformed "DominatingCheck: expected a record"

/-- `Inst::BoxDeref` payload decoders (wire v74). Every enum refuses an
    unknown variant: a fact this decoder cannot name is malformed, never
    defaulted. -/
def boxPointee (j : Json) : D BoxPointee := do
  let (tag, p) ← tagged "BoxPointee" j
  match tag with
  | "Sized" => pure (.sized (← ty (← field p "ty")))
  | other => malformed s!"BoxPointee: unknown variant {other}"

def validityConjunct (j : Json) : D ValidityConjunct := do
  match ← str "ValidityConjunct" j with
  | "NonNull" => pure .nonNull
  | "Aligned" => pure .aligned
  | "Dereferenceable" => pure .dereferenceable
  | "MetadataValid" => pure .metadataValid
  | other => malformed s!"ValidityConjunct: unknown variant {other}"

def premiseRoot (j : Json) : D PremiseRoot := do
  match ← str "PremiseRoot" j with
  | "ParamByValue" => pure .paramByValue
  | "AllocPostcondition" => pure .allocPostcondition
  | "ReturnedBoxDischarged" => pure .returnedBoxDischarged
  | "ReturnedBoxAssumed" => pure .returnedBoxAssumed
  | "ReferenceArgBoxValid" => pure .referenceArgBoxValid
  | other => malformed s!"PremiseRoot: unknown variant {other}"

def standingAssumption (j : Json) : D StandingAssumption := do
  match ← str "StandingAssumption" j with
  | "SafeBody" => pure .safeBody
  | "SoundCallees" => pure .soundCallees
  | "BoxUnique" => pure .boxUnique
  | other => malformed s!"StandingAssumption: unknown variant {other}"

def validityEvidence (j : Json) : D ValidityEvidence := do
  let (tag, p) ← tagged "ValidityEvidence" j
  match tag with
  | "Premise" =>
    pure (.premise (← premiseRoot (← field p "root"))
      (← (← listField p "standing").mapM standingAssumption))
  | "DominatingCheck" =>
    pure (.dominatingCheck (← boxOptionalAlign p))
  | "Obligation" => pure (.obligation ⟨← boxUnsignedNat 32 "ValidityEvidence.obligation" (← field p "obligation")⟩)
  | other => malformed s!"ValidityEvidence: unknown variant {other}"

def conjunctEvidence (j : Json) : D ConjunctEvidence := do
  pure { conjunct := ← validityConjunct (← field j "conjunct")
         evidence := ← validityEvidence (← field j "evidence") }

def boxValidityNonClaim (j : Json) : D BoxValidityNonClaim := do
  match ← str "BoxValidityNonClaim" j with
  | "Uniqueness" => pure .uniqueness
  | "PointeeValidity" => pure .pointeeValidity
  | "Allocator" => pure .allocator
  | other => malformed s!"BoxValidityNonClaim: unknown variant {other}"

def boxValidityFact (j : Json) : D BoxValidityFact := do
  let site ← field j "site"
  let session ← field j "session"
  let item ← (← listField site "item").mapM (fun b => do
    let n ← nat "BoxDerefSite.item" b
    if n < 256 then pure n else malformed "BoxDerefSite.item: byte > 255")
  if item.length != 16 then malformed "BoxDerefSite: item is not 16 bytes" else
  let judged ← match ← str "JudgedBody" (← field session "judged") with
    | "VerificationSnapshot" => pure JudgedBody.verificationSnapshot
    | "OptimizedFallback" => pure JudgedBody.optimizedFallback
    | other => malformed s!"JudgedBody: unknown variant {other}"
  let producing ← match ← str "ProducingSession" (← field session "producing") with
    | "ProofSession" => pure ProducingSession.proofSession
    | "NonProofSession" => pure ProducingSession.nonProofSession
    | other => malformed s!"ProducingSession: unknown variant {other}"
  pure { siteItem := item
         siteOrdinal := ← boxUnsignedNat 32 "BoxDerefSite.ordinal" (← field site "ordinal")
         judged := judged
         producing := producing
         evidence := ← (← listField j "evidence").mapM conjunctEvidence
         notClaimed := ← (← listField j "not_claimed").mapM boxValidityNonClaim }

def switchCase (j : Json) : D SwitchCase := do
  pure { value := ← constant (← field j "value")
         target := ← blockId "target" (← field j "target")
         args := ← valueIds "args" (← field j "args") }

def bindingFrameDef (j : Json) : D BindingFrameDef := do
  let slots ← (← listField j "slots").mapM (fun s => do
    pure ({ name := ← strField s "name", ty := ← ty (← field s "ty") } : BindingSlot))
  pure { id := ⟨← natField j "id"⟩, name := ← strField j "name", slots := slots }

/-- A `DialectOp` payload. Attributes are carried as an EMPTY list: the
    executable model refuses every dialect op before reading its payload
    (`stepInst` → `unsupported.dialect_op`), so no verdict can depend on
    them, and the decoder does not pretend to mirror the attribute schema. -/
def dialectInst (j : Json) : D DialectInst := do
  pure { dialect := ← strField j "dialect"
         op := ← strField j "op"
         operands := ← valueIds "operands" (← field j "operands")
         resultTys := ← tyList "result_tys" (← field j "result_tys")
         attrs := []
         version := ← natField j "version" }

def inst (j : Json) : D Inst := do
  let (tag, p) ← tagged "Inst" j
  let v := fun (k : String) => do valueId k (← field p k)
  let t := fun (k : String) => do ty (← field p k)
  let b := fun (k : String) => do blockId k (← field p k)
  let vs := fun (k : String) => do valueIds k (← field p k)
  match tag with
  | "BinOp" => pure (.BinOp (← binOp (← field p "op")) (← t "ty") (← v "lhs") (← v "rhs"))
  | "UnOp" => pure (.UnOp (← unOp (← field p "op")) (← t "ty") (← v "operand"))
  | "Overflow" =>
    pure (.Overflow (← overflowOp (← field p "op")) (← t "ty") (← v "lhs") (← v "rhs"))
  | "ICmp" => pure (.ICmp (← icmpOp (← field p "op")) (← t "ty") (← v "lhs") (← v "rhs"))
  | "FCmp" => pure (.FCmp (← fcmpOp (← field p "op")) (← t "ty") (← v "lhs") (← v "rhs"))
  | "Cast" =>
    pure (.Cast (← castOp (← field p "op")) (← t "src_ty") (← t "dst_ty") (← v "operand"))
  | "Load" =>
    pure (.Load (← t "ty") (← v "ptr") (← boolField p "volatile") (← optNat p "align"))
  | "Store" =>
    pure (.Store (← t "ty") (← v "ptr") (← v "value") (← boolField p "volatile")
      (← optNat p "align"))
  | "Alloca" => pure (.Alloca (← t "ty") (← optValueId p "count") (← optNat p "align"))
  | "HeapAlloc" =>
    pure (.HeapAlloc (← t "ty") (← optValueId p "count") (← optNat p "align")
      (← allocOrigin (← field p "origin")))
  | "GEP" =>
    pure (.GEP (← t "pointee_ty") (← v "base") (← vs "indices") (← boolField p "inbounds"))
  | "PtrData" => pure (.PtrData (← t "ptr_ty") (← v "ptr"))
  | "PtrMetadata" => pure (.PtrMetadata (← t "ptr_ty") (← t "metadata_ty") (← v "ptr"))
  | "PtrFromParts" =>
    pure (.PtrFromParts (← t "ptr_ty") (← t "metadata_ty") (← v "data") (← v "metadata"))
  | "GlobalAddr" => pure (.GlobalAddr ⟨← natField p "global"⟩)
  | "AtomicLoad" =>
    pure (.AtomicLoad (← t "ty") (← v "ptr") (← ordering (← field p "ordering")))
  | "AtomicStore" =>
    pure (.AtomicStore (← t "ty") (← v "ptr") (← v "value") (← ordering (← field p "ordering")))
  | "AtomicRMW" =>
    pure (.AtomicRMW (← rmwOp (← field p "op")) (← t "ty") (← v "ptr") (← v "value")
      (← ordering (← field p "ordering")))
  | "CmpXchg" =>
    -- Crystal lane (D3): serde SKIPS `weak` when it is false (the strong
    -- instruction's historical encoding), so an absent key is the strong form.
    let weak ← match p.getObjVal? "weak" with
      | .ok w => bool "weak" w
      | .error _ => pure false
    pure (.CmpXchg (← t "ty") (← v "ptr") (← v "expected") (← v "desired")
      (← ordering (← field p "success")) (← ordering (← field p "failure")) weak)
  | "Fence" => pure (.Fence (← ordering (← field p "ordering")))
  | "Br" => pure (.Br (← b "target") (← vs "args"))
  | "CondBr" =>
    pure (.CondBr (← v "cond") (← b "then_target") (← vs "then_args") (← b "else_target")
      (← vs "else_args"))
  | "Switch" =>
    pure (.Switch (← v "value") (← b "default") (← vs "default_args")
      (← (← listField p "cases").mapM switchCase)
      (← boolField p "exhaustive_enum_unreachable"))
  | "Call" => pure (.Call (← funcId "callee" (← field p "callee")) (← vs "args"))
  | "CallCannotUnwind" =>
    pure (.CallCannotUnwind (← funcId "callee" (← field p "callee")) (← vs "args"))
  | "CallIndirectCannotUnwind" =>
    pure (.CallIndirectCannotUnwind (← v "callee") ⟨← natField p "sig"⟩ (← vs "args")
      (← callingConv (← field p "calling_conv")))
  | "CallIndirect" =>
    pure (.CallIndirect (← v "callee") ⟨← natField p "sig"⟩ (← vs "args")
      (← callingConv (← field p "calling_conv")))
  | "Return" => pure (.Return (← vs "values"))
  | "ExtractField" => pure (.ExtractField (← t "ty") (← v "aggregate") (← natField p "field"))
  | "InsertField" =>
    pure (.InsertField (← t "ty") (← v "aggregate") (← natField p "field") (← v "value"))
  | "BoxDeref" =>
    pure (.BoxDeref (← t "ptr_ty") (← boxPointee (← field p "pointee"))
      ⟨← boxUnsignedNat 32 "BoxDeref.operand" (← field p "operand")⟩
      (← boxValidityFact (← field p "fact")))
  | "MakeClosure" =>
    pure (.MakeClosure ⟨← natField p "ty"⟩ (← funcId "func" (← field p "func")) (← vs "captures"))
  | "ArraySplat" => pure (.ArraySplat (← t "ty") (← v "value"))
  | "MakeAggregate" =>
    pure (.MakeAggregate (← t "ty") (← optNat p "variant") (← vs "fields"))
  | "ExtractElement" => pure (.ExtractElement (← t "ty") (← v "array") (← v "index"))
  | "InsertElement" =>
    pure (.InsertElement (← t "ty") (← v "array") (← v "index") (← v "value"))
  | "Const" => pure (.Const (← t "ty") (← constant (← field p "value")))
  | "NullPtr" => pure .NullPtr
  | "Undef" => pure (.Undef (← t "ty"))
  | "Assume" => pure (.Assume (← v "cond"))
  | "Assert" =>
    let kind ← match p.getObjVal? "kind" with
      | .ok k => assertKind k
      | .error _ => pure .Unspecified
    -- Amendment P (wire v54): serde skips an absent site.
    let site ← match p.getObjVal? "site" with
      | .ok .null => pure none
      | .ok j => pure (some (← panicSite j))
      | .error _ => pure none
    pure (.Assert (← v "cond") kind site)
  | "Unreachable" => pure .Unreachable
  | "Copy" => pure (.Copy (← t "ty") (← v "operand"))
  | "Select" => pure (.Select (← t "ty") (← v "cond") (← v "then_val") (← v "else_val"))
  | "SeqMapAddK" => pure (.SeqMapAddK (← t "ty") (← v "seq") (← natField p "k"))
  | "SeqMapNot" => pure (.SeqMapNot (← t "ty") (← v "seq"))
  | "SeqMap" => pure (.SeqMap (← t "ty") (← v "seq") (← funcId "fwd" (← field p "fwd")))
  | "Borrow" => pure (.Borrow (← v "ptr"))
  | "BorrowMut" => pure (.BorrowMut (← v "ptr"))
  | "EndBorrow" => pure (.EndBorrow (← v "borrow_ptr"))
  | "Retain" => pure (.Retain (← v "ptr"))
  | "Release" => pure (.Release (← v "ptr"))
  | "IsUnique" => pure (.IsUnique (← v "ptr"))
  | "Dealloc" => pure (.Dealloc (← v "ptr"))
  -- Crystal lane (wave-DS): decoded faithfully; `stepInst` then refuses it
  -- (`unsupported.destructor`), exactly as the reference interpreter does.
  | "Drop" => pure (.Drop (← t "ty") (← v "ptr"))
  -- Amendment D (wire v55): the unwinding twin, decoded the same way.
  | "DropInvoke" =>
    pure (.DropInvoke (← t "ty") (← v "ptr") (← b "normal_dest") (← vs "normal_args")
      (← b "unwind_dest"))
  | "MemCopy" =>
    pure (.MemCopy (← v "dst") (← v "src") (← v "bytes") (← boolField p "overlap"))
  | "MemSet" => pure (.MemSet (← v "dst") (← v "byte") (← v "bytes"))
  | "OpenFrame" => pure (.OpenFrame (← bindingFrameDef (← field p "def")))
  | "BindSlot" => pure (.BindSlot (← v "frame") (← natField p "slot") (← v "value"))
  | "LoadSlot" => pure (.LoadSlot (← v "frame") (← natField p "slot") (← t "ty"))
  | "CloseFrame" => pure (.CloseFrame (← v "frame"))
  | "CoroSuspend" =>
    pure (.CoroSuspend (← v "frame") (← natField p "state_slot")
      (← int "next_state" (← field p "next_state")) (← v "value"))
  | "Invoke" =>
    pure (.Invoke (← funcId "callee" (← field p "callee")) (← vs "args") (← b "normal_dest")
      (← vs "normal_args") (← b "unwind_dest"))
  | "LandingPad" =>
    pure (.LandingPad (← boolField p "is_cleanup")
      (← (← listField p "catch_type_indices").mapM (nat "catch_type_indices")))
  | "Resume" => pure (.Resume (← v "exn"))
  | "AssertInvoke" =>
    pure (.AssertInvoke (← v "cond") (← assertKind (← field p "kind"))
      (← panicSite (← field p "site")) (← b "normal_dest") (← vs "normal_args")
      (← b "unwind_dest"))
  -- Amendment D, Part 2 (wire v56): `CallIndirect`'s unwinding twin, its
  -- fields decoded as `CallIndirect`'s then `Invoke`'s successors.
  | "InvokeIndirect" =>
    pure (.InvokeIndirect (← v "callee") ⟨← natField p "sig"⟩ (← vs "args")
      (← callingConv (← field p "calling_conv")) (← b "normal_dest") (← vs "normal_args")
      (← b "unwind_dest"))
  | "DialectOp" => pure (.DialectOp (← dialectInst p))
  | other => unsupported s!"inst.{other}"

-- ---------------------------------------------------------------------------
-- Blocks, functions, module
-- ---------------------------------------------------------------------------

def node (j : Json) : D Node := do
  pure { inst := ← inst (← field j "inst"), results := ← valueIds "results" (← field j "results") }

/-- A Rust `Block` carries its terminator as the LAST node of `body`; the Lean
    `BasicBlock` splits it out. A block whose last node is not a terminator is
    malformed IR the validator would have refused. -/
def block (j : Json) : D (BlockId × BasicBlock) := do
  let id ← blockId "id" (← field j "id")
  let params ← (← listField j "params").mapM (fun pj => do
    let (vid, tj) ← pair "params" pj
    pure (← valueId "param" vid, ← ty tj))
  let nodes ← (← listField j "body").mapM node
  match nodes.reverse with
  | [] => malformed s!"block {id.index}: empty body"
  | term :: revBody =>
    if !term.inst.isTerminator then
      malformed s!"block {id.index}: last node is not a terminator"
    else
      let body := revBody.reverse
      pure (id, { params := params
                  body := body.map (·.inst)
                  bodyResultDests := body.map (·.results)
                  terminator := term.inst
                  terminatorResultDests := term.results })

def function (j : Json) : D Function := do
  let blocksJson ← listField j "blocks"
  pure { id := ← funcId "id" (← field j "id")
         name := ← strField j "name"
         ty := ⟨← natField j "ty"⟩
         entry := ← blockId "entry" (← field j "entry")
         isDeclaration := blocksJson.isEmpty
         callingConvention := ← callingConv (← field j "calling_conv")
         blocks := blocksJson.mapM block }

trustIrDecodeCompilerCommand {
/-- ABI records follow the Rust `deny_unknown_fields` schema. An extension
    must be modelled explicitly rather than silently erased. -/
def abiFields (ctx : String) (j : Json) (allowed : List String) : D Unit :=
  match j with
  | .obj kvs =>
    match trustIrJsonObjectFold kvs (fun acc k _ => if allowed.contains k then acc else k :: acc) [] with
    | [] => pure ()
    | key :: _ => unsupported s!"{ctx}.unknown_field.{key}"
  | _ => malformed s!"{ctx}: expected a record"
} {
/-- ABI records follow the Rust `deny_unknown_fields` schema. An extension
    must be modelled explicitly rather than silently erased. -/
def abiFields (ctx : String) (j : Json) (allowed : List String) : D Unit :=
  match j with
  | .obj kvs =>
    match kvs.foldl (fun acc k _ => if allowed.contains k then acc else k :: acc) [] with
    | [] => pure ()
    | key :: _ => unsupported s!"{ctx}.unknown_field.{key}"
  | _ => malformed s!"{ctx}: expected a record"
}

def abiNat (bits : Nat) (ctx : String) (j : Json) : D Nat := do
  let n ← nat ctx j
  if n < 2 ^ bits then pure n else malformed s!"{ctx}: outside u{bits} range"

def abiU64 (j : Json) (key : String) : D Nat := do
  abiNat 64 key (← field j key)

def abiExtension (j : Json) : D AbiExtension := do
  match ← str "AbiExtension" j with
  | "None" => pure .None | "Sign" => pure .Sign | "Zero" => pure .Zero
  | other => unsupported s!"abi_extension.{other}"

def abiCapture (j : Json) : D AbiCapture := do
  match ← str "AbiCapture" j with
  | "Any" => pure .Any | "ReadOnly" => pure .ReadOnly
  | "Address" => pure .Address | "None" => pure .None
  | other => unsupported s!"abi_capture.{other}"

def abiAttributes (j : Json) : D AbiAttributes := do
  abiFields "AbiAttributes" j ["extension", "in_reg", "no_alias", "nonnull", "readonly",
    "no_undef", "writable", "no_free", "capture", "pointee_size", "pointee_align"]
  pure { extension := ← abiExtension (← field j "extension")
         inReg := ← boolField j "in_reg", noAlias := ← boolField j "no_alias"
         nonnull := ← boolField j "nonnull", readonly := ← boolField j "readonly"
         noUndef := ← boolField j "no_undef", writable := ← boolField j "writable"
         noFree := ← boolField j "no_free", capture := ← abiCapture (← field j "capture")
         pointeeSize := ← abiU64 j "pointee_size"
         pointeeAlign := ← optional (← field j "pointee_align") (abiNat 64 "pointee_align") }

def abiRegister (j : Json) : D AbiRegister := do
  abiFields "AbiRegister" j ["class", "bytes"]
  let cls ← match ← strField j "class" with
    | "Integer" => pure AbiRegisterClass.Integer
    | "Float" => pure .Float | "Vector" => pure .Vector
    | other => unsupported s!"abi_register_class.{other}"
  pure { regClass := cls, bytes := ← abiU64 j "bytes" }

def abiScalar (j : Json) : D AbiScalar := do
  abiFields "AbiScalar" j ["register", "source_offset", "source_bytes", "value_bits", "attributes"]
  pure { register := ← abiRegister (← field j "register")
         sourceOffset := ← abiU64 j "source_offset", sourceBytes := ← abiU64 j "source_bytes"
         valueBits := ← abiNat 16 "value_bits" (← field j "value_bits")
         attributes := ← abiAttributes (← field j "attributes") }

def abiUniform (j : Json) : D AbiUniform := do
  abiFields "AbiUniform" j ["unit", "total", "consecutive"]
  pure { unit := ← abiRegister (← field j "unit"), total := ← abiU64 j "total"
         consecutive := ← boolField j "consecutive" }

def abiPassMode (j : Json) : D AbiPassMode := do
  let (tag, p) ← tagged "AbiPassMode" j
  match tag with
  | "Ignore" =>
    if p.isNull then pure .Ignore else malformed "AbiPassMode.Ignore: unexpected payload"
  | "Direct" => pure (.Direct (← abiScalar p))
  | "Pair" =>
    let (a, b) ← pair "AbiPassMode.Pair" p
    pure (.Pair (← abiScalar a) (← abiScalar b))
  | "Cast" =>
    abiFields "AbiPassMode.Cast" p ["pad_i32", "prefix", "rest_offset", "rest", "attributes"]
    pure (.Cast (← boolField p "pad_i32") (← (← listField p "prefix").mapM abiRegister)
      (← optional (← field p "rest_offset") (abiNat 64 "rest_offset"))
      (← abiUniform (← field p "rest")) (← abiAttributes (← field p "attributes")))
  | "Indirect" =>
    abiFields "AbiPassMode.Indirect" p ["attributes", "metadata_attributes", "on_stack", "caller_copy"]
    pure (.Indirect (← abiAttributes (← field p "attributes"))
      (← optional (← field p "metadata_attributes") abiAttributes)
      (← boolField p "on_stack") (← boolField p "caller_copy"))
  | other => unsupported s!"abi_pass_mode.{other}"

def abiBinding (j : Json) : D AbiBinding := do
  abiFields "AbiBinding" j ["place", "source_offset", "source_bytes", "carrier_offset", "carrier_bytes"]
  let (tag, p) ← tagged "AbiBindingPlace" (← field j "place")
  let place ← match tag with
    | "Parameter" => pure (AbiBindingPlace.Parameter (← abiNat 32 tag p))
    | "Result" => pure (.Result (← abiNat 32 tag p))
    | "HiddenResult" => pure (.HiddenResult (← abiNat 32 tag p))
    | other => unsupported s!"abi_binding_place.{other}"
  pure { place := place, sourceOffset := ← abiU64 j "source_offset"
         sourceBytes := ← abiU64 j "source_bytes", carrierOffset := ← abiU64 j "carrier_offset"
         carrierBytes := ← abiU64 j "carrier_bytes" }

def abiArgument (j : Json) : D AbiArgument := do
  abiFields "AbiArgument" j ["size", "align", "mode", "bindings"]
  pure { size := ← abiU64 j "size", align := ← abiU64 j "align"
         mode := ← abiPassMode (← field j "mode")
         bindings := ← (← listField j "bindings").mapM abiBinding }

def abiTarget (j : Json) : D AbiTarget := do
  abiFields "AbiTarget" j ["triple", "data_layout", "abi", "cpu", "features", "target_spec", "pointer_bytes", "little_endian"]
  pure { triple := ← strField j "triple", dataLayout := ← strField j "data_layout"
         abi := ← strField j "abi", cpu := ← strField j "cpu"
         features := ← (← listField j "features").mapM (str "feature")
         targetSpec := ← strField j "target_spec"
         pointerBytes := ← abiNat 8 "pointer_bytes" (← field j "pointer_bytes")
         littleEndian := ← boolField j "little_endian" }

def abiFrontend (j : Json) : D AbiFrontend := do
  abiFields "AbiFrontend" j ["name", "revision"]
  pure { name := ← strField j "name", revision := ← strField j "revision" }

def signatureAbi (j : Json) : D SignatureAbi := do
  abiFields "SignatureAbi" j ["target", "frontend", "convention", "lowered_convention", "source_abi",
    "can_unwind", "variadic", "fixed_count", "arguments", "result"]
  let fixedCount ← abiNat 32 "fixed_count" (← field j "fixed_count")
  let arguments ← (← listField j "arguments").mapM abiArgument
  -- FnAbi excludes an untupled RustCall tail and an appended track_caller
  -- argument from this count, including in a nonvariadic signature.
  if fixedCount > arguments.length then
    malformed "SignatureAbi.fixed_count exceeds the argument census"
  pure { target := ← abiTarget (← field j "target"), frontend := ← abiFrontend (← field j "frontend")
         convention := ← strField j "convention"
         loweredConvention := ← callingConv (← field j "lowered_convention")
         sourceAbi := ← strField j "source_abi", canUnwind := ← boolField j "can_unwind"
         variadic := ← boolField j "variadic", fixedCount := fixedCount
         arguments := arguments
         result := ← abiArgument (← field j "result") }

def funcTyDef (j : Json) : D FuncTyDef := do
  abiFields "FuncTy" j ["params", "returns", "is_vararg", "abi"]
  pure { params := ← tyList "params" (← field j "params")
         returns := ← tyList "returns" (← field j "returns")
         isVararg := ← boolField j "is_vararg"
         abi := ← match j.getObjVal? "abi" with
           | .ok value => optional value signatureAbi
           | .error _ => pure none }

def globalDef (j : Json) : D GlobalDef := do
  pure { ty := ← ty (← field j "ty")
         initializer := ← optional (← field j "initializer") constant
         align := ← optNat j "align" }

def enumTagRepr (j : Json) : D EnumTagRepr := do
  let (tag, _) ← tagged "EnumTagRepr" j
  match tag with
  | "U8" => pure .u8 | "U16" => pure .u16 | "U32" => pure .u32 | "U64" => pure .u64
  | "I8" => pure .i8 | "I16" => pure .i16 | "I32" => pure .i32 | "I64" => pure .i64
  | "U128" => pure .u128 | "I128" => pure .i128
  | other => unsupported s!"enum_tag_repr.{other}"

private def storageNat (j : Json) (name : String) : D Nat := do
  let value ← natField j name
  if value ≥ 2 ^ 64 then malformed s!"{name}: expected u64" else pure value

private def fieldStorageLayout (j : Json) : D FieldStorageLayout := do
  pure { size := ← storageNat j "size", align := ← storageNat j "align" }

private def uninhabitedVariantLayout (j : Json) : D UninhabitedVariantLayout := do
  let variant ← natField j "variant"
  if variant ≥ 2 ^ 32 then malformed "UninhabitedVariantLayout.variant: expected u32"
  let fields ← (← listField j "fields").mapM fieldStorageLayout
  if fields.length ≥ 2 ^ 32 then malformed "UninhabitedVariantLayout.fields: expected u32 census"
  pure { variant, size := ← storageNat j "size", align := ← storageNat j "align", fields }

def enumTagEncoding (j : Json) : D EnumTagEncoding := do
  let (tag, value) ← tagged "EnumTagEncoding" j
  match tag with
  | "Direct" => pure (.direct (← natField value "tag_offset"))
  | "Niche" =>
    let start ← wideInt "niche_start" (← field value "niche_start")
    if start < 0 then malformed "niche_start: expected an unsigned integer"
    else pure (.niche (← natField value "untagged_variant")
      (← natField value "niche_variants_start") (← natField value "niche_variants_end")
      start.toNat (← natField value "niche_offset")
      (← enumTagRepr (← field value "niche_ty")))
  | "Untagged" => pure .untagged
  | "SingleInhabited" =>
    let variant ← natField value "variant"
    if variant ≥ 2 ^ 32 then malformed "SingleInhabited.variant: expected u32"
    else pure (.singleInhabited variant)
  | "DirectWithUninhabited" =>
    let profiles ← (← listField value "variants").mapM uninhabitedVariantLayout
    if profiles.length ≥ 2 ^ 32 then malformed "DirectWithUninhabited.variants: expected u32 census"
    pure (.directWithUninhabited (← storageNat value "tag_offset") profiles)
  | other => unsupported s!"enum_tag_encoding.{other}"

def enumLayoutDescriptor (j : Json) : D EnumLayoutDescriptor := do
  let encoding ← enumTagEncoding (← field j "encoding")
  let size ← natField j "size"
  let align ← natField j "align"
  let offsets ← (← listField j "variant_field_offsets").mapM (fun row => do
    let entries ← arr "variant_field_offsets row" row
    entries.mapM (nat "variant_field_offset"))
  pure { encoding := encoding, size := size, align := align, variantFieldOffsets := offsets }

/-- The original enum's logical and physical declaration. An explicit layout
    is retained verbatim; no descriptor becomes a synthesized canonical one. -/
def enumDef (j : Json) : D EnumDef := do
  let variants ← (← listField j "variants").mapM (fun v => do
    let names ← match v.getObjVal? "field_names" with
      | .error _ => pure []
      | .ok value => (← arr "field_names" value).mapM (str "field_names entry")
    pure ({ name := ← strField v "name", fields := ← tyList "fields" (← field v "fields"), fieldNames := names } : EnumVariantDef))
  let discriminants ← match ← optional (← field j "discriminants") (arr "discriminants") with
    | some ds => ds.mapM (fun d => optional d (wideInt "discriminants"))
    | none => pure []
  pure { id := ⟨← natField j "id"⟩
         name := ← strField j "name"
         variants := variants
         discriminants := discriminants
         tagRepr := ← optional (← field j "repr") enumTagRepr
         layout := ← match j.getObjVal? "layout" with
           | .error _ => pure none
           | .ok value => optional value enumLayoutDescriptor }

def structRepr (j : Json) : D StructRepr := do
  let (tag, value) ← tagged "StructRepr" j
  match tag with
  | "Rust" => pure .rust
  | "C" => pure .c
  | "Transparent" => pure .transparent
  | "Packed" => pure (.packed (← nat "packed alignment" value))
  | other => unsupported s!"struct_repr.{other}"

/-- Preserve the producer's layout declaration, including partial or invalid
    descriptors whose contextual layout query must refuse rather than repair. -/
def structDef (j : Json) : D StructDef := do
  let fields ← (← listField j "fields").mapM (fun f => do
    pure ({ name := ← strField f "name", ty := ← ty (← field f "ty"),
            offset := ← optNat f "offset" } : FieldDef))
  pure { id := ⟨← natField j "id"⟩
         name := ← strField j "name"
         fields := fields
         size := ← optNat j "size"
         align := ← optNat j "align"
         repr := ← match j.getObjVal? "repr" with
           | .error _ => pure .rust
           | .ok value => structRepr value }

def tupleLayoutDescriptor (j : Json) : D TupleLayoutDescriptor := do
  pure { tupleType := ⟨← natField j "tuple_type"⟩
         size := ← natField j "size"
         align := ← natField j "align"
         fieldOffsets := ← (← listField j "field_offsets").mapM (nat "field_offset") }

/-- Named record fields supply their declared types to constant lowering. -/
def recordDef (j : Json) : D RecordDef := do
  let fields ← (← listField j "fields").mapM (fun f => do
    pure ({ name := ← strField f "name", ty := ← ty (← field f "ty"), offset := none } : FieldDef))
  pure { id := ⟨← natField j "id"⟩
         name := ← strField j "name"
         fields := fields }

/-- Select the model from the actual target before evaluating a body. Mirror
    Rust's canonical scalar table; a word size alone does not establish an
    i686/AVR scalar ABI, and big-endian bytes have no rule here. -/
def moduleByteModel (j : Json) : D ByteModel := do
  match j.getObjVal? "target_info" with
  | .error _ => pure .le64
  | .ok .null => pure .le64
  | .ok target =>
    let bytes ← natField target "pointer_size"
    let endian ← strField target "endianness"
    let triple ← strField target "triple"
    let arch := (triple.splitOn "-").headD ""
    let model ← match ByteModel.ofRepresentation bytes (endian == "Little") with
      | some model => pure model
      | none => unsupported "target.byte_model"
    let canonical := match model with
      | .le32 => arch == "wasm32"
      | .le64 => true
    if canonical then pure model else unsupported "target.scalar_layout"

def module (j : Json) : D Module := do
  pure { byteModel := moduleByteModel j
         hasTargetInfo := match j.getObjVal? "target_info" with
           | .error _ | .ok .null => false
           | .ok _ => true
         functions := ← (← listField j "functions").mapM function
         funcTys := ← (← listField j "func_types").mapM funcTyDef
         closureTys := ← match j.getObjVal? "closure_types" with
           | .error _ => pure []
           | .ok rows => do
             (← arr "closure_types" rows).mapM (fun row => do
             pure { func := ⟨← natField row "func"⟩,
                    captures := ← (← listField row "captures").mapM ty })
         globals := ← (← listField j "globals").mapM globalDef
         enums := ← (← listField j "enums").mapM enumDef
         structs := ← (← listField j "structs").mapM structDef
         tupleLayouts := ← match j.getObjVal? "tuple_layouts" with
           | .error _ => pure []
           | .ok rows => do (← arr "tuple_layouts" rows).mapM tupleLayoutDescriptor
         closureLayouts := ← match j.getObjVal? "closure_layouts" with
           | .error _ => pure []
           | .ok rows => do
             (← arr "closure_layouts" rows).mapM (fun row => do
               let closure ← natField row "closure"
               let size ← natField row "size"
               let align ← natField row "align"
               let offsets ← (← listField row "capture_offsets").mapM (nat "capture_offset")
               if closure ≥ 2 ^ 32 || size > word64Max || align > word64Max ||
                   offsets.any (fun offset => offset > word64Max) then
                 malformed "closure layout contains an out-of-range source integer"
               else pure { closure := ⟨closure⟩, size, align, captureOffsets := offsets })
         records := ← match j.getObjVal? "records" with
           | .error _ => pure []
           | .ok rows => do
             (← arr "records" rows).mapM (fun row => do
               let id : RecordId := ⟨← natField row "id"⟩
               match recordDef row with
               | .ok d => pure (id, some d)
               | .error (.unsupported _) => pure (id, none)
               | .error e => throw e)
         types := (← listField j "types").map (fun t =>
           match ty t with
           | .ok t => some t
           | .error _ => none)
         dropGlue := ← match j.getObjVal? "drop_glue" with
           | .ok rows => do
             (← arr "drop_glue" rows).mapM (fun row => do
               pure (← funcId "glue" (← field row "glue"),
                 match ty (← field row "ty") with
                 | .ok t => some t
                 | .error _ => none))
           | .error _ => pure [] }

end TrustIrEval
