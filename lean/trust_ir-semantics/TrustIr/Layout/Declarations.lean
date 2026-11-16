-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Schema
import TrustIr.Semantics.NatIndex
import TrustIr.Semantics.ClosureTypes

namespace TrustIr.SourceLayout

private def mix (left right : Nat) : Nat := (257 * left + right) % 65521
private def stringBucket (text : String) : Nat := text.toList.foldl (fun key ch => mix key ch.toNat) 0

mutual
  /-- A bounded bucket key only. Every lookup still checks exact source type
      identity with the proved structural comparator, including collisions. -/
  def typeBucket : Ty → Nat
    | .I8 => 1 | .I16 => 2 | .I32 => 3 | .I64 => 4 | .I128 => 5
    | .U8 => 6 | .U16 => 7 | .U32 => 8 | .U64 => 9 | .U128 => 10
    | .Isize => 11 | .Usize => 12 | .Char => 13 | .Error => 14
    | .F16 => 15 | .F32 => 16 | .F64 => 17 | .Bool => 18 | .Ptr => 19
    | .FatPtr _ => 20
    | .Struct id => mix 21 id.index
    | .Array id count => mix (mix 22 id.index) count
    | .Func id => mix 23 id.index
    | .FnItem id => mix 42 id.index
    | .Unit => 24 | .Never => 25
    | .Tuple fields => mix 26 (typesBucket fields)
    | .Enum id => mix 27 id.index
    | .Vector count element => mix (mix 28 count) (typeBucket element)
    | .Ref element => mix 29 (typeBucket element)
    | .RefMut element => mix 30 (typeBucket element)
    | .PtrConst element => mix 31 (typeBucket element)
    | .PtrMut element => mix 32 (typeBucket element)
    | .Rc element => mix 33 (typeBucket element)
    | .Set id _ => mix 34 id.index
    | .Sequence id => mix 35 id.index
    | .Record id => mix 36 id.index
    | .Closure id => mix 37 id.index
    | .Refine base predicate => mix (mix 38 base.index) predicate.index
    | .Dialect family name version => mix (mix (mix 39 (stringBucket family)) (stringBucket name)) version.toNat
    | .Storage size align => mix (mix 41 size) align
    | .Handle name runtime => mix (mix 40 (stringBucket name)) (stringBucket runtime)
  def typesBucket : List Ty → Nat
    | [] => 0
    | first :: rest => mix (typeBucket first) (typesBucket rest)
end

theorem same_type_same_bucket (left right : Ty) (same : closureTyEq left right = true) :
    typeBucket left = typeBucket right := by
  cases closureTyEq_sound left right same
  rfl

structure TupleIndex where
  buckets : NatIndexTree (List (Ty × TupleLayoutDescriptor)) := .empty
  refusal : Option Error := none

def TupleIndex.ofRows (types : Array (Option Ty)) : List TupleLayoutDescriptor → TupleIndex
  | [] => {}
  | rows => Id.run do
    let mut index : TupleIndex := {}
    for row in rows do
      if index.refusal.isNone then
        match (types[row.tupleType.index]?).join with
        | none => index := { index with refusal := some (.missingType row.tupleType.index) }
        | some declared =>
          match declared with
          | .Tuple _ =>
            let key := typeBucket declared
            index := { index with buckets := index.buckets.insert key ((declared, row) :: (index.buckets.find key).getD []) }
          | _ => index := { index with refusal := some (.incoherent "tuple" row.tupleType.index) }
    return index

def TupleIndex.lookup (index : TupleIndex) (ty : Ty) : Except Error (Option TupleLayoutDescriptor) :=
  let rec scan : List (Ty × TupleLayoutDescriptor) → Option TupleLayoutDescriptor →
      Except Error (Option TupleLayoutDescriptor)
    | [], found => match index.refusal with | some error => .error error | none => .ok found
    | (declared, row) :: rest, found =>
      if closureTyEq declared ty then
        if found.isSome then .error (.incoherent "tuple" row.tupleType.index)
        else scan rest (some row)
      else scan rest found
  scan ((index.buckets.find (typeBucket ty)).getD []).reverse none

structure ClosureIndex where
  rows : NatIndexTree (List ClosureLayoutDescriptor) := .empty
  refusal : Option Error := none

def ClosureIndex.ofRows (types : Array ClosureTy) (rows : List ClosureLayoutDescriptor) : ClosureIndex := Id.run do
  let mut index : ClosureIndex := {}
  for row in rows do
    if index.refusal.isNone then
      if !(types[row.closure.index]?).isSome then
        index := { index with refusal := some (.incoherent "closure" row.closure.index) }
      else index := { index with rows := index.rows.insert row.closure.index (row :: (index.rows.find row.closure.index).getD []) }
  return index

def ClosureIndex.lookup (index : ClosureIndex) (id : ClosureTyId) : Except Error (Option ClosureLayoutDescriptor) :=
  match (index.rows.find id.index).getD [] with
  | _ :: _ :: _ => .error (.incoherent "closure" id.index)
  | found => match index.refusal with | some error => .error error | none => .ok found.head?

end TrustIr.SourceLayout
