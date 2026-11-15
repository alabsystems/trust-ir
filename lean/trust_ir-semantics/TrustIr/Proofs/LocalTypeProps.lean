-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Eval

namespace TrustIr

/-- Signedness comes from the declared source type, independently of the
    runtime integer carrier that the signed and unsigned types share. -/
theorem typedIntegerValue_i8 (model : ByteModel) (raw : Int) :
    typedIntegerValue model .I8 (.int 8 raw) =
      .ok (toSigned (truncateUnsigned raw 8) 8) := by
  cases model <;> rfl

theorem typedIntegerValue_u8 (model : ByteModel) (raw : Int) :
    typedIntegerValue model .U8 (.int 8 raw) = .ok (truncateUnsigned raw 8) := by
  cases model <;> rfl

/-- Signed interpretation retains a negative integer before a consumer
    applies its own range policy. -/
theorem typedIntegerValue_negative_offset (model : ByteModel) :
    typedIntegerValue model .I8 (.int 8 255) = .ok (-1) := by
  cases model <;> rfl

/-- The index policy rejects the signed interpretation of the same bits. -/
theorem typed_signed_index_refused (model : ByteModel) :
    (do let value ← typedIntegerValue model .I8 (.int 8 255)
        nonnegativeElementIndex value) = .error (.ub "negative element index") := by
  cases model <;> rfl

/-- Unsigned 255 is a valid index in a 257-lane value. No backend lane-count
    condition is introduced by the integer reader. -/
theorem typed_unsigned_index_255 (model : ByteModel) :
    (do let value ← typedIntegerValue model .U8 (.int 8 255)
        nonnegativeElementIndex value) = .ok 255 := by
  cases model <;> rfl

/-- Pointer-width signedness uses the selected model, not host width. -/
theorem typed_isize32_high_bit :
    typedIntegerValue .le32 .Isize (.int 32 2147483648) = .ok (-2147483648) := rfl

theorem typed_usize32_high_bit :
    typedIntegerValue .le32 .Usize (.int 32 2147483648) = .ok 2147483648 := rfl

/-- Type metadata cannot grant a mismatched-width payload integer semantics. -/
theorem typed_integer_width_refused (model : ByteModel) (raw : Int) :
    typedIntegerValue model .I8 (.int 16 raw) =
      .error (.typeError "typed integer: carrier width mismatch") := by
  cases model <;> rfl

/-- Poison inspection precedes declaration family and width checks. -/
theorem typed_integer_poison_priority (model : ByteModel) (ty poisonTy : Ty) :
    typedIntegerValue model ty (.undef poisonTy) =
      .error (.ub "typed integer: use of an uninitialized operand") := rfl

/-- Missing original declarations are an explicit boundary rather than a
    guess that identical runtime bits have a particular signedness. -/
theorem integerOperand_missing_metadata (ctx : EvalContext) (id : ValueId) (raw : Int) :
    ({ ctx with localTypes := none }).integerOperand id (.int 8 raw) =
      .error (.unsupported .ssaTypeTable "original function SSA declarations are unavailable") := rfl

theorem integerOperand_poison_before_metadata (ctx : EvalContext) (id : ValueId) (ty : Ty) :
    ({ ctx with localTypes := none }).integerOperand id (.undef ty) =
      .error (.ub "typed integer: use of an uninitialized operand") := rfl

theorem integerOperand_missing_declaration (ctx : EvalContext) (id : ValueId) (raw : Int) :
    ({ ctx with localTypes := some (fun _ => none) }).integerOperand id (.int 8 raw) =
      .error (.typeError "SSA types: value has no declaration") := rfl

private def directTypeSource (fid : FuncId) : Option FuncTyDef :=
  if fid == FuncId.mk 65537 then
    some { params := [], returns := [.I8, .U8], isVararg := false }
  else none

private def indirectTypeSource (sig : FuncTyId) : Option FuncTyDef :=
  if sig == FuncTyId.mk 9 then
    some { params := [], returns := [.I8], isVararg := false }
  else none

private def sourceTypeParams : List (ValueId × Ty) :=
  [(⟨7⟩, .U64), (⟨99⟩, .Ptr), (⟨88⟩, .Func ⟨9⟩), (⟨5⟩, .I8)]

/-- These are flattened declarations from arbitrary block serialization order,
    not an instruction execution order. IDs need not be dense or sorted. -/
private def sourceTypeNodes : List (Inst × List ValueId) :=
  [(.Copy .I8 ⟨900⟩, [⟨4294967295⟩]),
   (.Call ⟨65537⟩ [], [⟨900⟩, ⟨2⟩]),
   (.Cast .Trunc .U64 .I8 ⟨7⟩, [⟨42⟩]),
   (.Copy .I8 ⟨42⟩, [⟨1017⟩]),
   (.CallIndirect ⟨88⟩ ⟨9⟩ [] .C, [⟨23⟩]),
   (.Load .I8 ⟨99⟩ false none, [⟨65537⟩]),
   (.BinOp .Add .I8 ⟨1017⟩ ⟨23⟩, [⟨1⟩])]

/-- Params, Copy chains, casts, loads, arithmetic and both call forms retain
    actual source types, including multi-return position and sparse max ID. -/
theorem inferLocalTypes_source_producers :
    (inferLocalTypes directTypeSource indirectTypeSource sourceTypeParams sourceTypeNodes).map
      (fun table => [table ⟨4294967295⟩, table ⟨900⟩, table ⟨2⟩, table ⟨42⟩,
        table ⟨1017⟩, table ⟨23⟩, table ⟨65537⟩, table ⟨1⟩, table ⟨5⟩,
        table ⟨7⟩, table ⟨99⟩, table ⟨88⟩, table ⟨1234⟩]) =
      .ok [some .I8, some .I8, some .U8, some .I8, some .I8, some .I8,
        some .I8, some .I8, some .I8, some .U64, some .Ptr, some (.Func ⟨9⟩), none] := by
  simp [inferLocalTypes, inferLocalTypesWithWork, inferLocalTypesWithEvidence,
    LocalTypeInference.addLocalTypeSource, LocalTypeInference.addLocalTypeNode,
    LocalTypeInference.resolveLocalType, LocalTypeInference.finishLocalTypePath,
    localResultTypes, List.foldlM, List.foldl, List.map, List.zip, Bind.bind, Pure.pure,
    Except.bind, Except.pure, Except.map, NatIndex.contains, NatIndex.find?_insert, NatIndex.find?_empty,
    sourceTypeParams, sourceTypeNodes, directTypeSource, indirectTypeSource]

/-- Borrow roots are resolved after declaration collection, including a
    forward serialized chain whose result must remain fat. -/
theorem inferLocalTypes_fat_borrow_chain :
    (inferLocalTypes (fun _ => none) (fun _ => none)
      [(⟨500⟩, .FatPtr .Str)]
      [(.BorrowMut ⟨9⟩, [⟨4294967295⟩]), (.Borrow ⟨500⟩, [⟨9⟩])]).map
      (fun table => table ⟨4294967295⟩) = .ok (some (.FatPtr .Str)) := by
  simp [inferLocalTypes, inferLocalTypesWithWork, inferLocalTypesWithEvidence,
    LocalTypeInference.addLocalTypeSource, LocalTypeInference.addLocalTypeNode,
    LocalTypeInference.resolveLocalType, LocalTypeInference.finishLocalTypePath,
    LocalTypeInference.borrowedLocalType, localResultTypes, List.foldlM, List.foldl,
    List.map, List.zip, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.map, NatIndex.contains,
    NatIndex.find?_insert, NatIndex.find?_empty]

/-- Thin borrows normalize to Ptr rather than copying a Ref spelling. -/
theorem inferLocalTypes_thin_borrow :
    (inferLocalTypes (fun _ => none) (fun _ => none)
      [(⟨500⟩, .Ref .I8)] [(.Borrow ⟨500⟩, [⟨9⟩])]).map
      (fun table => table ⟨9⟩) = .ok (some .Ptr) := by
  simp [inferLocalTypes, inferLocalTypesWithWork, inferLocalTypesWithEvidence,
    LocalTypeInference.addLocalTypeSource, LocalTypeInference.addLocalTypeNode,
    LocalTypeInference.resolveLocalType, LocalTypeInference.finishLocalTypePath,
    LocalTypeInference.borrowedLocalType, localResultTypes, List.foldlM, List.foldl,
    List.map, List.zip, Bind.bind, Pure.pure, Except.bind, Except.pure, Except.map, NatIndex.contains,
    NatIndex.find?_insert, NatIndex.find?_empty]

theorem inferLocalTypes_duplicate_refused :
    (inferLocalTypes (fun _ => none) (fun _ => none) [(⟨42⟩, .I8)]
      [(.Const .I8 (.int 0), [⟨42⟩])]).map (fun table => table ⟨42⟩) =
      .error (.typeError "SSA types: duplicate value declaration") := rfl

theorem inferLocalTypes_result_census_refused :
    (inferLocalTypes (fun _ => none) (fun _ => none) []
      [(.Overflow .AddOverflow .I8 ⟨0⟩ ⟨1⟩, [⟨42⟩])]).map (fun table => table ⟨42⟩) =
      .error (.typeError "SSA types: instruction result count mismatch") := rfl

theorem inferLocalTypes_borrow_cycle_refused :
    (inferLocalTypes (fun _ => none) (fun _ => none) []
      [(.Borrow ⟨2⟩, [⟨1⟩]), (.BorrowMut ⟨1⟩, [⟨2⟩])]).map (fun table => table ⟨1⟩) =
      .error (.typeError "SSA types: cyclic borrow declarations") := rfl

/-- Declared I64 indices retain the existing signed interpretation. This is
    the typed metadata fact required by an explicit coroutine expansion. -/
theorem integerOperand_i64 (ctx : EvalContext) (table : LocalTypeTable)
    (id : ValueId) (raw : Int) (hTable : ctx.localTypes = some table)
    (hType : table id = some .I64) :
    ctx.integerOperand id (.int 64 raw) = .ok (toSigned raw 64) := by
  have normalized : typedIntegerValue ctx.byteModel .I64 (.int 64 raw) =
      .ok (toSigned (truncateUnsigned raw 64) 64) := by
    cases ctx.byteModel <;> rfl
  have read : typedIntegerValue ctx.byteModel .I64 (.int 64 raw) = .ok (toSigned raw 64) := by
    simpa only [toSigned, truncateUnsigned, Int.emod_emod] using normalized
  simpa [EvalContext.integerOperand, Value.isPoison, Value.isUninit,
    hTable, hType, Except.bind] using read

/-- The typed reader keeps the signed I64 interpretation used by the
    immediate coroutine operand, without an untyped signedness fallback. -/
theorem carrierIntegerOperand_i64 (ctx : EvalContext) (table : LocalTypeTable)
    (id : ValueId) (raw : Int) (hTable : ctx.localTypes = some table)
    (hType : table id = some .I64) :
    ctx.carrierIntegerOperand id (.int 64 raw) = .ok (toSigned raw 64) := by
  have read := integerOperand_i64 ctx table id raw hTable hType
  simpa [EvalContext.carrierIntegerOperand, EvalContext.integerOperand,
    typedIntegerCarrierValue, Value.isPoison, Value.isUninit, hTable, hType,
    Except.bind] using read

end TrustIr
