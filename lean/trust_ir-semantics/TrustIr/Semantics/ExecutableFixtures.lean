-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Executable reference-semantics fixtures with stable observable outcomes.
-- These are intentionally small and target-independent: integer wrapping,
-- casts, vector select, structured unsupported cases, and fuel behavior.

import TrustIr.Semantics.Eval
import TrustIr.Semantics.VectorDialect
import TrustIr.Semantics.CompactArrayFixtures

namespace TrustIr

/-!
# Executable Reference Fixtures

This module provides a tiny stable-result surface around the Lean executable
semantics.  The fixtures below are checked by `lake build` via `native_decide`;
they compare normalized successful values and stable error codes rather than
diagnostic strings whose details may legitimately change.
-/

/-- Join strings without depending on formatting instances. -/
def stableJoin (sep : String) : List String → String
  | [] => ""
  | head :: tail => tail.foldl (fun acc item => acc ++ sep ++ item) head

/-- Stable non-recursive rendering for values embedded inside vectors and
    aggregates.  Nested containers are summarized by shape so fixtures do not
    accidentally depend on `repr` output.  Exception: a fat pointer renders
    its metadata lane recursively (one level — metadata is a scalar atom:
    an int64 length or a vtable pointer). -/
def stableValueAtomString : Value → String
  | .int width value => s!"int{width}:{value}"
  | .float value => s!"float:{value}"
  | .bool true => "bool:true"
  | .bool false => "bool:false"
  | .ptr addr _ => s!"ptr:{addr}"
  | .array values => s!"array({values.size})"
  | .aggregate values => s!"aggregate({values.length})"
  | .vector lanes => s!"vector({lanes.length})"
  | .frame _ values => s!"frame({values.length})"
  | .set values => s!"set({values.length})"
  | .sequence values => s!"sequence({values.length})"
  | .record fields => s!"record({fields.length})"
  | .closure func captures => s!"closure:{func.index}:{captures.length}"
  | .fnDef sig func => s!"fnDef:{sig.index}:{func.index}"
  | .typedClosure ty func captures => s!"typedClosure:{ty.index}:{func.index}:{captures.length}"
  | .fatPtr data _ metadata => s!"fatptr:{data}:" ++ stableValueAtomString metadata
  | .partial image => s!"partial({image.length})"
  | .undef ty => s!"undef:{repr ty}"
  | .nullPtr => "null"
  | .uninit => "uninit"

/-- Structural fixture rendering: describes actual stored payloads, never
    enumerates a uniform count or hides the array's contents behind its size. -/
def stableArrayLeafStrings {size : Nat} : CompactArray.Leaf Value size → List String
  | .nil => []
  | .cons value rest => stableValueAtomString value :: stableArrayLeafStrings rest

def stableArrayTreeString {size : Nat} : CompactArray.Tree Value size → String
  | .uniform count value =>
    if count == 0 then "uniform(0)" else s!"uniform({count};{stableValueAtomString value})"
  | .dense _ values => "dense[" ++ stableJoin "," (stableArrayLeafStrings values) ++ "]"
  | .split _ left right => "split(" ++ stableArrayTreeString left ++ "," ++ stableArrayTreeString right ++ ")"
  | .periodic (period := period) unit _ phase count =>
    s!"periodic({period};{phase};{count};" ++ stableArrayTreeString unit ++ ")"

/-- Stable rendering for top-level fixture values. -/
def stableValueString : Value → String
  | .array values => "array:" ++ stableArrayTreeString values.tree
  | .aggregate values =>
    "aggregate[" ++ stableJoin "," (values.map stableValueAtomString) ++ "]"
  | .vector lanes =>
    "vector[" ++ stableJoin "," (lanes.map stableValueAtomString) ++ "]"
  | .sequence values =>
    "sequence[" ++ stableJoin "," (values.map stableValueAtomString) ++ "]"
  | value => stableValueAtomString value

/-- Stable rendering for a list of returned values. -/
def stableValueListString (values : List Value) : String :=
  "[" ++ stableJoin "," (values.map stableValueString) ++ "]"

namespace StepResult

/-- Stable rendering for terminator results. -/
def stableString : StepResult → String
  | .Continue block args =>
    s!"continue:{block.index}:" ++ stableValueListString args
  | .Ret values => "return:" ++ stableValueListString values
  | .Stuck => "stuck"
  | .CallReq callee args =>
    s!"call:{callee.index}:" ++ stableValueListString args
  | .CallIndirectReq addr sig args =>
    s!"call_indirect:{addr}:sig{sig.index}:" ++ stableValueListString args
  | .InvokeReq callee args normalDest _normalArgs unwindDest =>
    s!"invoke:{callee.index}:normal{normalDest.index}:unwind{unwindDest.index}:"
      ++ stableValueListString args
  | .InvokeIndirectReq addr sig args normalDest _normalArgs unwindDest =>
    s!"invoke_indirect:{addr}:sig{sig.index}:normal{normalDest.index}:unwind{unwindDest.index}:"
      ++ stableValueListString args
  | .SeqMapReq fwd elems =>
    s!"seq_map:{fwd.index}:" ++ stableValueListString elems

end StepResult

namespace InstrResult

/-- Stable rendering for a single-instruction result, resolving fresh SSA
    values through the post-state. -/
def stableString (state : MachineState) : InstrResult → String
  | .value none => "value:none"
  | .value (some id) =>
    match state.lookupValue id with
    | some v => "value:" ++ stableValueString v
    | none => s!"value:missing:{id.index}"
  | .values ids =>
    "values:[" ++ stableJoin ","
      (ids.map (fun id =>
        match state.lookupValue id with
        | some v => stableValueString v
        | none => s!"missing:{id.index}")) ++ "]"
  | .terminator result => "terminator:" ++ StepResult.stableString result

end InstrResult

/-- Stable observable outcome for a single instruction. -/
def stepInstStableOutcome (inst : Inst) (state : MachineState) : String :=
  match Sem.run (stepInst inst) state with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error err => "error:" ++ err.code

/-- These manual instruction fixtures carry their authored operand types.
    No declaration is inferred from an integer's raw width or high bit. -/
def typedFixtureContext (declarations : List (ValueId × Ty)) : EvalContext :=
  { EvalContext.empty with
    localTypes := some (fun id => (declarations.find? (fun entry => entry.1 == id)).map Prod.snd) }

def stepTypedInstStableOutcome (declarations : List (ValueId × Ty))
    (inst : Inst) (state : MachineState) : String :=
  match Sem.run (stepInstWithContext (typedFixtureContext declarations) inst) state with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error err => "error:" ++ err.code

def stepTypedInstListStableOutcome (declarations : List (ValueId × Ty))
    (insts : List Inst) (state : MachineState) : String :=
  match Sem.run
      (insts.foldlM (fun _ inst => stepInstWithContext (typedFixtureContext declarations) inst)
        (InstrResult.value none)) state with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error err => "error:" ++ err.code

/-- Stable observable outcome for a declared dialect denotation.

    Dialect ops in this first slice bind one fresh result, so the observable
    value is read from the initial state's next fresh SSA id in the post-state.
    Raw `Inst.DialectOp` execution remains covered by `stepInstStableOutcome`
    and stays unsupported. -/
def declaredDialectStableOutcome
    (mk : DialectInst → Except SemError DialectOpSem)
    (inst : DialectInst) (state : MachineState) : String :=
  match mk inst with
  | .error err => "error:" ++ err.code
  | .ok op =>
    match op.runOp state with
    | .error err => "error:" ++ err.code
    | .ok post =>
      match post.lookupValue (ValueId.mk state.nextValueId) with
      | some value => "ok:value:" ++ stableValueString value
      | none => "ok:value:missing"

/-- Stable observable outcome for a function/block evaluator returning values. -/
def evalValuesStableOutcome (m : Sem (List Value)) (state : MachineState) : String :=
  match Sem.run m state with
  | .ok (values, _) => "ok:return:" ++ stableValueListString values
  | .error err => "error:" ++ err.code

namespace ExecutableFixtures

def v0 : ValueId := ValueId.mk 0
def v1 : ValueId := ValueId.mk 1
def v2 : ValueId := ValueId.mk 2
def v3 : ValueId := ValueId.mk 3
def b0 : BlockId := BlockId.mk 0
def f0 : FuncId := FuncId.mk 0
def f1 : FuncId := FuncId.mk 1
def sig0 : FuncTyId := FuncTyId.mk 0
def ptr0 : Nat := 4096

def stateWith (bindings : List (ValueId × Value)) (nextValueId : Nat) :
    MachineState :=
  let locals := bindings.foldl
    (fun locals binding => locals.set binding.fst binding.snd)
    ValueMap.empty
  { MachineState.empty with locals := locals, nextValueId := nextValueId }

def v4i32 (a b c d : Int) : Value :=
  .vector [.int 32 a, .int 32 b, .int 32 c, .int 32 d]

def v2i64 (a b : Int) : Value :=
  .vector [.int 64 a, .int 64 b]

def intVector (width : Nat) (values : List Int) : Value :=
  .vector (values.map (Value.int width))

def v16i8 (values : List Int) : Value :=
  intVector 8 values

def v8i16 (values : List Int) : Value :=
  intVector 16 values

def v4bool (a b c d : Bool) : Value :=
  .vector [.bool a, .bool b, .bool c, .bool d]

def v2bool (a b : Bool) : Value :=
  .vector [.bool a, .bool b]

def boolVector (values : List Bool) : Value :=
  .vector (values.map Value.bool)

def stepTwoInstStableOutcome (first second : Inst) (state : MachineState) :
    String :=
  match Sem.run (do
      let _ ← stepInst first
      stepInst second) state with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error err => "error:" ++ err.code

def stepThreeInstStableOutcome (first second third : Inst)
    (state : MachineState) : String :=
  match Sem.run (do
      let _ ← stepInst first
      let _ ← stepInst second
      stepInst third) state with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error err => "error:" ++ err.code

/-- Stable observable outcome for a straight-line instruction list: the
    result of the LAST instruction, or the error that stops the run. -/
def stepInstListStableOutcome (insts : List Inst) (state : MachineState) :
    String :=
  match Sem.run
      (insts.foldlM (fun _ inst => stepInst inst) (InstrResult.value none))
      state with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error err => "error:" ++ err.code

def stepThenDeclaredDialectStableOutcome
    (first : Inst)
    (mk : DialectInst → Except SemError DialectOpSem)
    (second : DialectInst) (state : MachineState) : String :=
  match Sem.run (stepInst first) state with
  | .error err => "error:" ++ err.code
  | .ok (_, mid) =>
    match mk second with
    | .error err => "error:" ++ err.code
    | .ok op =>
      match op.runOp mid with
      | .error err => "error:" ++ err.code
      | .ok post =>
        match post.lookupValue (ValueId.mk mid.nextValueId) with
        | some value => "ok:value:" ++ stableValueString value
        | none => "ok:value:missing"

def v8i32 : Value :=
  .vector [.int 32 0, .int 32 1, .int 32 2, .int 32 3,
           .int 32 4, .int 32 5, .int 32 6, .int 32 7]

def i32WrapState : MachineState :=
  stateWith [(v0, .int 32 4294967295), (v1, .int 32 2)] 2

theorem i32_add_wraps_stable :
    stepInstStableOutcome (.BinOp .Add .I32 v0 v1) i32WrapState =
      "ok:value:int32:1" := by
  native_decide

-- Signed-division rounding locks (I8, two's-complement residues). These pin the
-- truncation-toward-zero convention ratified in docs/ub-numerics-policy.md §1 and
-- locked on the Rust side by crates/trust-ir-build/tests/numerics_policy.rs. Each
-- would FAIL under the old Euclidean `Int./`,`Int.%` semantics, so they guard
-- against a regression back to flooring/Euclidean rounding on negative operands.

/-- -7 (u8 249) SDiv 2 = -3 (u8 253), truncating toward zero. Euclidean would
    give -4 (u8 252). -/
def sdivNegState : MachineState := stateWith [(v0, .int 8 249), (v1, .int 8 2)] 2
theorem sdiv_neg_truncates_toward_zero_stable :
    stepInstStableOutcome (.BinOp .SDiv .I8 v0 v1) sdivNegState =
      "ok:value:int8:253" := by
  native_decide

/-- -7 (u8 249) SRem 3 = -1 (u8 255), sign of the dividend. Euclidean emod would
    give 2. -/
def sremNegState : MachineState := stateWith [(v0, .int 8 249), (v1, .int 8 3)] 2
theorem srem_neg_has_dividend_sign_stable :
    stepInstStableOutcome (.BinOp .SRem .I8 v0 v1) sremNegState =
      "ok:value:int8:255" := by
  native_decide

-- Sequence element-op loop locks (SeqMapAddK / SeqMapNot, the give-back loop
-- instructions). These pin the Lean semantics to the reference interpreter
-- (crates/trust-ir/src/interpret.rs `Inst::SeqMapAddK` / `Inst::SeqMapNot`):
-- element-wise wrapping increment at the element width / boolean flip, and
-- type errors on non-sequence operands or wrongly-typed elements.

def seqI32State : MachineState :=
  stateWith [(v0, .sequence [.int 32 1, .int 32 2, .int 32 3])] 1

/-- `seq_map_add_k k=1` over `seq<i32> [1,2,3]` is `[2,3,4]` (loopFwd of
    `for x in &mut l { *x += 1 }`). -/
theorem seq_map_add_k_increments_stable :
    stepInstStableOutcome (.SeqMapAddK (.Sequence (TyId.mk 0)) v0 1) seqI32State =
      "ok:value:sequence[int32:2,int32:3,int32:4]" := by
  native_decide

/-- `seq_map_add_k` wraps at the ELEMENT width: `255 + 1 = 0` at i8. -/
def seqI8WrapState : MachineState :=
  stateWith [(v0, .sequence [.int 8 255])] 1
theorem seq_map_add_k_wraps_at_element_width_stable :
    stepInstStableOutcome (.SeqMapAddK (.Sequence (TyId.mk 0)) v0 1) seqI8WrapState =
      "ok:value:sequence[int8:0]" := by
  native_decide

/-- `seq_map_not` over `seq<bool> [true,false]` is `[false,true]` (loopFwd of
    `for b in &mut l { *b = !*b }`). -/
def seqBoolState : MachineState :=
  stateWith [(v0, .sequence [.bool true, .bool false])] 1
theorem seq_map_not_flips_stable :
    stepInstStableOutcome (.SeqMapNot (.Sequence (TyId.mk 0)) v0) seqBoolState =
      "ok:value:sequence[bool:false,bool:true]" := by
  native_decide

/-- `seq_map_not` on an integer sequence is a type error (mirrors the
    interpreter's "requires a sequence of booleans"). -/
theorem seq_map_not_rejects_ints_stable :
    stepInstStableOutcome (.SeqMapNot (.Sequence (TyId.mk 0)) v0) seqI32State =
      "error:type_error" := by
  native_decide

-- WS3.17 (F-051): sequence ELEMENT ops. The reference interpreter has always
-- executed `ExtractElement` / `InsertElement` over a `Sequence` payload
-- (interpret.rs `eval_extract_element` / `eval_insert_element`, which accept
-- Vector | Array | Sequence | Aggregate); the Lean model type-errored on them
-- and the validator refused them, so all three engines disagreed. These locks
-- pin the agreed rule: an in-range read yields the element, an in-range write
-- yields a SEQUENCE (not an aggregate), and an out-of-range index of either is
-- run-time UB — exactly the array rule, since a sequence's length is a
-- property of the value and no static check can bound it.

def seqReadState : MachineState :=
  stateWith [(v0, .sequence [.int 32 1, .int 32 5, .int 32 15]), (v1, .int 64 1)] 2

/-- Element 1 of `seq<i32> [1,5,15]` is `5`. -/
theorem seq_extract_element_reads_stable :
    stepInstStableOutcome (.ExtractElement .I32 v0 v1) seqReadState =
      "ok:value:int32:5" := by
  native_decide

def seqReadPastEndState : MachineState :=
  stateWith [(v0, .sequence [.int 32 1, .int 32 5, .int 32 15]), (v1, .int 64 3)] 2

/-- Reading past the end of a sequence is UB, not a type error. -/
theorem seq_extract_element_out_of_bounds_is_ub_stable :
    stepInstStableOutcome (.ExtractElement .I32 v0 v1) seqReadPastEndState =
      "error:ub" := by
  native_decide

def seqWriteState : MachineState :=
  stateWith [(v0, .sequence [.int 32 1, .int 32 5, .int 32 15]),
             (v1, .int 64 1), (v2, .int 32 7)] 3

/-- Writing element 1 of `seq<i32> [1,5,15]` yields the SEQUENCE `[1,7,15]`:
    the operand's own constructor survives the update. -/
theorem seq_insert_element_writes_a_sequence_stable :
    stepInstStableOutcome (.InsertElement (.Sequence (TyId.mk 0)) v0 v1 v2) seqWriteState =
      "ok:value:sequence[int32:1,int32:7,int32:15]" := by
  native_decide

def seqWritePastEndState : MachineState :=
  stateWith [(v0, .sequence [.int 32 1, .int 32 5, .int 32 15]),
             (v1, .int 64 3), (v2, .int 32 7)] 3

/-- Writing past the end of a sequence is UB, not a type error. -/
theorem seq_insert_element_out_of_bounds_is_ub_stable :
    stepInstStableOutcome (.InsertElement (.Sequence (TyId.mk 0)) v0 v1 v2) seqWritePastEndState =
      "error:ub" := by
  native_decide

/-- A NON-sequence, non-aggregate operand is still a type error: widening the
    element ops to sequences did not widen them to every value. -/
theorem seq_extract_element_rejects_scalars_stable :
    stepInstStableOutcome (.ExtractElement .I32 v1 v1) seqReadState =
      "error:type_error" := by
  native_decide

-- Fat-pointer trio locks (PtrData / PtrMetadata / PtrFromParts). The THIN
-- fixtures agree with the reference interpreter (interpret.rs eval_ptr_data /
-- eval_ptr_metadata / eval_ptr_from_parts); the FAT fixtures pin the shared
-- `(data, metadata)` `Value.fatPtr` model and its 16-byte memory image.

def thinPtrState : MachineState := stateWith [(v0, .ptr 4096 none)] 1

/-- Thin `ptr_data` is the provenance-preserving identity. -/
theorem ptr_data_thin_identity_stable :
    stepInstStableOutcome (.PtrData .Ptr v0) thinPtrState =
      "ok:value:ptr:4096" := by
  native_decide

/-- Thin `ptr_metadata` is Unit (`aggregate[]` is the Lean Unit value). -/
theorem ptr_metadata_thin_unit_stable :
    stepInstStableOutcome (.PtrMetadata .Ptr .Unit v0) thinPtrState =
      "ok:value:aggregate[]" := by
  native_decide

def thinFromPartsState : MachineState :=
  stateWith [(v0, .ptr 4096 none), (v1, .aggregate [])] 2

/-- Thin `ptr_from_parts` is the identity on the data pointer. -/
theorem ptr_from_parts_thin_identity_stable :
    stepInstStableOutcome (.PtrFromParts .Ptr .Unit v0 v1) thinFromPartsState =
      "ok:value:ptr:4096" := by
  native_decide

def fatSliceTy : Ty := .FatPtr (.Slice (TyId.mk 0))
def fatSliceState : MachineState :=
  stateWith [(v0, .fatPtr 4096 none (.int 64 3))] 1

/-- Fat `ptr_data` projects the data lane as a thin pointer. -/
theorem ptr_data_fat_projects_stable :
    stepInstStableOutcome (.PtrData fatSliceTy v0) fatSliceState =
      "ok:value:ptr:4096" := by
  native_decide

def fatSliceNullState : MachineState :=
  stateWith [(v0, .fatPtr 0 none (.int 64 3))] 1

/-- The zero data lane projects as the canonical null pointer, matching the
    Rust interpreter rather than fabricating a distinct `.ptr 0` value. -/
theorem ptr_data_fat_null_projects_stable :
    stepInstStableOutcome (.PtrData fatSliceTy v0) fatSliceNullState =
      "ok:value:null" := by
  native_decide

/-- Fat `ptr_metadata` projects the metadata lane (slice length, usize). -/
theorem ptr_metadata_fat_projects_stable :
    stepInstStableOutcome (.PtrMetadata fatSliceTy .U64 v0) fatSliceState =
      "ok:value:int64:3" := by
  native_decide

/-- The declared metadata type must match the KIND's metadata type
    (Unit is the thin metadata, not a slice's). -/
theorem ptr_metadata_fat_wrong_decl_stable :
    stepInstStableOutcome (.PtrMetadata fatSliceTy .Unit v0) fatSliceState =
      "error:type_error" := by
  native_decide

def malformedFatSliceState : MachineState :=
  stateWith [(v0, .fatPtr 4096 none (.int 32 3))] 1

/-- Projection does not launder an externally supplied malformed fat value:
    both operations validate the kind's metadata lane before exposing it. -/
theorem ptr_data_fat_bad_metadata_rejected_stable :
    stepInstStableOutcome (.PtrData fatSliceTy v0) malformedFatSliceState =
      "error:type_error" := by
  native_decide

theorem ptr_metadata_fat_bad_metadata_rejected_stable :
    stepInstStableOutcome (.PtrMetadata fatSliceTy .U64 v0) malformedFatSliceState =
      "error:type_error" := by
  native_decide

def fatFromPartsState : MachineState :=
  stateWith [(v0, .ptr 4096 none), (v1, .int 64 3)] 2

/-- Fat `ptr_from_parts` injects (data, metadata) into a `.fatPtr`. -/
theorem ptr_from_parts_fat_injects_stable :
    stepInstStableOutcome (.PtrFromParts fatSliceTy .U64 v0 v1) fatFromPartsState =
      "ok:value:fatptr:4096:int64:3" := by
  native_decide

def fatFromPartsBadMetaState : MachineState :=
  stateWith [(v0, .ptr 4096 none), (v1, .int 32 3)] 2

/-- The metadata operand must INHABIT the declared metadata type
    (an i32 is not a usize length). -/
theorem ptr_from_parts_fat_bad_metadata_stable :
    stepInstStableOutcome (.PtrFromParts fatSliceTy .U64 v0 v1) fatFromPartsBadMetaState =
      "error:type_error" := by
  native_decide

def dynTraitTy : Ty := .FatPtr (.TraitObject 7)
def dynFromPartsState : MachineState :=
  stateWith [(v0, .ptr 4096 none), (v1, .ptr 8192 none)] 2

/-- Trait-object metadata is the vtable pointer. -/
theorem ptr_from_parts_trait_object_stable :
    stepInstStableOutcome (.PtrFromParts dynTraitTy .Ptr v0 v1) dynFromPartsState =
      "ok:value:fatptr:4096:ptr:8192" := by
  native_decide

/-- Decompose-then-recombine is the identity — the executable instance of
    `semFatPtr_roundTrip` (Proofs/MemorySafety.lean) and
    `fatPtr_roundTrip_value` (Proofs/MemoryProps.lean). -/
def fatPtrRoundTripOutcome : String :=
  match Sem.run (do
      let dId ← semPtrData fatSliceTy v0
      let mId ← semPtrMetadata fatSliceTy .U64 v0
      let rId ← semPtrFromParts fatSliceTy .U64 dId mId
      Sem.lookupValue rId) fatSliceState with
  | .ok (v, _) => "ok:" ++ stableValueString v
  | .error err => "error:" ++ err.code

theorem fat_ptr_round_trip_stable :
    fatPtrRoundTripOutcome = "ok:fatptr:4096:int64:3" := by
  native_decide

/-- First-class fat pointers occupy exactly two lanes on the executable
    model's pinned 64-bit target. -/
theorem fat_ptr_byte_size_stable : fatSliceTy.byteSize = some 16 := by
  native_decide

-- WS2.18: the container-tail kinds are classified by what their METADATA
-- means (Rust `PointerMetadataShape::metadata_ty`): `ContainerLen` rides the
-- usize length lane with Slice/Str, `ContainerVtable` the vtable-pointer lane
-- with TraitObject — never a length.
def containerLenTy : Ty := .FatPtr .ContainerLen
def containerVtableTy : Ty := .FatPtr .ContainerVtable

/-- `Arc<str>`'s `*const ArcInner<str>`: length metadata. -/
theorem ptr_from_parts_container_len_stable :
    stepInstStableOutcome (.PtrFromParts containerLenTy .U64 v0 v1) fatFromPartsState =
      "ok:value:fatptr:4096:int64:3" := by
  native_decide

/-- `Arc<dyn Any>`'s `*const ArcInner<dyn Any>`: vtable-pointer metadata. -/
theorem ptr_from_parts_container_vtable_stable :
    stepInstStableOutcome (.PtrFromParts containerVtableTy .Ptr v0 v1) dynFromPartsState =
      "ok:value:fatptr:4096:ptr:8192" := by
  native_decide

/-- A container-vtable word is NEVER a length: declaring `U64` metadata for
    it is refused (the type confusion the Rust enum doc forbids). -/
theorem ptr_from_parts_container_vtable_as_length_refused :
    stepInstStableOutcome (.PtrFromParts containerVtableTy .U64 v0 v1) fatFromPartsState =
      "error:type_error" := by
  native_decide

/-- ... and a container-len length is never a vtable pointer. -/
theorem ptr_from_parts_container_len_as_vtable_refused :
    stepInstStableOutcome (.PtrFromParts containerLenTy .Ptr v0 v1) dynFromPartsState =
      "error:type_error" := by
  native_decide

/-- Both container-tail kinds are the two-word image on the 64-bit pin. -/
theorem container_fat_ptr_byte_size_stable :
    containerLenTy.byteSize = some 16 ∧ containerVtableTy.byteSize = some 16 := by
  native_decide

/-- A malformed metadata lane fails closed at the byte-image boundary. -/
theorem fat_ptr_bad_metadata_encoding_rejected :
    encodeValue (.fatPtr 4096 none (.int 32 3)) = none := by
  native_decide

theorem fat_ptr_float_metadata_encoding_rejected :
    encodeValue (.fatPtr 4096 none (.float 3.0)) = none := by
  native_decide

def fatPtrMemoryState (value : Value) : MachineState :=
  let (addr, mem) := Memory.empty.alloc 16 8 0 .rustStack
  { (stateWith [(v0, .ptr addr (some (AllocId.mk 0))), (v1, value)] 2) with memory := mem }

def fatPtrMemoryRoundTripOutcome (ty : Ty) (value : Value) : String :=
  match Sem.run (do
      semStore ty v0 v1
      let loadedId ← semLoad ty v0
      Sem.lookupValue loadedId) (fatPtrMemoryState value) with
  | .ok (loaded, _) => "ok:" ++ stableValueString loaded
  | .error err => "error:" ++ err.code

/-- Slice/str length metadata survives Store/Load in the same data-then-length
    16-byte layout as the Rust reference interpreter. -/
theorem fat_slice_memory_round_trip_stable :
    fatPtrMemoryRoundTripOutcome fatSliceTy (.fatPtr 4096 none (.int 64 3)) =
      "ok:fatptr:4096:int64:3" := by
  native_decide

/-- Trait-object vtable metadata uses the same second pointer-sized lane and
    survives Store/Load without being confused with slice length metadata. -/
theorem fat_trait_memory_round_trip_stable :
    fatPtrMemoryRoundTripOutcome dynTraitTy (.fatPtr 4096 none (.ptr 8192 none)) =
      "ok:fatptr:4096:ptr:8192" := by
  native_decide

/-- Even though a pointer is one lane wide, it cannot be stored as slice
    length metadata: Store checks the kind, not just the encoded byte count. -/
theorem fat_slice_memory_rejects_pointer_metadata_stable :
    fatPtrMemoryRoundTripOutcome fatSliceTy (.fatPtr 4096 none (.ptr 8192 none)) =
      "error:type_error" := by
  native_decide

-- WS2.18 review: the container-tail kinds through MEMORY, not just the
-- register trio — Store checks the kind's metadata lane and Load decodes it
-- by the kind, so a vtable word can never come back out as a length.

theorem fat_container_len_memory_round_trip_stable :
    fatPtrMemoryRoundTripOutcome (.FatPtr .ContainerLen) (.fatPtr 4096 none (.int 64 3)) =
      "ok:fatptr:4096:int64:3" := by
  native_decide

theorem fat_container_vtable_memory_round_trip_stable :
    fatPtrMemoryRoundTripOutcome (.FatPtr .ContainerVtable) (.fatPtr 4096 none (.ptr 8192 none)) =
      "ok:fatptr:4096:ptr:8192" := by
  native_decide

theorem fat_container_vtable_memory_rejects_length_metadata_stable :
    fatPtrMemoryRoundTripOutcome (.FatPtr .ContainerVtable) (.fatPtr 4096 none (.int 64 3)) =
      "error:type_error" := by
  native_decide

theorem fat_container_len_memory_rejects_pointer_metadata_stable :
    fatPtrMemoryRoundTripOutcome (.FatPtr .ContainerLen) (.fatPtr 4096 none (.ptr 8192 none)) =
      "error:type_error" := by
  native_decide

-- Container-tail fat pointers, projection half (WS3.19; Rust
-- `FatPtrKind::ContainerLen` wire v38, `FatPtrKind::ContainerVtable` wire
-- v40). WS2.18 pinned `PtrFromParts`, the byte size and the Store/Load
-- round-trips above; these pin `PtrMetadata` / `PtrData` and their
-- lane-swapped twins. The DATA lane addresses the container header
-- (`ArcInner<str>` / `ArcInner<dyn Any>`); the METADATA lane is the tail's
-- length (`U64`) or vtable word (`Ptr`). The Rust side of the agreement is
-- `container_tail_null_fat_pointer_constants_zero_their_own_metadata_type`
-- (crates/trust-ir/src/interpret.rs). Exchanging the two lanes in
-- `FatPtrKind.metadataTy` / `metadataTyMatches` fails this file.

def containerLenState : MachineState :=
  stateWith [(v0, .fatPtr 4096 none (.int 64 3))] 1
def containerVtableState : MachineState :=
  stateWith [(v0, .fatPtr 4096 none (.ptr 8192 none))] 1

/-- `ContainerLen` metadata is on the `U64` length lane (a `usize` length,
    `rfl`-level). -/
theorem container_len_metadata_ty_is_u64 :
    FatPtrKind.ContainerLen.metadataTy = .U64 := rfl

/-- `ContainerVtable` metadata is on the `Ptr` vtable lane. -/
theorem container_vtable_metadata_ty_is_ptr :
    FatPtrKind.ContainerVtable.metadataTy = .Ptr := rfl

/-- `PtrMetadata` of a `ContainerLen` fat pointer yields the `U64` length. -/
theorem ptr_metadata_container_len_yields_u64_stable :
    stepInstStableOutcome (.PtrMetadata containerLenTy .U64 v0) containerLenState =
      "ok:value:int64:3" := by
  native_decide

/-- Lane-swap twin: declaring the vtable lane for a `ContainerLen` pointer is
    a type error (a length is not a vtable word). -/
theorem ptr_metadata_container_len_rejects_ptr_decl_stable :
    stepInstStableOutcome (.PtrMetadata containerLenTy .Ptr v0) containerLenState =
      "error:type_error" := by
  native_decide

/-- `PtrMetadata` of a `ContainerVtable` fat pointer yields the vtable word. -/
theorem ptr_metadata_container_vtable_yields_ptr_stable :
    stepInstStableOutcome (.PtrMetadata containerVtableTy .Ptr v0)
        containerVtableState =
      "ok:value:ptr:8192" := by
  native_decide

/-- Lane-swap twin: a vtable word is never read as a `U64` length. -/
theorem ptr_metadata_container_vtable_rejects_u64_decl_stable :
    stepInstStableOutcome (.PtrMetadata containerVtableTy .U64 v0)
        containerVtableState =
      "error:type_error" := by
  native_decide

/-- A length-lane value masquerading as a `ContainerVtable` pointer is refused
    on projection (the stored metadata must inhabit the kind's lane). -/
theorem ptr_metadata_container_vtable_rejects_length_value_stable :
    stepInstStableOutcome (.PtrMetadata containerVtableTy .Ptr v0)
        containerLenState =
      "error:type_error" := by
  native_decide

/-- `ContainerLen` data projects the container header address. -/
theorem ptr_data_container_len_projects_stable :
    stepInstStableOutcome (.PtrData containerLenTy v0) containerLenState =
      "ok:value:ptr:4096" := by
  native_decide

-- Review (WS3.19): adversarial container shapes the fixtures above do not
-- reach. Each pins one edge a plausible mis-modelling would get wrong.

/-- A NULL vtable word is the zero of `ContainerVtable`'s metadata lane (the
    Rust null fat-pointer constant's metadata is `NullPtr`, not an int 0):
    it survives the 16-byte image as `null`, never decoding as a length 0. -/
theorem container_vtable_null_metadata_memory_round_trip_stable :
    fatPtrMemoryRoundTripOutcome containerVtableTy (.fatPtr 4096 none .nullPtr) =
      "ok:fatptr:4096:null" := by
  native_decide

/-- ...and a null vtable word masquerading as `ContainerLen` metadata is
    refused at Store (the `.nullPtr` arm of the `Ptr` lane, distinct from the
    `.ptr` arm the fixture above refuses). -/
theorem container_len_memory_rejects_null_metadata_stable :
    fatPtrMemoryRoundTripOutcome containerLenTy (.fatPtr 4096 none .nullPtr) =
      "error:type_error" := by
  native_decide

def containerLenBadWidthState : MachineState :=
  stateWith [(v0, .ptr 4096 none), (v1, .int 32 3)] 2

/-- A 32-bit length is not the 64-bit model's `usize`: `ContainerLen`
    injection demands an `int64` metadata operand, exactly like `Slice`. -/
theorem ptr_from_parts_container_len_rejects_i32_length_stable :
    stepInstStableOutcome (.PtrFromParts containerLenTy .U64 v0 v1)
        containerLenBadWidthState =
      "error:type_error" := by
  native_decide

/-- The declared metadata type is the EXACT lane `U64`, not the
    pointer-width-generic `Usize` — the Rust validator's
    `check_pointer_metadata_ty` compares against `metadata_ty(64) = U64` by
    equality, so both referees refuse the `Usize` spelling. -/
theorem ptr_metadata_container_len_rejects_usize_decl_stable :
    stepInstStableOutcome (.PtrMetadata containerLenTy .Usize v0) containerLenState =
      "error:type_error" := by
  native_decide

-- Coroutine suspend lock (CoroSuspend, the state-machine `yield` terminator).
-- Pins the macro-expansion semantics to the reference interpreter
-- (crates/trust-ir/src/interpret.rs `Inst::CoroSuspend`): the resume state
-- index is stored into `frame[stateSlot]` AND the yielded value is returned.

/-- Alloca an i64 coroutine frame (ValueId 1), `coro_suspend` recording
    next_state=7 and yielding v0 (int32:42), then load the frame's state
    field back: the suspend returns `[int32:42]` and the frame holds
    `int64:7`. -/
def coroSuspendFixtureOutcome : String :=
  match Sem.run (do
      let _ ← stepInst (.Alloca .I64 none none)
      let sr ← stepInst (.CoroSuspend (ValueId.mk 1) 0 7 v0)
      let loadedId ← semLoad .I64 (ValueId.mk 1)
      let loaded ← Sem.lookupValue loadedId
      match sr with
      | .terminator (.Ret vals) =>
        pure (stableValueListString vals ++ ";state=" ++ stableValueString loaded)
      | _ => pure "unexpected")
    (stateWith [(v0, .int 32 42)] 1) with
  | .ok (s, _) => "ok:" ++ s
  | .error e => "error:" ++ e.code

theorem coro_suspend_stores_state_and_yields_stable :
    coroSuspendFixtureOutcome = "ok:[int32:42];state=int64:7" := by
  native_decide

-- Exception-handling locks (Invoke / LandingPad / Resume). Pin the
-- non-throwing executable model to the reference interpreter
-- (crates/trust-ir/src/interpret.rs): an Invoke runs the call and always
-- takes the NORMAL edge with the callee's returns bound to the invoke's
-- results; a directly-executed LandingPad fails closed; Resume is a
-- structured unsupported (host unwinding is outside the model).

/-- A directly-executed landing pad FAILS CLOSED (WS2.24, completing the
    WS2.5 interpreter change on the Lean side): it is only enterable via an
    unwind edge, which the panic=abort projection never takes, so its two
    results would read registers no unwinder loaded. It formerly bound a
    fabricated `(null, 0)` packed into one aggregate; interpret.rs refuses
    with `UnsupportedInstruction` "landingpad entered without an unwind
    edge", and so does this model — same named reason. -/
theorem landing_pad_direct_entry_fails_closed_stable :
    (match Sem.run (stepInst (.LandingPad true [])) (stateWith [] 0) with
     | .ok _ => "ok"
     | .error err => err.stable) =
      "unsupported.host_unwind:landingpad entered without an unwind edge (unwinding is not modelled; panic=abort)" := by
  native_decide

/-- Resume is a structured unsupported: the executable model never has an
    in-flight host exception (panic=abort; unwind edges are never taken). -/
theorem resume_is_structured_unsupported_stable :
    stepInstStableOutcome (.Resume v0) (stateWith [(v0, .nullPtr)] 1) =
      "error:unsupported.host_unwind" := by
  native_decide

-- WS2.18: the carrier constants, each mirroring the reference interpreter's
-- `constant_to_value` (crates/trust-ir/src/interpret.rs).

/-- A canonical `U128` (above `i128::MAX`) binds at width 128, exactly. -/
theorem const_u128_binds_at_width_128_stable :
    stepInstStableOutcome (.Const .U128 (.u128 (2 ^ 127))) (stateWith [] 0) =
      "ok:value:int128:170141183460469231731687303715884105728" := by
  native_decide

def byteArrayConstantContext (model : ByteModel) : ConstantEvalContext :=
  { byteModel := model
    closures := fun _ => none
    enums := fun _ => none
    structs := fun _ => none
    records := fun _ => none
    types := fun tid =>
      if tid.index == 0 then some .U8 else if tid.index == 1 then some .I8 else none }

def byteArrayConstantOutcome (model : ByteModel) (ty : Ty) (c : Constant) : String :=
  match constValueAtWithDefsIn (byteArrayConstantContext model) ty c with
  | .ok value => "ok:" ++ stableValueString value
  | .error error => "error:" ++ error.code

/-- The actual element table establishes that a Bytes payload is `[u8; N]`. -/
theorem const_bytes_binds_u8_lanes_stable :
    byteArrayConstantOutcome .le64 (.Array (TyId.mk 0) 2) (.bytes [104, 105] true) =
      "ok:array:dense[int8:104,int8:105]" := by
  native_decide

/-- A context-free converter cannot presume a TyId names U8. -/
theorem const_bytes_without_element_table_refused_stable :
    stepInstStableOutcome (.Const (.Array (TyId.mk 0) 2) (.bytes [104, 105] true))
      MachineState.empty = "error:unsupported.enum_def_table" := by
  native_decide

/-- A typed function item retains both signature and target identity. -/
theorem const_fn_def_retains_signature_stable :
    stepInstStableOutcome (.Const (.Func (FuncTyId.mk 0)) (.fnDef (FuncId.mk 3)))
      (stateWith [] 0) = "ok:value:fnDef:0:3" := by
  native_decide

/-- `PhantomData` is the canonical constant spelling of the unit value. -/
theorem const_phantom_data_binds_unit_stable :
    stepInstStableOutcome (.Const .Unit .phantomData) (stateWith [] 0) =
      "ok:value:aggregate[]" := by
  native_decide

def fixtureByteModels : List ByteModel := [.le32, .le64]

theorem const_bytes_type_and_census_checked_stable :
    fixtureByteModels.map (fun model =>
      [byteArrayConstantOutcome model (.Array (TyId.mk 0) 2) (.bytes [104, 105] true),
       byteArrayConstantOutcome model (.Array (TyId.mk 1) 2) (.bytes [104, 105] true),
       byteArrayConstantOutcome model (.Array (TyId.mk 0) 3) (.bytes [104, 105] true)]) =
      List.replicate 2 ["ok:array:dense[int8:104,int8:105]", "error:type_error", "error:type_error"] := by
  native_decide

theorem const_uninit_pointer_field_written_before_read_stable :
    stepInstListStableOutcome
      [.Const (.Tuple [.Ptr]) (.aggregate [.uninit]), .Const .Ptr (.int 0),
       .InsertField (.Tuple [.Ptr]) v0 0 v1, .ExtractField .Ptr v2 0]
      MachineState.empty = "ok:value:null" := by
  native_decide

theorem const_uninit_placement_checked_stable :
    [stepInstStableOutcome (.Const .I8 .uninit) MachineState.empty,
     stepInstStableOutcome
       (.Const (.Tuple [.Tuple [.Ptr]]) (.aggregate [.aggregate [.uninit]])) MachineState.empty] =
      ["error:type_error", "error:type_error"] := by
  native_decide

def nullPointerKinds : List Ty :=
  [.Ptr, fatSliceTy, .FatPtr .Str, dynTraitTy, containerLenTy, containerVtableTy]

def nullPointerSpelling : Ty → Constant
  | .FatPtr _ => .aggregate [.int 0, .int 0]
  | _ => .int 0

/-- Inspect the actual constructors and provenance, which stable rendering
    intentionally does not expose. A null data word never carries provenance. -/
def nullPointerValueCorrect (model : ByteModel) (ty : Ty) (value : Value) : Bool :=
  match ty, value with
  | .Ptr, .nullPtr => true
  | .FatPtr kind, .fatPtr 0 none metadata =>
    match kind, metadata with
    | .Slice _, .int width value | .Str, .int width value
    | .ContainerLen, .int width value => width == model.pointerBits && value == 0
    | .TraitObject _, .nullPtr | .ContainerVtable, .nullPtr => true
    | _, _ => false
  | _, _ => false

def nullPointerConstCorrect (model : ByteModel) (ty : Ty) : Bool :=
  match Sem.run (stepInst (.Const ty (nullPointerSpelling ty)) model) MachineState.empty with
  | .ok (.value (some id), post) =>
    match post.lookupValue id with
    | some value => nullPointerValueCorrect model ty value
    | none => false
  | _ => false

/-- Both targets construct canonical thin nulls and all five wide-pointer
    kinds, with the kind's own zero metadata and no data provenance. -/
theorem const_null_pointer_kinds_preserve_representation_stable :
    fixtureByteModels.all (fun model => nullPointerKinds.all (nullPointerConstCorrect model)) =
      true := by
  native_decide

theorem const_thin_null_binds_pointer_stable :
    stepInstStableOutcome (.Const .Ptr (.int 0)) MachineState.empty =
      "ok:value:null" := by
  native_decide

/-- The integer Const path cannot bypass the checked pointer converter. -/
theorem const_nonzero_pointer_refused_stable :
    stepInstStableOutcome (.Const .Ptr (.int 1)) MachineState.empty =
      "error:type_error" := by
  native_decide

/-- Total bit width does not make an integer literal a float constant. -/
theorem const_integer_at_float_type_refused_stable :
    stepInstStableOutcome (.Const .F32 (.int 0)) MachineState.empty =
      "error:type_error" := by
  native_decide

theorem const_nonzero_fat_pointer_refused_stable :
    stepInstStableOutcome (.Const fatSliceTy (.aggregate [.int 0, .int 1]))
      MachineState.empty = "error:type_error" := by
  native_decide

/-- Known pointer grammar is checked before unresolved float width. -/
theorem const_malformed_fat_float_pair_refused_stable :
    stepInstStableOutcome (.Const fatSliceTy (.aggregate [.int 0, .float 0.1]))
      MachineState.empty = "error:type_error" := by
  native_decide

theorem const_nested_nonzero_pointer_refused_stable :
    stepInstStableOutcome
      (.Const (.Tuple [.Ptr, .Vector 2 .Ptr])
        (.aggregate [.int 0, .vector [.int 0, .int 1]]))
      MachineState.empty = "error:type_error" := by
  native_decide

def checkedConstantStableOutcome : Except SemError Value → String
  | .ok value => "ok:" ++ stableValueString value
  | .error error => "error:" ++ error.code

def nullPointerConstantContext (model : ByteModel) : ConstantEvalContext :=
  { byteModel := model
    closures := fun _ => none
    enums := fun _ => none
    structs := fun _ => none
    records := fun _ => none
    types := fun tid => if tid.index == 0 then some .Ptr else none }

/-- Named element types reach the same checked leaf converter. -/
theorem const_contextual_null_sequence_preserves_pointers_stable :
    fixtureByteModels.map (fun model => checkedConstantStableOutcome
      (constValueAtWithDefsIn (nullPointerConstantContext model) (.Sequence (TyId.mk 0))
        (.sequence [.int 0, .int 0]))) =
      ["ok:sequence[null,null]", "ok:sequence[null,null]"] := by
  native_decide

theorem const_contextual_nonzero_pointer_refused_stable :
    fixtureByteModels.map (fun model => checkedConstantStableOutcome
      (constValueAtWithDefsIn (nullPointerConstantContext model) (.Sequence (TyId.mk 0))
        (.sequence [.int 0, .int 1]))) =
      ["error:type_error", "error:type_error"] := by
  native_decide

/-- A link-time address has no compile-time value: refused fail-closed. -/
theorem const_symbol_addr_refused_stable :
    stepInstStableOutcome (.Const .Ptr (.symbolAddr "vtable" 0)) (stateWith [] 0) =
      "error:unsupported.link_time_address" := by
  native_decide

/-- ... at ANY nesting depth (a vtable slot inside an aggregate), never
    laundered through `Value.ofConstant`'s placeholder arm. -/
theorem const_nested_symbol_addr_refused_stable :
    stepInstStableOutcome
      (.Const (.Tuple [.Ptr, .Ptr]) (.aggregate [.int 0, .symbolAddr "f" 8]))
      (stateWith [] 0) = "error:unsupported.link_time_address" := by
  native_decide

/-- Symbol-address refusal keeps precedence even when another pointer lane
    would independently fail its null-only grammar. -/
theorem const_symbol_addr_precedes_pointer_grammar_stable :
    stepInstStableOutcome
      (.Const (.Tuple [.Ptr, .Ptr]) (.aggregate [.int 1, .symbolAddr "f" 8]))
      MachineState.empty = "error:unsupported.link_time_address" := by
  native_decide

def pointerComparisonFixtureOutcome (model : ByteModel) (op : ICmpOp)
    (lhs rhs : Value) : String :=
  match Sem.run (do
      let id ← semICmpInst op .Ptr v0 v1 model
      Sem.lookupValue id) (stateWith [(v0, lhs), (v1, rhs)] 2) with
  | .ok (value, _) => "ok:" ++ stableValueString value
  | .error error => "error:" ++ error.code

def pointerComparisonFixtureOps : List ICmpOp :=
  [.Eq, .Ne, .Slt, .Sle, .Sgt, .Sge, .Ult, .Ule, .Ugt, .Uge]

theorem pointer_icmp_all_predicates_low_addresses_stable :
    fixtureByteModels.map (fun model => pointerComparisonFixtureOps.map (fun op =>
      pointerComparisonFixtureOutcome model op (.ptr 4096 none) (.ptr 8192 none))) =
      List.replicate 2 ["ok:bool:false", "ok:bool:true", "ok:bool:true", "ok:bool:true",
        "ok:bool:false", "ok:bool:false", "ok:bool:true", "ok:bool:true",
        "ok:bool:false", "ok:bool:false"] := by
  native_decide

theorem pointer_icmp_32_high_bit_signed_unsigned_stable :
    [.Slt, .Ult].map (fun op => pointerComparisonFixtureOutcome .le32 op
      (.ptr 2147483648 none) .nullPtr) = ["ok:bool:true", "ok:bool:false"] := by
  native_decide

theorem pointer_icmp_high_address_refused_stable :
    fixtureByteModels.map (fun model => pointerComparisonFixtureOutcome model .Eq
      (.ptr model.addressLimit none) .nullPtr) =
      ["error:ub", "error:ub"] := by
  native_decide

theorem pointer_icmp_poison_precedes_pointer_shape_stable :
    fixtureByteModels.map (fun model =>
      [pointerComparisonFixtureOutcome model .Eq (.ptr model.addressLimit none) (.partial [none]),
       pointerComparisonFixtureOutcome model .Eq (.partial [none]) (.int 8 0)]) =
      List.replicate 2 ["error:ub", "error:ub"] := by
  native_decide

theorem pointer_icmp_uses_address_independent_of_provenance_stable :
    fixtureByteModels.map (fun model =>
      [pointerComparisonFixtureOutcome model .Eq (.ptr 4096 (some (AllocId.mk 7))) (.ptr 4096 none),
       pointerComparisonFixtureOutcome model .Eq (.ptr 0 none) .nullPtr]) =
      List.replicate 2 ["ok:bool:true", "ok:bool:true"] := by
  native_decide

-- WS2.18 review: `Switch` over the new constant carriers. The interpreter
-- (interpret.rs `Inst::Switch`) scans cases IN ORDER, converting each at the
-- scrutinee's type and comparing: a canonical `U128` case is a real case, and a
-- case it cannot convert (a link-time address) is an error, never a miss.

def u128SwitchState : MachineState := stateWith [(v0, .int 128 (2 ^ 127))] 1

/-- A canonical `U128` case (above `i128::MAX`) is TAKEN by an equal
    width-128 scrutinee. Before the review fix the Lean scan fell through to
    the default edge here while the interpreter took the case. -/
theorem switch_u128_case_taken_stable :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) []
        [{ value := .u128 (2 ^ 127), target := BlockId.mk 1, args := [] }] false)
      u128SwitchState = "ok:terminator:continue:1:[]" := by
  native_decide

/-- ... and an unequal `U128` case misses to the default edge (no over-match). -/
theorem switch_u128_case_miss_takes_default_stable :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) []
        [{ value := .u128 (2 ^ 127 + 1), target := BlockId.mk 1, args := [] }] false)
      u128SwitchState = "ok:terminator:continue:2:[]" := by
  native_decide

/-- A `U128` case never equals a narrower scrutinee holding the same number:
    the interpreter converts it only at `U128`. -/
theorem switch_u128_case_needs_width_128_stable :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) []
        [{ value := .u128 5, target := BlockId.mk 1, args := [] }] false)
      (stateWith [(v0, .int 64 5)] 1) = "ok:terminator:continue:2:[]" := by
  native_decide

/-- A case holding a link-time address, once the in-order scan reaches it, is
    refused fail-closed — never skipped to a later matching case or to the
    default edge (the third constant entry point, beside `Const` and the
    global initializer). -/
theorem switch_symbol_addr_case_refused_stable :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) []
        [{ value := .symbolAddr "f" 0, target := BlockId.mk 3, args := [] },
         { value := .u128 (2 ^ 127), target := BlockId.mk 1, args := [] }] false)
      u128SwitchState = "error:unsupported.link_time_address" := by
  native_decide

/-- ... and, exactly as the interpreter's early return, a case that matches
    BEFORE the scan reaches the address is taken. -/
theorem switch_match_before_symbol_addr_case_taken_stable :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) []
        [{ value := .u128 (2 ^ 127), target := BlockId.mk 1, args := [] },
         { value := .symbolAddr "f" 0, target := BlockId.mk 3, args := [] }] false)
      u128SwitchState = "ok:terminator:continue:1:[]" := by
  native_decide

/-- `exhaustiveEnumUnreachable` is carried, not interpreted: a miss still takes
    the default edge, exactly as the reference interpreter does. -/
theorem switch_exhaustive_flag_miss_takes_default_stable :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) []
        [{ value := .int 7, target := BlockId.mk 1, args := [] }] true)
      (stateWith [(v0, .int 32 3)] 1) = "ok:terminator:continue:2:[]" := by
  native_decide

/-- Explicit host-unwind call boundaries refuse before consulting any operand.
    This is coverage/refusal, not a proof that a callee cannot panic. -/
theorem call_cannot_unwind_is_structured_unsupported_stable :
    stepInstStableOutcome (.CallCannotUnwind ⟨999⟩ [⟨999⟩]) MachineState.empty =
      "error:unsupported.call_unwind_boundary" := by native_decide

theorem call_indirect_cannot_unwind_is_structured_unsupported_stable :
    stepInstStableOutcome (.CallIndirectCannotUnwind ⟨999⟩ ⟨999⟩ [⟨999⟩] .Fast)
      MachineState.empty = "error:unsupported.call_unwind_boundary" := by native_decide

/-- A BARE drop (no module context, so no drop-glue table) is a structured
    unsupported, and this fixture is the INTERPRETER AGREEMENT: the Rust
    reference interpreter answers `UnsupportedInstruction` ("Drop: no module,
    so no drop-glue table", amendment D) and the executable model answers
    `error:unsupported.destructor`. Both REFUSE; neither invents a step: a drop
    frees and can run arbitrary user code, so a model that stepped over it
    would agree with the interpreter about a program neither of them ran.
    With a table, a drop runs its glue (`drop_resolved_runs_glue_stable`). -/
theorem drop_is_structured_unsupported_stable :
    stepInstStableOutcome (.Drop .I32 v0) (stateWith [(v0, .nullPtr)] 1) =
      "error:unsupported.destructor" := by
  native_decide

/-- The refusal does not depend on the dropped TYPE: an aggregate type refuses
    exactly as a scalar one does. Pinned because the natural wrong fix -- "drop
    is a no-op for types without a destructor" -- would make the answer
    type-dependent, and the producer emits `Drop` only where rustc says the type
    needs dropping in the first place. -/
theorem drop_refuses_at_an_aggregate_type_stable :
    stepInstStableOutcome (.Drop (.Tuple [.I32, .I32]) v0) (stateWith [(v0, .nullPtr)] 1) =
      "error:unsupported.destructor" := by
  native_decide

/-- A WEAK compare-exchange is a structured unsupported, and this fixture is
    the INTERPRETER AGREEMENT: the Rust reference interpreter answers
    `Inst::CmpXchg weak: a spurious failure is nondeterministic ...` (a typeError
    on its own refusal channel) and the executable model answers
    `error:unsupported.weak_cmpxchg`. Both REFUSE; neither steps it as strong,
    which would delete its spurious-failure executions. The state here would
    make the STRONG instruction fault (a null pointer), so the answer also pins
    that the refusal comes first and does not read the state. -/
theorem weak_cmpxchg_is_structured_unsupported_stable :
    stepInstStableOutcome (.CmpXchg .I8 v0 v1 v2 .SeqCst .SeqCst true)
      (stateWith [(v0, .nullPtr), (v1, .int 8 7), (v2, .int 8 9)] 3) =
      "error:unsupported.weak_cmpxchg" := by
  native_decide

/-- The STRONG instruction over the same state still runs `semCmpXchg` (and
    faults on the null pointer as undefined behaviour): the `weak` flag changes
    the weak form only. -/
theorem strong_cmpxchg_still_steps_stable :
    stepInstStableOutcome (.CmpXchg .I8 v0 v1 v2 .SeqCst .SeqCst false)
      (stateWith [(v0, .nullPtr), (v1, .int 8 7), (v2, .int 8 9)] 3) =
      "error:ub" := by
  native_decide

/-- -8 (u8 248) AShr 1 = -4 (u8 252): arithmetic shift = floor division by 2. -/
def ashrNegState : MachineState := stateWith [(v0, .int 8 248), (v1, .int 8 1)] 2
theorem ashr_neg_floors_stable :
    stepInstStableOutcome (.BinOp .AShr .I8 v0 v1) ashrNegState =
      "ok:value:int8:252" := by
  native_decide

/-- -1 (u8 255) AShr 1 = -1 (u8 255): sign-extending arithmetic shift. -/
def ashrAllOnesState : MachineState := stateWith [(v0, .int 8 255), (v1, .int 8 1)] 2
theorem ashr_all_ones_sticky_stable :
    stepInstStableOutcome (.BinOp .AShr .I8 v0 v1) ashrAllOnesState =
      "ok:value:int8:255" := by
  native_decide

-- FRem exact-fmod differential locks (docs/ub-numerics-policy.md §2). Expected
-- values are the BIT-EXACT libm fmod results computed by the Rust reference
-- interpreter (`%` on f64) and mirrored by crates/trust-ir-build/tests/
-- numerics_policy.rs (frem_* tests over the same operand bits). Operands and
-- expectations are written in exact dyadic form `±m·2^e` so no decimal parsing
-- or Float printing is in the trust path.

/-- Build the exact float `(-1)^neg · m · 2^e` (exact for `m < 2^53`). -/
def mkDyadic (neg : Bool) (m : Nat) (e : Int) : Float :=
  let mag := (Float.ofNat m).scaleB e
  if neg then -mag else mag

def infF : Float := (1.0 : Float) / 0.0

/-- Bit-faithful rendering of a Float: `±mp e` with `m ∈ [2^52, 2^53)` from the
    frExp normalization (injective on finite doubles, distinguishes ±0). -/
def floatExactString (f : Float) : String :=
  if f.isNaN then "nan"
  else if f.isInf then (if f < 0.0 then "-inf" else "+inf")
  else if f == 0.0 then (if (1.0 / f) < 0.0 then "-0" else "+0")
  else
    let sign := if f < 0.0 then "-" else "+"
    let (frac, e) := f.abs.frExp
    let m := (frac.scaleB 53).toUInt64.toNat
    s!"{sign}{m}p{e - 53}"

def fremExactOutcome (lhs rhs : Float) : String :=
  match semFloatBinOp .FRem lhs rhs with
  | .ok value => "ok:" ++ floatExactString value
  | .error err => "error:" ++ err.code

/-- 5.25 % 2.0 = 1.25 (bits 0x3ff4000000000000). -/
theorem frem_pos_simple_stable :
    fremExactOutcome (mkDyadic false 5910974510923776 (-50))
        (mkDyadic false 4503599627370496 (-51)) =
      "ok:+5629499534213120p-52" := by
  native_decide

/-- -7.5 % 2.25 = -0.75: the result takes the DIVIDEND's sign
    (bits 0xbfe8000000000000). -/
theorem frem_neg_dividend_stable :
    fremExactOutcome (mkDyadic true 8444249301319680 (-50))
        (mkDyadic false 5066549580791808 (-51)) =
      "ok:-6755399441055744p-53" := by
  native_decide

/-- 7.5 % -2.25 = +0.75: the divisor's sign is ignored. -/
theorem frem_neg_divisor_stable :
    fremExactOutcome (mkDyadic false 8444249301319680 (-50))
        (mkDyadic true 5066549580791808 (-51)) =
      "ok:+6755399441055744p-53" := by
  native_decide

/-- -5.5 % -2.0 = -1.5. -/
theorem frem_both_negative_stable :
    fremExactOutcome (mkDyadic true 6192449487634432 (-50))
        (mkDyadic true 4503599627370496 (-51)) =
      "ok:-6755399441055744p-52" := by
  native_decide

/-- 6.75 % 1.1 = 0.14999999999999947 (0x3fc3333333333320): non-dyadic-decimal
    divisor, remainder exact on the ROUNDED operand values. -/
theorem frem_non_dyadic_divisor_stable :
    fremExactOutcome (mkDyadic false 7599824371187712 (-50))
        (mkDyadic false 4953959590107546 (-52)) =
      "ok:+5404319552844576p-55" := by
  native_decide

/-- 1e308 % 3.0 = 2.0. The former rounded formula collapsed this to +0.0;
    exact fmod (and the interpreter) give 2.0 — this fixture FAILS under the
    pre-exact semantics, locking the reconciliation. -/
theorem frem_huge_dividend_stable :
    fremExactOutcome (mkDyadic false 5010420900022432 971)
        (mkDyadic false 6755399441055744 (-51)) =
      "ok:+4503599627370496p-51" := by
  native_decide

/-- 1e308 % 1e-308 = 3.498445546245627e-309 (subnormal, 0x00028401cf53d610).
    The former rounded formula overflowed the intermediate quotient and
    returned -inf. -/
theorem frem_huge_by_tiny_stable :
    fremExactOutcome (mkDyadic false 5010420900022432 971)
        (mkDyadic false 2024022533073106 (-1074)) =
      "ok:+5664746093064320p-1077" := by
  native_decide

/-- 1.0 % (3·2^-1074) = 2^-1074 (the minimum positive subnormal, bits 0x1). -/
theorem frem_subnormal_divisor_stable :
    fremExactOutcome (mkDyadic false 4503599627370496 (-52))
        (mkDyadic false 3 (-1074)) =
      "ok:+4503599627370496p-1126" := by
  native_decide

/-- -0.0 % 3.0 = -0.0: fmod preserves the dividend's zero sign. The former
    rounded formula returned +0.0. -/
theorem frem_negative_zero_dividend_stable :
    fremExactOutcome (mkDyadic true 0 0)
        (mkDyadic false 6755399441055744 (-51)) =
      "ok:-0" := by
  native_decide

/-- -6.0 % 3.0 = -0.0: a zero remainder keeps the dividend's sign. -/
theorem frem_zero_remainder_negative_dividend_stable :
    fremExactOutcome (mkDyadic true 6755399441055744 (-50))
        (mkDyadic false 6755399441055744 (-51)) =
      "ok:-0" := by
  native_decide

/-- 5.0 % inf = 5.0 (finite % infinite returns the dividend). The former
    rounded formula returned NaN. -/
theorem frem_finite_by_inf_stable :
    fremExactOutcome (mkDyadic false 5629499534213120 (-50)) infF =
      "ok:+5629499534213120p-50" := by
  native_decide

/-- inf % 3.0 = NaN. -/
theorem frem_inf_dividend_stable :
    fremExactOutcome infF (mkDyadic false 6755399441055744 (-51)) =
      "ok:nan" := by
  native_decide

/-- 5.0 % 0.0 = NaN (fmod domain error is a NaN value, not UB). -/
theorem frem_by_zero_stable :
    fremExactOutcome (mkDyadic false 5629499534213120 (-50))
        (mkDyadic false 0 0) =
      "ok:nan" := by
  native_decide

/-- Full-dispatch lock: `.BinOp .FRem .F64` over `.float` machine values routes
    through the exact fmod (-7.5 % 2.25 = -0.75, rendered by the generic
    fixture harness). -/
def fremDispatchState : MachineState :=
  stateWith
    [(v0, .float (mkDyadic true 8444249301319680 (-50))),
     (v1, .float (mkDyadic false 5066549580791808 (-51)))]
    2

theorem frem_stepinst_dispatch_stable :
    stepInstStableOutcome (.BinOp .FRem .F64 v0 v1) fremDispatchState =
      "ok:value:float:-0.750000" := by
  native_decide

-- Assert condition typing locks. Assert requires a Bool condition on BOTH
-- engines: the interpreter type-errors on non-bool (interpret.rs Inst::Assert)
-- and validation requires Bool (validate.rs check_predicate_is_bool). The Lean
-- semantics formerly accepted integer conditions ("nonzero passes"); these
-- fixtures lock the reconciled reject-non-bool behavior. Rust-side twins:
-- numerics_policy.rs assert_* tests.

def assertBoolTrueState : MachineState := stateWith [(v0, .bool true)] 1
theorem assert_bool_true_passes_stable :
    stepInstStableOutcome (.Assert v0 .Unspecified none) assertBoolTrueState =
      "ok:value:none" := by
  native_decide

def assertBoolFalseState : MachineState := stateWith [(v0, .bool false)] 1
theorem assert_bool_false_panics_stable :
    stepInstStableOutcome (.Assert v0 .Unspecified none) assertBoolFalseState =
      "error:panic" := by
  native_decide

/-- A NONZERO integer condition is a type error, not a pass: Assert does no
    truthiness coercion. This fixture FAILS under the former int-accepting
    Lean semantics, locking the interpreter alignment. -/
def assertIntOneState : MachineState := stateWith [(v0, .int 32 1)] 1
theorem assert_int_condition_type_error_stable :
    stepInstStableOutcome (.Assert v0 .Unspecified none) assertIntOneState =
      "error:type_error" := by
  native_decide

def assertIntZeroState : MachineState := stateWith [(v0, .int 32 0)] 1
theorem assert_int_zero_condition_type_error_stable :
    stepInstStableOutcome (.Assert v0 .Unspecified none) assertIntZeroState =
      "error:type_error" := by
  native_decide

-- Plan item P (wire v52): a failed assert's panic names its kind, with the
-- operands its message prints read ONLY on failure. Rust-side twins:
-- `interpret.rs` `assert_panic_kind_tests` (the same messages, byte for byte).

/-- The panic message a single instruction raises, or its stable outcome. -/
def stepInstPanicMessage (inst : Inst) (state : MachineState) : String :=
  match Sem.run (stepInst inst) state with
  | .error (.panic msg _) => "panic:" ++ msg
  | _ => "not-a-panic:" ++ stepInstStableOutcome inst state

def assertKindState : MachineState :=
  stateWith [(v0, .bool false), (v1, .int 64 7), (v2, .int 64 3)] 3

theorem assert_unspecified_message_stable :
    stepInstPanicMessage (.Assert v0 .Unspecified none) assertKindState =
      "panic:assertion failed" := by
  native_decide

theorem assert_overflow_add_message_stable :
    stepInstPanicMessage (.Assert v0 (.Overflow .Add) none) assertKindState =
      "panic:attempt to add with overflow" := by
  native_decide

theorem assert_overflow_neg_message_stable :
    stepInstPanicMessage (.Assert v0 (.Overflow .Neg) none) assertKindState =
      "panic:attempt to negate with overflow" := by
  native_decide

theorem assert_div_by_zero_message_stable :
    stepInstPanicMessage (.Assert v0 .DivByZero none) assertKindState =
      "panic:attempt to divide by zero" := by
  native_decide

theorem assert_rem_by_zero_message_stable :
    stepInstPanicMessage (.Assert v0 .RemByZero none) assertKindState =
      "panic:attempt to calculate the remainder with a divisor of zero" := by
  native_decide

theorem assert_null_ptr_message_stable :
    stepInstPanicMessage (.Assert v0 .NullPtr none) assertKindState =
      "panic:null pointer dereference occurred" := by
  native_decide

theorem assert_bounds_check_message_stable :
    stepInstPanicMessage (.Assert v0 (.BoundsCheck v1 v2) none) assertKindState =
      "panic:index out of bounds: the len is 3 but the index is 7" := by
  native_decide

def assertMisalignedState : MachineState :=
  stateWith [(v0, .bool false), (v1, .int 64 8), (v2, .int 64 4097)] 3

theorem assert_misaligned_ptr_message_stable :
    stepInstPanicMessage (.Assert v0 (.MisalignedPtr v1 v2) none) assertMisalignedState =
      "panic:misaligned pointer dereference: address must be a multiple of 0x8 but is 0x1001" := by
  native_decide

/-- A negative two's-complement operand prints as its UNSIGNED value. -/
def assertNegativeIndexState : MachineState :=
  stateWith [(v0, .bool false), (v1, .int 8 (-1)), (v2, .int 8 3)] 3

theorem assert_bounds_check_unsigned_operand_stable :
    stepInstPanicMessage (.Assert v0 (.BoundsCheck v1 v2) none) assertNegativeIndexState =
      "panic:index out of bounds: the len is 3 but the index is 255" := by
  native_decide

/-- The operands are read only on FAILURE: a passing check never inspects a
    poison operand (the negative twin below inspects it and is UB). -/
def assertPassPoisonState : MachineState :=
  stateWith [(v0, .bool true), (v1, .undef .U64), (v2, .int 64 3)] 3

theorem assert_pass_ignores_kind_operands_stable :
    stepInstStableOutcome (.Assert v0 (.BoundsCheck v1 v2) none) assertPassPoisonState =
      "ok:value:none" := by
  native_decide

def assertFailPoisonState : MachineState :=
  stateWith [(v0, .bool false), (v1, .undef .U64), (v2, .int 64 3)] 3

theorem assert_fail_poison_kind_operand_is_ub_stable :
    stepInstStableOutcome (.Assert v0 (.BoundsCheck v1 v2) none) assertFailPoisonState =
      "error:ub" := by
  native_decide

def assertFailBoolOperandState : MachineState :=
  stateWith [(v0, .bool false), (v1, .bool true), (v2, .int 64 3)] 3

theorem assert_fail_non_int_kind_operand_type_error_stable :
    stepInstStableOutcome (.Assert v0 (.BoundsCheck v1 v2) none) assertFailBoolOperandState =
      "error:type_error" := by
  native_decide

-- Amendment P (wire v54): a failed SITED check is the terminal panic
-- (kind, operand values, entry, resolved location); the entry is never
-- executed. Rust-side twins: `interpret.rs` `panic_site_tests`.

/-- Stable rendering of a resolved panic site. -/
def stablePanicSite : Option PanicOutcomeSite → String
  | none => "unsited"
  | some site =>
    let loc := match site.loc with
      | .global g offset => s!"global:{g.index}+{offset}"
      | .other => "other"
    s!"entry:{site.entry.index}@{loc}"

/-- The panic (message and site) a straight-line instruction list raises,
    or its stable outcome. -/
def stepInstListPanicSite (insts : List Inst) (state : MachineState) : String :=
  match Sem.run
      (insts.foldlM (fun _ inst => stepInst inst) (InstrResult.value none))
      state with
  | .error (.panic msg site) => "panic:" ++ msg ++ ";" ++ stablePanicSite site
  | _ => "not-a-panic:" ++ stepInstListStableOutcome insts state

def g0 : GlobalId := ⟨0⟩

/-- A `global` location resolves to `global g + 0` without materializing the
    global (no `GlobalAddr`: the global table is not even consulted). -/
theorem assert_site_static_location_stable :
    stepInstListPanicSite [.Assert v0 (.BoundsCheck v1 v2) (some ⟨f0, .global g0⟩)]
      assertKindState =
      "panic:index out of bounds: the len is 3 but the index is 7;entry:0@global:0+0" := by
  native_decide

/-- A run-time location (`#[track_caller]` forwarding) that addresses a
    materialized global resolves to that global at its byte offset. -/
def siteFailState : MachineState := stateWith [(v0, .bool false)] 1

theorem assert_site_value_location_global_stable :
    stepInstListPanicSite
      [.GlobalAddr g0, .Assert v0 .NullPtr (some ⟨f1, .value v1⟩)] siteFailState =
      "panic:null pointer dereference occurred;entry:1@global:0+0" := by
  native_decide

/-- A live pointer outside every global (a stack slot) is `other`. -/
theorem assert_site_value_location_other_stable :
    stepInstListPanicSite
      [.Alloca .U64 none none, .Assert v0 .NullPtr (some ⟨f1, .value v1⟩)] siteFailState =
      "panic:null pointer dereference occurred;entry:1@other" := by
  native_decide

/-- A null location on a FAILING check is UB, not a panic. -/
def siteNullState : MachineState := stateWith [(v0, .bool false), (v1, .nullPtr)] 2

theorem assert_site_null_location_ub_stable :
    stepInstStableOutcome (.Assert v0 .NullPtr (some ⟨f1, .value v1⟩)) siteNullState =
      "error:ub" := by
  native_decide

/-- A PASSING check reads neither its operands nor its location: a poison
    location is never inspected. -/
def sitePassPoisonState : MachineState :=
  stateWith [(v0, .bool true), (v1, .undef .Ptr)] 2

theorem assert_site_passing_poison_location_stable :
    stepInstStableOutcome (.Assert v0 .NullPtr (some ⟨f1, .value v1⟩)) sitePassPoisonState =
      "ok:value:none" := by
  native_decide

/-- A location-only entry on an `Unspecified` check (MIR's coroutine-resume
    kinds): the site is reported with the historical message. -/
theorem assert_site_unkinded_location_only_stable :
    stepInstListPanicSite [.Assert v0 .Unspecified (some ⟨f1, .global g0⟩)] siteFailState =
      "panic:assertion failed;entry:1@global:0+0" := by
  native_decide

/-- `AssertInvoke`: a passing check takes its normal edge with its arguments. -/
def assertInvokeState (cond : Bool) : MachineState :=
  stateWith [(v0, .bool cond), (v1, .int 64 42)] 2

theorem assert_invoke_normal_edge_stable :
    stepInstStableOutcome
      (.AssertInvoke v0 .DivByZero ⟨f1, .global g0⟩ (BlockId.mk 1) [v1] (BlockId.mk 2))
      (assertInvokeState true) =
      "ok:terminator:continue:1:[int64:42]" := by
  native_decide

/-- A failing `AssertInvoke` is the sited panic; its unwind edge is never
    taken (panic=abort). -/
theorem assert_invoke_fail_panics_with_site_stable :
    stepInstListPanicSite
      [.AssertInvoke v0 .DivByZero ⟨f1, .global g0⟩ (BlockId.mk 1) [v1] (BlockId.mk 2)]
      (assertInvokeState false) =
      "panic:attempt to divide by zero;entry:1@global:0+0" := by
  native_decide

def sextState : MachineState :=
  stateWith [(v0, .int 8 255)] 1

theorem sext_i8_to_i32_stable :
    stepInstStableOutcome (.Cast .SExt .I8 .I32 v0) sextState =
      "ok:value:int32:4294967295" := by
  native_decide

def boolResizeState : MachineState :=
  stateWith [(v0, .bool true)] 1

theorem zext_bool_to_i64_stable :
    stepInstStableOutcome (.Cast .ZExt .Bool .I64 v0) boolResizeState =
      "ok:value:int64:1" := by
  native_decide

theorem sext_bool_to_i8_stable :
    stepInstStableOutcome (.Cast .SExt .Bool .I8 v0) boolResizeState =
      "ok:value:int8:255" := by
  native_decide

def truncToBoolState : MachineState :=
  stateWith [(v0, .int 8 3)] 1

theorem trunc_i8_to_bool_stable :
    stepInstStableOutcome (.Cast .Trunc .I8 .Bool v0) truncToBoolState =
      "ok:value:bool:true" := by
  native_decide

-- Transmute (scalar-only partial) executable regressions.
def transmuteIntState : MachineState :=
  stateWith [(v0, .int 64 42)] 1

theorem transmute_i64_identity_stable :
    stepInstStableOutcome (.Cast .Transmute .I64 .I64 v0) transmuteIntState =
      "ok:value:int64:42" := by
  native_decide

theorem transmute_i64_to_ptr_stable :
    stepInstStableOutcome (.Cast .Transmute .I64 .Ptr v0) transmuteIntState =
      "ok:value:ptr:42" := by
  native_decide

/-- `transmute i32 -> u32` reinterprets in place (the reference interpreter's
    `transmute_executes_on_the_integer_pointer_scalar_set` positive). -/
theorem transmute_i32_to_u32_stable :
    stepInstStableOutcome (.Cast .Transmute .I32 .U32 v0)
      (stateWith [(v0, .int 32 7)] 1) = "ok:value:int32:7" := by
  native_decide

/-- A pointer stays a POINTER through `transmute ptr -> ptr`: re-tagging it
    as an integer would disagree with the reference interpreter, which
    transports the pointer. -/
theorem transmute_ptr_to_ptr_stable :
    stepInstStableOutcome (.Cast .Transmute .Ptr .Ptr v0)
      (stateWith [(v0, .ptr 4096 none)] 1) = "ok:value:ptr:4096" := by
  native_decide

/-- The same rule for `Bitcast ptr -> ptr` (WS2.9 review): before it the
    Bitcast arm re-tagged a pointer operand as `.int 64 4096` even at a `Ptr`
    destination — an integer-shaped value at a pointer type, the mirror image
    of the float-destination mistranslation the Transmute arm fixed. The
    reference interpreter transports the pointer (`eval_bitcast`, src == dst). -/
theorem bitcast_ptr_to_ptr_stays_a_pointer_stable :
    stepInstStableOutcome (.Cast .Bitcast .Ptr .Ptr v0)
      (stateWith [(v0, .ptr 4096 none)] 1) = "ok:value:ptr:4096" := by
  native_decide

/-- Mutation control: a pointer bitcast to an INTEGER destination still
    yields the address as an integer. -/
theorem bitcast_ptr_to_u64_is_the_address_stable :
    stepInstStableOutcome (.Cast .Bitcast .Ptr .U64 v0)
      (stateWith [(v0, .ptr 4096 none)] 1) = "ok:value:int64:4096" := by
  native_decide

/-- The pointer rule covers the WHOLE pointer-like set the reference
    interpreter transports through (`is_pointer_like_ty`: `Ptr`, `PtrConst`,
    `PtrMut`, `Ref`, `RefMut`, `Rc`), not `Ptr` alone: a `*const u8`
    destination keeps the pointer too. -/
theorem bitcast_ptr_to_ptr_const_stays_a_pointer_stable :
    stepInstStableOutcome (.Cast .Bitcast .Ptr (.PtrConst .U8) v0)
      (stateWith [(v0, .ptr 4096 none)] 1) = "ok:value:ptr:4096" := by
  native_decide

/-- And on the integer side: `Bitcast u64 -> &mut u8` binds a POINTER at the
    address, exactly as `eval_bitcast` re-resolves an integer for a
    pointer-like destination (before the review it bound `.int 64 4096`). -/
theorem bitcast_u64_to_ref_mut_is_a_pointer_stable :
    stepInstStableOutcome (.Cast .Bitcast .U64 (.RefMut .U8) v0)
      (stateWith [(v0, .int 64 4096)] 1) = "ok:value:ptr:4096" := by
  native_decide

def transmuteFloatState : MachineState :=
  stateWith [(v0, .float 1.5)] 1

/-- Subset v3 (WS2.9): a float SOURCE is refused by the two-sided scalar gate
    — `unsupported.cast`, the mirror of the interpreter's `UnsupportedCast`
    (v2 fell through to the operand match and answered `vector_shape`). -/
theorem transmute_float_rejected_stable :
    stepInstStableOutcome (.Cast .Transmute .F64 .I64 v0) transmuteFloatState =
      "error:unsupported.cast" := by
  native_decide

def transmuteU32State : MachineState :=
  stateWith [(v0, .int 32 0x3fc00000)] 1

/-- The v3 mistranslation control: before WS2.9 `transmute u32 -> f32` bound
    `.int 32 v` — an INTEGER value at a float type — because the destination
    was gated only by `getTyWidth`. It is now a structured refusal; the
    sanctioned int->float reinterpret is `Bitcast` (next fixture). -/
theorem transmute_u32_to_f32_unsupported_stable :
    stepInstStableOutcome (.Cast .Transmute .U32 .F32 v0) transmuteU32State =
      "error:unsupported.cast" := by
  native_decide

/-- Twin of the control: the same bits through `Bitcast` ARE a float (1.5). -/
theorem bitcast_u32_to_f32_is_the_sanctioned_reinterpret_stable :
    stepInstStableOutcome (.Cast .Bitcast .U32 .F32 v0) transmuteU32State =
      "ok:value:float:1.500000" := by
  native_decide

/-- The bool half of the control: `transmute u8 -> bool` used to bind
    `.int 1 2`, a "bool" whose payload exceeds 1. -/
theorem transmute_u8_to_bool_unsupported_stable :
    stepInstStableOutcome (.Cast .Transmute .U8 .Bool v0)
      (stateWith [(v0, .int 8 2)] 1) = "error:unsupported.cast" := by
  native_decide

/-- Mutation control: an integer source outside the scalar set on the OTHER
    side (`i32 -> bool` via the bool source, `bool -> u8`) is refused too —
    the gate is two-sided, not destination-only. -/
theorem transmute_bool_source_unsupported_stable :
    stepInstStableOutcome (.Cast .Transmute .Bool .U8 v0)
      (stateWith [(v0, .bool true)] 1) = "error:unsupported.cast" := by
  native_decide

/-- Review (WS2.9): an off-set IDENTITY transmute (`bool -> bool`,
    `f64 -> f64`) is refused too — the gate is on the types, not on whether
    a reinterpretation would change anything, so a same-type shortcut
    (`eval_bitcast`'s `src == dst` transport) never runs for a type the
    scalar set excludes. Both engines answer the same code. -/
theorem transmute_bool_identity_unsupported_stable :
    stepInstStableOutcome (.Cast .Transmute .Bool .Bool v0)
      (stateWith [(v0, .bool true)] 1) = "error:unsupported.cast" := by
  native_decide

theorem transmute_f64_identity_unsupported_stable :
    stepInstStableOutcome (.Cast .Transmute .F64 .F64 v0) transmuteFloatState =
      "error:unsupported.cast" := by
  native_decide

-- ReifyFnPointer (fn-item-preserving partial) executable regressions.
def reifyFnState : MachineState :=
  stateWith [(v0, .closure (FuncId.mk 7) [])] 1

theorem reify_fn_pointer_identity_stable :
    stepInstStableOutcome (.Cast .ReifyFnPointer .I64 .Ptr v0) reifyFnState =
      "ok:value:closure:7:0" := by
  native_decide

theorem reify_fn_pointer_rejected_stable :
    stepInstStableOutcome (.Cast .ReifyFnPointer .I64 .Ptr v0) transmuteIntState =
      "error:type_error" := by
  native_decide

-- Saturating float→int cast locks (FPToSISat / FPToUISat — Rust `f as iN`/
-- `uN`, LLVM fptosi.sat / fptoui.sat; docs/ub-numerics-policy.md §2).
-- Expected values are the reference interpreter's outputs over the SAME
-- inputs (interpret.rs `CastOp::FPToUISat | CastOp::FPToSISat`, executed via
-- `Interpreter::execute_func`, 2026-07-10). Operands are in exact dyadic form
-- (`mkDyadic`) so no decimal parsing or Float printing is in the trust path.
-- Unlike the raw FPToSI/FPToUI (NaN/out-of-range = UB), the saturating twins
-- are TOTAL: NaN → 0, out-of-range clamps to MIN/MAX, in-range truncates
-- toward zero. Coverage per op, at two widths each: NaN, +inf, -inf,
-- in-range, above-max, below-min, negative→unsigned, and the asymmetric
-- signed boundary (`2^(w-1)` saturates but `-2^(w-1)` is in-range).

def nanF : Float := (0.0 : Float) / 0.0

def satCastState (v : Float) : MachineState := stateWith [(v0, .float v)] 1

def fpToSISatOutcome (dst : Ty) (v : Float) : String :=
  stepInstStableOutcome (.Cast .FPToSISat .F64 dst v0) (satCastState v)

def fpToUISatOutcome (dst : Ty) (v : Float) : String :=
  stepInstStableOutcome (.Cast .FPToUISat .F64 dst v0) (satCastState v)

-- FPToSISat → i8 (values are the canonical unsigned two's-complement raw).

/-- NaN → 0 (not UB — contrast fptosi). -/
theorem fptosisat_i8_nan_to_zero_stable :
    fpToSISatOutcome .I8 nanF = "ok:value:int8:0" := by
  native_decide

/-- +inf saturates to i8::MAX = 127. -/
theorem fptosisat_i8_pos_inf_saturates_max_stable :
    fpToSISatOutcome .I8 infF = "ok:value:int8:127" := by
  native_decide

/-- -inf saturates to i8::MIN = -128 (raw 128). -/
theorem fptosisat_i8_neg_inf_saturates_min_stable :
    fpToSISatOutcome .I8 (-infF) = "ok:value:int8:128" := by
  native_decide

/-- -5.75 truncates toward zero to -5 (raw 251), NOT -6. -/
theorem fptosisat_i8_in_range_truncates_toward_zero_stable :
    fpToSISatOutcome .I8 (mkDyadic true 23 (-2)) = "ok:value:int8:251" := by
  native_decide

/-- 300.0 (above max) saturates to 127. -/
theorem fptosisat_i8_above_max_saturates_stable :
    fpToSISatOutcome .I8 (mkDyadic false 300 0) = "ok:value:int8:127" := by
  native_decide

/-- -200.0 (below min) saturates to -128 (raw 128). -/
theorem fptosisat_i8_below_min_saturates_stable :
    fpToSISatOutcome .I8 (mkDyadic true 200 0) = "ok:value:int8:128" := by
  native_decide

/-- 127.5 is in range (< 2^7) and truncates to 127. -/
theorem fptosisat_i8_just_below_max_truncates_stable :
    fpToSISatOutcome .I8 (mkDyadic false 255 (-1)) = "ok:value:int8:127" := by
  native_decide

/-- 128.0 = 2^7 is NOT representable: saturates to 127. -/
theorem fptosisat_i8_at_hi_boundary_saturates_stable :
    fpToSISatOutcome .I8 (mkDyadic false 128 0) = "ok:value:int8:127" := by
  native_decide

/-- -128.0 = -2^7 IS representable: in-range, raw 128. -/
theorem fptosisat_i8_at_lo_boundary_in_range_stable :
    fpToSISatOutcome .I8 (mkDyadic true 128 0) = "ok:value:int8:128" := by
  native_decide

/-- -128.5 is below min: saturates to -128 (raw 128). -/
theorem fptosisat_i8_just_below_lo_saturates_stable :
    fpToSISatOutcome .I8 (mkDyadic true 257 (-1)) = "ok:value:int8:128" := by
  native_decide

-- FPToSISat → i32.

theorem fptosisat_i32_nan_to_zero_stable :
    fpToSISatOutcome .I32 nanF = "ok:value:int32:0" := by
  native_decide

theorem fptosisat_i32_pos_inf_saturates_max_stable :
    fpToSISatOutcome .I32 infF = "ok:value:int32:2147483647" := by
  native_decide

theorem fptosisat_i32_neg_inf_saturates_min_stable :
    fpToSISatOutcome .I32 (-infF) = "ok:value:int32:2147483648" := by
  native_decide

/-- -123456.75 truncates toward zero to -123456 (raw 4294843840). -/
theorem fptosisat_i32_in_range_truncates_toward_zero_stable :
    fpToSISatOutcome .I32 (mkDyadic true 493827 (-2)) =
      "ok:value:int32:4294843840" := by
  native_decide

/-- 3e9 (above i32::MAX) saturates to 2147483647. -/
theorem fptosisat_i32_above_max_saturates_stable :
    fpToSISatOutcome .I32 (mkDyadic false 3000000000 0) =
      "ok:value:int32:2147483647" := by
  native_decide

/-- -3e9 (below i32::MIN) saturates to -2^31 (raw 2147483648). -/
theorem fptosisat_i32_below_min_saturates_stable :
    fpToSISatOutcome .I32 (mkDyadic true 3000000000 0) =
      "ok:value:int32:2147483648" := by
  native_decide

-- FPToUISat → u8.

/-- NaN → 0 (not UB — contrast fptoui). -/
theorem fptouisat_u8_nan_to_zero_stable :
    fpToUISatOutcome .U8 nanF = "ok:value:int8:0" := by
  native_decide

/-- +inf saturates to u8::MAX = 255. -/
theorem fptouisat_u8_pos_inf_saturates_max_stable :
    fpToUISatOutcome .U8 infF = "ok:value:int8:255" := by
  native_decide

/-- -inf saturates to 0. -/
theorem fptouisat_u8_neg_inf_saturates_zero_stable :
    fpToUISatOutcome .U8 (-infF) = "ok:value:int8:0" := by
  native_decide

/-- 200.25 truncates toward zero to 200. -/
theorem fptouisat_u8_in_range_truncates_stable :
    fpToUISatOutcome .U8 (mkDyadic false 801 (-2)) = "ok:value:int8:200" := by
  native_decide

/-- 300.0 (above max) saturates to 255. -/
theorem fptouisat_u8_above_max_saturates_stable :
    fpToUISatOutcome .U8 (mkDyadic false 300 0) = "ok:value:int8:255" := by
  native_decide

/-- -3.5 (negative → unsigned) saturates to 0, does NOT two's-complement
    wrap. -/
theorem fptouisat_u8_negative_saturates_zero_stable :
    fpToUISatOutcome .U8 (mkDyadic true 7 (-1)) = "ok:value:int8:0" := by
  native_decide

/-- -0.0 is in range (not < 0.0) and truncates to 0. -/
theorem fptouisat_u8_negative_zero_in_range_stable :
    fpToUISatOutcome .U8 (mkDyadic true 0 0) = "ok:value:int8:0" := by
  native_decide

-- FPToUISat → u32.

theorem fptouisat_u32_nan_to_zero_stable :
    fpToUISatOutcome .U32 nanF = "ok:value:int32:0" := by
  native_decide

theorem fptouisat_u32_pos_inf_saturates_max_stable :
    fpToUISatOutcome .U32 infF = "ok:value:int32:4294967295" := by
  native_decide

theorem fptouisat_u32_neg_inf_saturates_zero_stable :
    fpToUISatOutcome .U32 (-infF) = "ok:value:int32:0" := by
  native_decide

/-- 4000000000.5 (above i32::MAX, within u32) truncates to 4000000000. -/
theorem fptouisat_u32_in_range_truncates_stable :
    fpToUISatOutcome .U32 (mkDyadic false 8000000001 (-1)) =
      "ok:value:int32:4000000000" := by
  native_decide

/-- 5e9 (above u32::MAX) saturates to 4294967295. -/
theorem fptouisat_u32_above_max_saturates_stable :
    fpToUISatOutcome .U32 (mkDyadic false 5000000000 0) =
      "ok:value:int32:4294967295" := by
  native_decide

/-- -1e9 (negative → unsigned) saturates to 0. -/
theorem fptouisat_u32_negative_saturates_zero_stable :
    fpToUISatOutcome .U32 (mkDyadic true 1000000000 0) =
      "ok:value:int32:0" := by
  native_decide

-- RAW float→int cast in-range locks (FPToSI / FPToUI — NaN/out-of-range is
-- UB per docs/ub-numerics-policy.md §2, so ONLY defined in-range inputs are
-- fixtured here; the UB envelope itself is untouched). These lock the exact
-- frExp in-range truncation against the reference interpreter (interpret.rs
-- `CastOp::FPToUI | CastOp::FPToSI`, `float_to_u128`/`float_to_i128` +
-- width mask). Expected values are the interpreter's outputs over the SAME
-- inputs (executed via `Interpreter::execute_func`, 2026-07-10). The
-- NEGATIVE in-range signed cases are the B3 depth-ledger divergence: the
-- former axiomatized `toUInt64` path yielded raw 0 for them, where the
-- interpreter produces the two's-complement encoding. Negative inputs to
-- FPToUI are UB (not fixtured) — except -0.0, which is NOT < 0.0 and hence
-- in-range, truncating to 0.

def fpToSIOutcome (dst : Ty) (v : Float) : String :=
  stepInstStableOutcome (.Cast .FPToSI .F64 dst v0) (satCastState v)

def fpToUIOutcome (dst : Ty) (v : Float) : String :=
  stepInstStableOutcome (.Cast .FPToUI .F64 dst v0) (satCastState v)

-- Raw FPToSI → i8.

/-- -5.75 truncates toward zero to -5 (raw 251) — the ledger's divergence
    case: the old `toUInt64` path yielded raw 0. -/
theorem fptosi_i8_negative_in_range_twos_complement_stable :
    fpToSIOutcome .I8 (mkDyadic true 23 (-2)) = "ok:value:int8:251" := by
  native_decide

/-- -128.0 = -2^7 = i8::MIN is IN-RANGE for the raw cast (the UB bound is
    strict: v < -2^7), raw 128 — the largest-magnitude in-range negative. -/
theorem fptosi_i8_min_boundary_in_range_stable :
    fpToSIOutcome .I8 (mkDyadic true 128 0) = "ok:value:int8:128" := by
  native_decide

/-- -127.75 truncates toward zero to -127 (raw 129), NOT -128. -/
theorem fptosi_i8_negative_truncates_toward_zero_stable :
    fpToSIOutcome .I8 (mkDyadic true 511 (-2)) = "ok:value:int8:129" := by
  native_decide

/-- 100.5 (positive in-range) truncates to 100. -/
theorem fptosi_i8_positive_in_range_stable :
    fpToSIOutcome .I8 (mkDyadic false 201 (-1)) = "ok:value:int8:100" := by
  native_decide

-- Raw FPToSI → i32.

/-- -5.0 as i32 is raw 4294967291 (two's complement), NOT 0. -/
theorem fptosi_i32_negative_in_range_twos_complement_stable :
    fpToSIOutcome .I32 (mkDyadic true 5 0) = "ok:value:int32:4294967291" := by
  native_decide

/-- -2147483648.0 = -2^31 = i32::MIN is in-range (strict UB bound), raw
    2147483648 — the largest-magnitude in-range negative. -/
theorem fptosi_i32_min_boundary_in_range_stable :
    fpToSIOutcome .I32 (mkDyadic true 2147483648 0) =
      "ok:value:int32:2147483648" := by
  native_decide

/-- -2147483647.75 truncates toward zero to -2147483647 (raw 2147483649). -/
theorem fptosi_i32_negative_truncates_toward_zero_stable :
    fpToSIOutcome .I32 (mkDyadic true 8589934591 (-2)) =
      "ok:value:int32:2147483649" := by
  native_decide

/-- 2147483647.0 = i32::MAX exactly is in-range (UB bound is v ≥ 2^31). -/
theorem fptosi_i32_max_in_range_stable :
    fpToSIOutcome .I32 (mkDyadic false 2147483647 0) =
      "ok:value:int32:2147483647" := by
  native_decide

/-- 123456.75 (positive in-range) truncates to 123456. -/
theorem fptosi_i32_positive_in_range_stable :
    fpToSIOutcome .I32 (mkDyadic false 493827 (-2)) =
      "ok:value:int32:123456" := by
  native_decide

-- Raw FPToUI → u8. (Negative inputs are UB — no fixtures — except -0.0.)

/-- 200.25 truncates toward zero to 200. -/
theorem fptoui_u8_in_range_truncates_stable :
    fpToUIOutcome .U8 (mkDyadic false 801 (-2)) = "ok:value:int8:200" := by
  native_decide

/-- 255.75 (just below the 2^8 UB bound) truncates to 255. -/
theorem fptoui_u8_just_below_hi_in_range_stable :
    fpToUIOutcome .U8 (mkDyadic false 1023 (-2)) = "ok:value:int8:255" := by
  native_decide

/-- -0.0 is in range (not < 0.0) and truncates to 0 — the only
    negative-signed input the raw unsigned cast defines. -/
theorem fptoui_u8_negative_zero_in_range_stable :
    fpToUIOutcome .U8 (mkDyadic true 0 0) = "ok:value:int8:0" := by
  native_decide

-- Raw FPToUI → u32.

/-- 4000000000.5 (above i32::MAX, within u32) truncates to 4000000000. -/
theorem fptoui_u32_in_range_truncates_stable :
    fpToUIOutcome .U32 (mkDyadic false 8000000001 (-1)) =
      "ok:value:int32:4000000000" := by
  native_decide

/-- 4294967295.5 (just below the 2^32 UB bound) truncates to u32::MAX. -/
theorem fptoui_u32_just_below_hi_in_range_stable :
    fpToUIOutcome .U32 (mkDyadic false 8589934591 (-1)) =
      "ok:value:int32:4294967295" := by
  native_decide

-- GlobalAddr (cached, aliasing-faithful) executable regressions.
-- Empty memory reserves the null page below 1024, so the first reserved global
-- byte is at address 1024.

-- A single address-of yields a pointer at the reserved base.
theorem global_addr_single_stable :
    stepInstStableOutcome (.GlobalAddr (GlobalId.mk 0)) MachineState.empty =
      "ok:value:ptr:1024" := by
  native_decide

-- ALIASING: a second address-of the SAME global returns the cached pointer
-- (same address), not a fresh one.
theorem global_addr_same_aliases_stable :
    stepTwoInstStableOutcome
      (.GlobalAddr (GlobalId.mk 0)) (.GlobalAddr (GlobalId.mk 0)) MachineState.empty =
      "ok:value:ptr:1024" := by
  native_decide

-- DISTINCTNESS / collision-freedom: a DIFFERENT global gets a DIFFERENT address
-- (1040: the size-1 reservation advanced the allocator past 1024, and a global
-- is placed at `globalSectionAlign`, 16, as in the interpreter's
-- `global_pointer`).
theorem global_addr_distinct_addrs_stable :
    stepTwoInstStableOutcome
      (.GlobalAddr (GlobalId.mk 0)) (.GlobalAddr (GlobalId.mk 1)) MachineState.empty =
      "ok:value:ptr:1040" := by
  native_decide

def vectorSelectState : MachineState :=
  stateWith
    [(v0, .vector [.bool true, .bool false, .bool true, .bool false]),
     (v1, v4i32 1 2 3 4),
     (v2, v4i32 10 20 30 40)]
    3

theorem vector_select_stable :
    stepInstStableOutcome (.Select (.Vector 4 .I32) v0 v1 v2)
        vectorSelectState =
      "ok:value:vector[int32:1,int32:20,int32:3,int32:40]" := by
  native_decide

def vectorI8CompareState : MachineState :=
  stateWith
    [(v0, v16i8 [0, 1, 2, 3, 4, 5, 6, 7,
                 8, 9, 10, 11, 12, 13, 14, 15]),
     (v1, v16i8 [0, 2, 2, 4, 4, 6, 6, 8,
                 8, 10, 10, 12, 12, 14, 14, 0])]
    2

theorem vector_icmp_eq_v16i8_lane_order_stable :
    stepInstStableOutcome (.ICmp .Eq (.Vector 16 .I8) v0 v1)
        vectorI8CompareState =
      "ok:value:vector[bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false]" := by
  native_decide

theorem vector_icmp_ne_v16i8_lane_order_stable :
    stepInstStableOutcome (.ICmp .Ne (.Vector 16 .I8) v0 v1)
        vectorI8CompareState =
      "ok:value:vector[bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true]" := by
  native_decide

def vectorI16CompareState : MachineState :=
  stateWith
    [(v0, v8i16 [0, 1, 2, 3, 4, 5, 32768, 65535]),
     (v1, v8i16 [0, 2, 2, 4, 4, 6, 32768, 0])]
    2

theorem vector_icmp_eq_v8i16_lane_order_stable :
    stepInstStableOutcome (.ICmp .Eq (.Vector 8 .I16) v0 v1)
        vectorI16CompareState =
      "ok:value:vector[bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false]" := by
  native_decide

theorem vector_icmp_ne_v8i16_lane_order_stable :
    stepInstStableOutcome (.ICmp .Ne (.Vector 8 .I16) v0 v1)
        vectorI16CompareState =
      "ok:value:vector[bool:false,bool:true,bool:false,bool:true,bool:false,bool:true,bool:false,bool:true]" := by
  native_decide

def vectorI8SelectFromSignedCmpState : MachineState :=
  stateWith
    [(v0, v16i8 [255, 0, 1, 127, 128, 5, 250, 42,
                 100, 200, 15, 16, 17, 18, 19, 20]),
     (v1, v16i8 [1, 0, 2, 126, 127, 6, 251, 40,
                 99, 199, 15, 10, 18, 17, 21, 20]),
     (v2, v16i8 [10, 11, 12, 13, 14, 15, 16, 17,
                 18, 19, 20, 21, 22, 23, 24, 25])]
    3

theorem vector_select_v16i8_from_signed_icmp_stable :
    stepTwoInstStableOutcome
        (.ICmp .Slt (.Vector 16 .I8) v0 v1)
        (.Select (.Vector 16 .I8) v3 v0 v2)
        vectorI8SelectFromSignedCmpState =
      "ok:value:vector[int8:255,int8:11,int8:1,int8:13,int8:128,int8:5,int8:250,int8:17,int8:18,int8:19,int8:20,int8:21,int8:17,int8:23,int8:19,int8:25]" := by
  native_decide

def vectorI16SelectFromSignedCmpState : MachineState :=
  stateWith
    [(v0, v8i16 [65535, 0, 32767, 32768, 100, 40000, 7, 8]),
     (v1, v8i16 [1, 0, 32766, 32767, 101, 39999, 6, 9]),
     (v2, v8i16 [30, 31, 32, 33, 34, 35, 36, 37])]
    3

theorem vector_select_v8i16_from_signed_icmp_stable :
    stepTwoInstStableOutcome
        (.ICmp .Slt (.Vector 8 .I16) v0 v1)
        (.Select (.Vector 8 .I16) v3 v0 v2)
        vectorI16SelectFromSignedCmpState =
      "ok:value:vector[int16:65535,int16:31,int16:32,int16:32768,int16:100,int16:35,int16:36,int16:8]" := by
  native_decide

theorem v8i8_icmp_rejects_wrong_lane_census_stable :
    stepInstStableOutcome (.ICmp .Eq (.Vector 8 .I8) v0 v1)
        vectorI8CompareState =
      "error:type_error" := by
  native_decide

theorem vector_select_v16i8_rejects_v8bool_mask_stable :
    stepInstStableOutcome (.Select (.Vector 16 .I8) v0 v1 v2)
        (stateWith
          [(v0, boolVector [true, false, true, false, true, false, true, false]),
           (v1, v16i8 [0, 1, 2, 3, 4, 5, 6, 7,
                       8, 9, 10, 11, 12, 13, 14, 15]),
           (v2, v16i8 [15, 14, 13, 12, 11, 10, 9, 8,
                       7, 6, 5, 4, 3, 2, 1, 0])]
          3) =
      "error:type_error" := by
  native_decide

theorem vector_select_v16i8_rejects_i16_payload_stable :
    stepInstStableOutcome (.Select (.Vector 16 .I8) v0 v1 v2)
        (stateWith
          [(v0, boolVector [true, true, true, true, true, true, true, true,
                            true, true, true, true, true, true, true, true]),
           (v1, intVector 16 [0, 1, 2, 3, 4, 5, 6, 7,
                              8, 9, 10, 11, 12, 13, 14, 15]),
           (v2, intVector 16 [15, 14, 13, 12, 11, 10, 9, 8,
                              7, 6, 5, 4, 3, 2, 1, 0])]
          3) =
      "error:type_error" := by
  native_decide

def vectorElementI32State : MachineState :=
  stateWith [(v0, v4i32 11 (-22) 33 (-44)),
             (v1, .int 64 2),
             (v2, .int 32 99)]
    3

theorem vector_extract_v4i32_declared_lane_stable :
    stepInstStableOutcome (.ExtractElement .I32 v0 v1)
        vectorElementI32State =
      "ok:value:int32:33" := by
  native_decide

theorem vector_insert_v4i32_declared_vector_stable :
    stepInstStableOutcome (.InsertElement (.Vector 4 .I32) v0 v1 v2)
        vectorElementI32State =
      "ok:value:vector[int32:11,int32:-22,int32:99,int32:-44]" := by
  native_decide

theorem vector_insert_rejects_lane_declared_ty_stable :
    stepInstStableOutcome (.InsertElement .I32 v0 v1 v2)
        vectorElementI32State =
      -- A scalar declared result type is a type error. It is not an
      -- unsupported vector shape in the general semantic domain.
      "error:type_error" := by
  native_decide

def vectorElementI64State : MachineState :=
  stateWith [(v0, v2i64 5 (-6)), (v1, .int 64 1), (v2, .int 64 77)] 3

theorem vector_insert_v2i64_declared_vector_stable :
    stepInstStableOutcome (.InsertElement (.Vector 2 .I64) v0 v1 v2)
        vectorElementI64State =
      "ok:value:vector[int64:5,int64:77]" := by
  native_decide

def vectorElementV4BoolState : MachineState :=
  stateWith [(v0, v4bool true false true false),
             (v1, .int 64 3),
             (v2, .bool true)]
    3

theorem vector_insert_v4bool_declared_vector_stable :
    stepInstStableOutcome (.InsertElement (.Vector 4 .Bool) v0 v1 v2)
        vectorElementV4BoolState =
      "ok:value:vector[bool:true,bool:false,bool:true,bool:true]" := by
  native_decide

def vectorElementV2BoolState : MachineState :=
  stateWith [(v0, v2bool true false), (v1, .int 64 1), (v2, .bool true)] 3

theorem vector_extract_v2bool_declared_lane_stable :
    stepInstStableOutcome (.ExtractElement .Bool v0 v1)
        vectorElementV2BoolState =
      "ok:value:bool:false" := by
  native_decide

theorem vector_insert_v2bool_declared_vector_stable :
    stepInstStableOutcome (.InsertElement (.Vector 2 .Bool) v0 v1 v2)
        vectorElementV2BoolState =
      "ok:value:vector[bool:true,bool:true]" := by
  native_decide

def generalV8I32State : MachineState :=
  stateWith [(v0, v8i32), (v1, v8i32)] 2

/-- The old backend-shape refusal for this validator-admitted type is false
    after general lane execution. Keep its exact result as a positive control;
    the vector dialect's separate bounded shape policy remains unchanged. -/
theorem general_v8i32_binop_code_stable :
    stepInstStableOutcome (.BinOp .Add (.Vector 8 .I32) v0 v1)
        generalV8I32State =
      "ok:value:vector[int32:0,int32:2,int32:4,int32:6,int32:8,int32:10,int32:12,int32:14]" := by
  native_decide

def generalV8I32ElementState : MachineState :=
  stateWith [(v0, v8i32), (v1, .int 64 1), (v2, .int 32 99)] 3

theorem general_v8i32_insert_element_code_stable :
    stepInstStableOutcome (.InsertElement (.Vector 8 .I32) v0 v1 v2)
        generalV8I32ElementState =
      "ok:value:vector[int32:0,int32:99,int32:2,int32:3,int32:4,int32:5,int32:6,int32:7]" := by
  native_decide

def unsupportedDialect : DialectInst :=
  { dialect := "fixture"
    op := "opaque"
    operands := []
    resultTys := []
    attrs := []
    version := 1 }

theorem unsupported_dialect_code_stable :
    stepInstStableOutcome (.DialectOp unsupportedDialect) MachineState.empty =
      "error:unsupported.dialect_op" := by
  native_decide

def vectorDialectLaneState : MachineState :=
  stateWith
    [(v0, .int 32 1),
     (v1, .int 32 2),
     (v2, .int 32 3),
     (ValueId.mk 3, .int 32 4),
     (ValueId.mk 4, .int 64 11),
     (ValueId.mk 5, .int 64 22),
     (ValueId.mk 6, v4i32 10 20 30 40),
     (ValueId.mk 7, v2i64 100 200),
     (ValueId.mk 8, v4bool true false true true),
     (ValueId.mk 9, v2bool false true),
     (ValueId.mk 10, boolVector [true, true, true, true, true, true, true, true]),
     (ValueId.mk 11, boolVector [true, true, true, true, true, true, true, true,
                                  true, true, true, true, true, true, true, true])]
    12

def vectorDialectOutcome (inst : DialectInst) (state : MachineState) : String :=
  declaredDialectStableOutcome VectorDialect.opSem inst state

theorem vector_dialect_pack_lanes_v4i32_stable :
    vectorDialectOutcome
        (VectorDialect.packLanes (.Vector 4 .I32)
          [v0, v1, v2, ValueId.mk 3])
        vectorDialectLaneState =
      "ok:value:vector[int32:1,int32:2,int32:3,int32:4]" := by
  native_decide

theorem vector_dialect_pack_lanes_v2i64_stable :
    vectorDialectOutcome
        (VectorDialect.packLanes (.Vector 2 .I64)
          [ValueId.mk 4, ValueId.mk 5])
        vectorDialectLaneState =
      "ok:value:vector[int64:11,int64:22]" := by
  native_decide

theorem vector_dialect_extract_lane_v4i32_stable :
    vectorDialectOutcome
        (VectorDialect.extractLane (.Vector 4 .I32) .I32 (ValueId.mk 6) 2)
        vectorDialectLaneState =
      "ok:value:int32:30" := by
  native_decide

theorem vector_dialect_extract_lane_v2i64_stable :
    vectorDialectOutcome
        (VectorDialect.extractLane (.Vector 2 .I64) .I64 (ValueId.mk 7) 1)
        vectorDialectLaneState =
      "ok:value:int64:200" := by
  native_decide

theorem vector_dialect_insert_lane_v4i32_stable :
    vectorDialectOutcome
        (VectorDialect.insertLane (.Vector 4 .I32) (ValueId.mk 6) v0 1)
        vectorDialectLaneState =
      "ok:value:vector[int32:10,int32:1,int32:30,int32:40]" := by
  native_decide

theorem vector_dialect_insert_lane_v2i64_stable :
    vectorDialectOutcome
        (VectorDialect.insertLane (.Vector 2 .I64) (ValueId.mk 7) (ValueId.mk 4) 0)
        vectorDialectLaneState =
      "ok:value:vector[int64:11,int64:200]" := by
  native_decide

theorem vector_dialect_mask_to_bits_v4bool_lsb_lane0_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 4 .Bool) (ValueId.mk 8) .I32)
        vectorDialectLaneState =
      "ok:value:int32:13" := by
  native_decide

/-- The real decoder refuses the malformed F32 result spec that the generic
    lowering theorem now excludes with its integer-result-family premise. -/
theorem vector_dialect_mask_to_bits_float_result_refused_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 4 .Bool) (ValueId.mk 8) .F32)
        vectorDialectLaneState = "error:type_error" := by
  native_decide

theorem vector_dialect_mask_to_bits_v2bool_lsb_lane0_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 2 .Bool) (ValueId.mk 9) .I64)
        vectorDialectLaneState =
      "ok:value:int64:2" := by
  native_decide

theorem vector_dialect_mask_to_bits_v8bool_lsb_lane0_zero_extends_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 8 .Bool) (ValueId.mk 10) .I32)
        vectorDialectLaneState =
      "ok:value:int32:255" := by
  native_decide

theorem vector_dialect_mask_to_bits_v16bool_lsb_lane0_zero_extends_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 16 .Bool) (ValueId.mk 11) .I32)
        vectorDialectLaneState =
      "ok:value:int32:65535" := by
  native_decide

def vectorMaskOracleState : MachineState :=
  stateWith
    [(v0, boolVector [true, false, false, true, false, true, false, false,
                      true, false, false, false, false, true, false, true]),
     (v1, boolVector [true, false, true, true, false, false, false, true]),
     (v2, v4bool true false true true),
     (v3, v2bool false true)]
    4

theorem vector_mask_oracle_v16_bool_sparse_i32_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 16 .Bool) v0 .I32)
        vectorMaskOracleState =
      "ok:value:int32:41257" := by
  native_decide

theorem vector_mask_oracle_v8_bool_sparse_i32_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 8 .Bool) v1 .I32)
        vectorMaskOracleState =
      "ok:value:int32:141" := by
  native_decide

theorem vector_mask_oracle_v4_bool_existing_i32_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 4 .Bool) v2 .I32)
        vectorMaskOracleState =
      "ok:value:int32:13" := by
  native_decide

theorem vector_mask_oracle_v2_bool_existing_i64_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 2 .Bool) v3 .I64)
        vectorMaskOracleState =
      "ok:value:int64:2" := by
  native_decide

def vectorI8SltMaskOracleState : MachineState :=
  stateWith
    [(v0, v16i8 [-1, 0, 1, 127, -128, 5, -6, 42,
                 100, -56, 15, 16, 17, 18, 19, 20]),
     (v1, v16i8 [1, 0, 2, 126, 127, 6, -5, 40,
                 99, -57, 15, 10, 18, 17, 21, 20])]
    2

theorem vector_mask_oracle_compare_slt_v16_i8_i32_stable :
    stepThenDeclaredDialectStableOutcome
        (.ICmp .Slt (.Vector 16 .I8) v0 v1)
        VectorDialect.opSem
        (VectorDialect.maskToBits (.Vector 16 .Bool) v2 .I32)
        vectorI8SltMaskOracleState =
      "ok:value:int32:20597" := by
  native_decide

def vectorI16SltMaskOracleState : MachineState :=
  stateWith
    [(v0, v8i16 [-1, 0, 32767, -32768, 100, -25536, 7, 8]),
     (v1, v8i16 [1, 0, 32766, 32767, 101, -25537, 6, 9])]
    2

theorem vector_mask_oracle_compare_slt_v8_i16_i32_stable :
    stepThenDeclaredDialectStableOutcome
        (.ICmp .Slt (.Vector 8 .I16) v0 v1)
        VectorDialect.opSem
        (VectorDialect.maskToBits (.Vector 8 .Bool) v2 .I32)
        vectorI16SltMaskOracleState =
      "ok:value:int32:153" := by
  native_decide

theorem vector_dialect_mask_to_bits_v8bool_i64_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 8 .Bool) (ValueId.mk 10) .I64)
        vectorDialectLaneState =
      "error:type_error" := by
  native_decide

theorem vector_dialect_reduce_add_v4i32_stable :
    vectorDialectOutcome
        (VectorDialect.reduce (.Vector 4 .I32) .I32 (ValueId.mk 6) .add)
        vectorDialectLaneState =
      "ok:value:int32:100" := by
  native_decide

theorem vector_dialect_reduce_or_v2i64_stable :
    vectorDialectOutcome
        (VectorDialect.reduce (.Vector 2 .I64) .I64 (ValueId.mk 7) .or)
        vectorDialectLaneState =
      "ok:value:int64:236" := by
  native_decide

theorem vector_dialect_reduce_unsupported_shape_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.reduce (.Vector 8 .I32) .I32 (ValueId.mk 6) .add)
        vectorDialectLaneState =
      "error:unsupported.vector_shape" := by
  native_decide

theorem vector_dialect_reduce_unknown_kind_fails_closed_stable :
    vectorDialectOutcome
        { (VectorDialect.reduce (.Vector 4 .I32) .I32 (ValueId.mk 6) .add)
          with attrs := [VectorDialect.attr "vector_ty" (.ty (.Vector 4 .I32)),
                         VectorDialect.attr "kind" (.str "mul")] }
        vectorDialectLaneState =
      "error:unsupported.dialect_op" := by
  native_decide

theorem vector_dialect_shuffle_reverse_v4i32_stable :
    vectorDialectOutcome
        (VectorDialect.shuffle (.Vector 4 .I32) (ValueId.mk 6) [3, 2, 1, 0])
        vectorDialectLaneState =
      "ok:value:vector[int32:40,int32:30,int32:20,int32:10]" := by
  native_decide

theorem vector_dialect_shuffle_broadcast_v2i64_stable :
    vectorDialectOutcome
        (VectorDialect.shuffle (.Vector 2 .I64) (ValueId.mk 7) [1, 1])
        vectorDialectLaneState =
      "ok:value:vector[int64:200,int64:200]" := by
  native_decide

theorem vector_dialect_shuffle_out_of_range_index_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.shuffle (.Vector 4 .I32) (ValueId.mk 6) [4, 0, 1, 2])
        vectorDialectLaneState =
      "error:ub" := by
  native_decide

theorem vector_dialect_shuffle_wrong_index_count_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.shuffle (.Vector 4 .I32) (ValueId.mk 6) [0, 1, 2])
        vectorDialectLaneState =
      "error:type_error" := by
  native_decide

-- `shuffle` graduated from unknown-op fixture to a modelled op (fast-4); the
-- canonical unknown vector op is now `gather`, which remains on the backlog.
def vectorUnknownOp : DialectInst :=
  { dialect := "vector"
    op := "gather"
    operands := []
    resultTys := []
    attrs := []
    version := 1 }

theorem vector_dialect_unknown_op_fails_closed_stable :
    vectorDialectOutcome vectorUnknownOp vectorDialectLaneState =
      "error:unsupported.dialect_op" := by
  native_decide

theorem vector_dialect_unknown_version_fails_closed_stable :
    vectorDialectOutcome
        { (VectorDialect.packLanes (.Vector 4 .I32)
            [v0, v1, v2, ValueId.mk 3]) with version := 2 }
        vectorDialectLaneState =
      "error:unsupported.dialect_op" := by
  native_decide

theorem vector_dialect_unsupported_shape_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.packLanes (.Vector 8 .I32)
          [v0, v1, v2, ValueId.mk 3])
        vectorDialectLaneState =
      "error:unsupported.vector_shape" := by
  native_decide

theorem vector_dialect_missing_lane_attr_fails_closed_stable :
    vectorDialectOutcome
        { (VectorDialect.extractLane (.Vector 4 .I32) .I32 (ValueId.mk 6) 0)
          with attrs := [VectorDialect.attr "vector_ty" (.ty (.Vector 4 .I32))] }
        vectorDialectLaneState =
      "error:type_error" := by
  native_decide

theorem vector_dialect_malformed_bit_order_fails_closed_stable :
    vectorDialectOutcome
        { (VectorDialect.maskToBits (.Vector 2 .Bool) (ValueId.mk 9) .I32)
          with attrs := [VectorDialect.attr "mask_ty" (.ty (.Vector 2 .Bool)),
                         VectorDialect.attr "bit_order" (.bool_ true)] }
        vectorDialectLaneState =
      "error:type_error" := by
  native_decide

theorem vector_dialect_out_of_range_lane_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.extractLane (.Vector 4 .I32) .I32 (ValueId.mk 6) 4)
        vectorDialectLaneState =
      "error:ub" := by
  native_decide

theorem vector_dialect_non_bool_mask_ty_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 4 .I32) (ValueId.mk 6) .I32)
        vectorDialectLaneState =
      "error:unsupported.vector_shape" := by
  native_decide

theorem vector_dialect_non_bool_mask_payload_fails_closed_stable :
    vectorDialectOutcome
        (VectorDialect.maskToBits (.Vector 4 .Bool) (ValueId.mk 6) .I32)
        vectorDialectLaneState =
      "error:unsupported.vector_shape" := by
  native_decide

theorem vector_raw_dialect_op_still_unsupported_stable :
    stepInstStableOutcome
        (.DialectOp (VectorDialect.maskToBits (.Vector 4 .Bool) (ValueId.mk 8) .I32))
        vectorDialectLaneState =
      "error:unsupported.dialect_op" := by
  native_decide

-- Heap-lifetime UB locks (docs/ub-numerics-policy.md §6): a freed allocation
-- is terminally dead. Double free, use-after-free, and ARC refcount underflow
-- are UB on BOTH engines (interpreter: "Dealloc: allocation is already dead" /
-- "use after dealloc" / "Release: reference count underflow (double free)";
-- Lean: the alive checks semDealloc / Sem.checkedAccess / getAllocIdFromPtrARC
-- make on the allocation a pointer was derived from). Symbolic twins:
-- semDealloc_twice_is_ub,
-- semLoad_after_dealloc_is_ub, semRelease_after_last_release_is_ub
-- (Proofs/MemorySafety.lean). Rust twins: b2_heapalloc.rs heap-lifetime tests
-- and interpret.rs use_after_dealloc_reports_undefined_behavior_code.

-- Alloca binds the pointer as v0 from the empty state's nextValueId = 0.
theorem dealloc_once_ok_stable :
    stepTwoInstStableOutcome (.Alloca .I32 none none) (.Dealloc v0)
        MachineState.empty =
      "ok:value:none" := by
  native_decide

theorem dealloc_twice_ub_code_stable :
    stepThreeInstStableOutcome (.Alloca .I32 none none) (.Dealloc v0) (.Dealloc v0)
        MachineState.empty =
      "error:ub" := by
  native_decide

theorem load_after_dealloc_ub_code_stable :
    stepThreeInstStableOutcome (.Alloca .I32 none none) (.Dealloc v0)
        (.Load .I32 v0 false none) MachineState.empty =
      "error:ub" := by
  native_decide

/-- A live ARC allocation with `arcRef` permission and refcount 2 at v0. -/
def arcTwoRefState : MachineState :=
  let (addr, mem) := Memory.empty.alloc 4 4 heapUsableSlack .swiftHeap
  { MachineState.empty with
    memory      := mem
    permissions := PermissionMap.empty.set (AllocId.mk 0) .arcRef
    refCounts   := setRefCount RefCountMap.empty (AllocId.mk 0) 2
    locals      := ValueMap.empty.set v0 (.ptr addr (some (AllocId.mk 0)))
    nextValueId := 1 }

/-- Same allocation holding its LAST reference (refcount 1). -/
def arcLastRefState : MachineState :=
  { arcTwoRefState with
    refCounts := setRefCount RefCountMap.empty (AllocId.mk 0) 1 }

theorem release_with_remaining_refs_ok_stable :
    stepInstStableOutcome (.Release v0) arcTwoRefState =
      "ok:value:none" := by
  native_decide

/-- Releasing the last reference frees the allocation; a second Release is
    the ARC double free (refcount underflow) — UB. -/
theorem release_after_last_release_ub_code_stable :
    stepTwoInstStableOutcome (.Release v0) (.Release v0) arcLastRefState =
      "error:ub" := by
  native_decide

/-- Retain on an allocation freed by the last Release is use-after-free UB. -/
theorem retain_after_free_ub_code_stable :
    stepTwoInstStableOutcome (.Release v0) (.Retain v0) arcLastRefState =
      "error:ub" := by
  native_decide

-- P1 "Native ARC for Clean": `AllocOrigin.CleanHeap` / `AllocationOrigin.cleanHeap`.
-- Clean's Perceus RC cells follow EXACTLY the swiftHeap refcount discipline —
-- no origin-sensitive rule distinguishes them (symbolically:
-- `alloc_isInBounds_ignores_origin`, Proofs/MemoryProps.lean); the origin tag
-- is provenance so the backend routes the free to Clean's runtime, not
-- Swift's. The twin states below differ from the swiftHeap ones ONLY in the
-- origin tag, and the parity theorems pin identical observable outcomes.
--
-- Model boundary, revised by WS2.19: `semHeapAlloc` used to grant `owned`
-- for EVERY origin while the ARC ops require `arcRef`, so the lifecycle
-- fixtures below start from a hand-built runtime-initialized fresh-cell
-- state (arcRef, refcount 1). The W5b oracle measured that boundary as a
-- DIVERGENCE (the reference interpreter runs `HeapAlloc CleanHeap` +
-- `Retain` to `Ok`; the model said UB), so an RC-origin `HeapAlloc`
-- (`AllocOrigin.isRefCounted`: SwiftHeap / CleanHeap) now produces exactly
-- that fresh-cell state itself — the `*_from_heap_alloc_*` fixtures at the
-- end of this group run the same lifecycles from a bare `HeapAlloc`, and
-- the non-RC twin (`RustHeap`) keeps refusing the trio.

/-- `HeapAlloc` with the CleanHeap origin executes: origin is provenance
    only, so the fresh Clean cell gets the same first address as any other
    origin (`Memory.empty` reserves the null page below 1024). -/
theorem heap_alloc_clean_heap_stable :
    stepInstStableOutcome (.HeapAlloc .I32 none none .CleanHeap)
        MachineState.empty =
      "ok:value:ptr:1024" := by
  native_decide

/-- `HeapAlloc` outcome parity between the CleanHeap and SwiftHeap origins. -/
theorem heap_alloc_clean_swift_parity_stable :
    stepInstStableOutcome (.HeapAlloc .I32 none none .CleanHeap)
        MachineState.empty =
      stepInstStableOutcome (.HeapAlloc .I32 none none .SwiftHeap)
        MachineState.empty := by
  native_decide

/-- A fresh Clean Perceus cell as `clean_alloc_ctor` leaves it: cleanHeap
    origin, `arcRef` permission, refcount 1 (one owner), pointer at v0.
    Twin of `arcLastRefState` — the states differ only in the origin tag. -/
def cleanFreshCellState : MachineState :=
  let (addr, mem) := Memory.empty.alloc 4 4 heapUsableSlack .cleanHeap
  { MachineState.empty with
    memory      := mem
    permissions := PermissionMap.empty.set (AllocId.mk 0) .arcRef
    refCounts   := setRefCount RefCountMap.empty (AllocId.mk 0) 1
    locals      := ValueMap.empty.set v0 (.ptr addr (some (AllocId.mk 0)))
    nextValueId := 1 }

/-- Retain on a fresh Clean cell (count 1→2), then IsUnique: false. -/
theorem clean_retain_isunique_false_stable :
    stepTwoInstStableOutcome (.Retain v0) (.IsUnique v0)
        cleanFreshCellState =
      "ok:value:bool:false" := by
  native_decide

/-- The requested Clean RC lifecycle — Retain → IsUnique → Release →
    Release — drives the count 1→2→2→1→0: the last Release reaches
    refcount zero and frees the cell (ok, not UB). -/
theorem clean_rc_lifecycle_reaches_zero_stable :
    stepInstListStableOutcome
        [.Retain v0, .IsUnique v0, .Release v0, .Release v0]
        cleanFreshCellState =
      "ok:value:none" := by
  native_decide

/-- One Release past zero is the RC underflow (the Perceus double free):
    UB, exactly as for swiftHeap (`release_after_last_release_ub_code_stable`). -/
theorem clean_release_underflow_ub_code_stable :
    stepInstListStableOutcome
        [.Retain v0, .IsUnique v0, .Release v0, .Release v0, .Release v0]
        cleanFreshCellState =
      "error:ub" := by
  native_decide

/-- Refcount-discipline parity, lifecycle: the cleanHeap cell and its
    swiftHeap twin (`arcLastRefState`, identical state modulo origin tag)
    produce the SAME stable outcome for the full lifecycle. -/
theorem clean_swift_rc_lifecycle_parity_stable :
    stepInstListStableOutcome
        [.Retain v0, .IsUnique v0, .Release v0, .Release v0]
        cleanFreshCellState =
      stepInstListStableOutcome
        [.Retain v0, .IsUnique v0, .Release v0, .Release v0]
        arcLastRefState := by
  native_decide

/-- Refcount-discipline parity, underflow UB: same twin comparison one
    Release past zero. -/
theorem clean_swift_rc_underflow_parity_stable :
    stepInstListStableOutcome
        [.Retain v0, .IsUnique v0, .Release v0, .Release v0, .Release v0]
        cleanFreshCellState =
      stepInstListStableOutcome
        [.Retain v0, .IsUnique v0, .Release v0, .Release v0, .Release v0]
        arcLastRefState := by
  native_decide

/-- WS2.19: the Clean lifecycle from a BARE `HeapAlloc CleanHeap` — the shape
    of the `inst_borrow_arc` fixture's `clean_rc_lifecycle` — reaches zero
    and frees the cell, as in the reference interpreter. The `HeapAlloc`
    binds the pointer as v0 from the empty state's nextValueId = 0. -/
theorem clean_rc_lifecycle_from_heap_alloc_reaches_zero_stable :
    stepInstListStableOutcome
        [.HeapAlloc .I64 none none .CleanHeap, .Retain v0, .IsUnique v0,
         .Release v0, .Release v0]
        MachineState.empty =
      "ok:value:none" := by
  native_decide

/-- The fresh RC cell has ONE owner: Retain then IsUnique is false, and
    IsUnique alone is true. -/
theorem clean_heap_alloc_is_unique_stable :
    stepTwoInstStableOutcome (.HeapAlloc .I64 none none .CleanHeap) (.IsUnique v0)
        MachineState.empty =
      "ok:value:bool:true" := by
  native_decide

theorem swift_heap_alloc_retain_is_unique_false_stable :
    stepThreeInstStableOutcome (.HeapAlloc .I64 none none .SwiftHeap) (.Retain v0)
        (.IsUnique v0) MachineState.empty =
      "ok:value:bool:false" := by
  native_decide

/-- Underflow from the bare allocation is still the Perceus double free. -/
theorem clean_rc_underflow_from_heap_alloc_ub_stable :
    stepInstListStableOutcome
        [.HeapAlloc .I64 none none .CleanHeap, .Release v0, .Release v0]
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- Negative twin: a `RustHeap` cell has no refcount discipline, so the ARC
    trio on it is still refused — the refinement is keyed on the origin, not
    on "any heap cell". -/
theorem rust_heap_alloc_retain_is_ub_stable :
    stepTwoInstStableOutcome (.HeapAlloc .I64 none none .RustHeap) (.Retain v0)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- And the RC cell's payload stays writable and readable: the permission
    gate on `Load` / `Store` is the pointer/bounds discipline, not `arcRef`. -/
theorem clean_heap_alloc_store_load_round_trips_stable :
    stepInstListStableOutcome
        [.HeapAlloc .I64 none none .CleanHeap, .Const .I64 (.int 42),
         .Store .I64 v0 v1 false none, .Load .I64 v0 false none]
        MachineState.empty =
      "ok:value:int64:42" := by
  native_decide

-- A reference-counted cell is released by `Release`, never by `Dealloc`
-- (docs/SPEC_RATIFICATIONS.md): `Dealloc` of a fresh `CleanHeap` /
-- `SwiftHeap` cell is UB (its `arcRef` permission cannot deallocate), and the
-- `Release` that takes the count to zero frees it — a `Load` after it is a
-- use-after-free. Symbolic twins: `semDealloc_cleanHeap_is_ub_example`,
-- `semDealloc_swiftHeap_is_ub_example`, `semDealloc_arcRef_is_ub`
-- (Proofs/MemorySafety.lean). Rust twin:
-- `dealloc_of_a_reference_counted_cell_is_undefined_behavior` (interpret.rs).

theorem clean_heap_alloc_dealloc_is_ub_stable :
    stepTwoInstStableOutcome (.HeapAlloc .I64 none none .CleanHeap) (.Dealloc v0)
        MachineState.empty =
      "error:ub" := by
  native_decide

theorem swift_heap_alloc_dealloc_is_ub_stable :
    stepTwoInstStableOutcome (.HeapAlloc .I64 none none .SwiftHeap) (.Dealloc v0)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- `Release` at count 1 frees the cell: the `Load` after it is UB. -/
theorem clean_heap_alloc_release_frees_stable :
    stepInstListStableOutcome
        [.HeapAlloc .I64 none none .CleanHeap, .Const .I64 (.int 42),
         .Store .I64 v0 v1 false none, .Release v0, .Load .I64 v0 false none]
        MachineState.empty =
      "error:ub" := by
  native_decide

def singletonCFG (block : BasicBlock) : CFG :=
  fun bid => if bid == b0 then some block else none

def functionMap (entries : List (FuncId × EvalFunction)) :
    FuncId -> Option EvalFunction :=
  fun fid =>
    match entries.find? (fun entry => entry.fst.index == fid.index) with
    | some entry => some entry.snd
    | none => none

def funcPtrMap (entries : List (Nat × FuncId)) : FuncPtrTable :=
  fun addr =>
    match entries.find? (fun entry => entry.fst == addr) with
    | some entry => some entry.snd
    | none => none

def funcTyMap (entries : List (FuncTyId × FuncTyDef)) : FuncTyTable :=
  fun sig =>
    match entries.find? (fun entry => entry.fst.index == sig.index) with
    | some entry => some entry.snd
    | none => none

def returnConstCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Const .I32 (.int 41)]
      terminator := .Return [v0] }

theorem return_const_eval_stable :
    evalValuesStableOutcome (evalFunction returnConstCFG b0 [] 1)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

def interproceduralCallCFG : CFG :=
  singletonCFG
    { params := []
      body := []
      terminator := .Call (FuncId.mk 0) [] }

theorem interprocedural_call_unsupported_code_stable :
    evalValuesStableOutcome (evalFunction interproceduralCallCFG b0 [] 1)
        MachineState.empty =
      "error:unsupported.interprocedural_call" := by
  native_decide

def i32IdentityCFG : CFG :=
  singletonCFG
    { params := [(v0, .I32)]
      body := []
      terminator := .Return [v0] }

def i32IdentityFunction : EvalFunction :=
  { body := { paramTys := [.I32], returnTys := [.I32] }
    cfg := i32IdentityCFG
    entryBlock := b0 }

def directCallCFG : CFG :=
  singletonCFG
    { params := [(v0, .I32)]
      body := []
      terminator := .Call f1 [v0] }

def directCallFunction : EvalFunction :=
  { body := { paramTys := [.I32], returnTys := [.I32] }
    cfg := directCallCFG
    entryBlock := b0 }

def directCallContext : EvalContext :=
  { functions := functionMap [(f0, directCallFunction), (f1, i32IdentityFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem direct_call_eval_stable :
    evalValuesStableOutcome
        (evalFunctionInContext directCallContext f0 [.int 32 7] 2)
        MachineState.empty =
      "ok:return:[int32:7]" := by
  native_decide

def missingDirectCallContext : EvalContext :=
  { functions := functionMap [(f0, directCallFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem direct_call_undefined_function_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext missingDirectCallContext f0 [.int 32 7] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

def const42Function : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := returnConstCFG
    entryBlock := b0 }

def directBodyCallCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Call f1 []]
      bodyResultDests := [[v0]]
      terminator := .Return [v0] }

def directBodyCallFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := directBodyCallCFG
    entryBlock := b0 }

def directBodyCallContext : EvalContext :=
  { functions := functionMap [(f0, directBodyCallFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem direct_body_call_eval_stable :
    evalValuesStableOutcome
        (evalFunctionInContext directBodyCallContext f0 [] 2)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

def b1 : BlockId := BlockId.mk 1
def b2 : BlockId := BlockId.mk 2

/-- Invoke caller: entry invokes the i32 identity function; the callee's
    return binds the invoke's own result (v1), which the normal edge passes
    to b1; the unwind edge names a landing-pad block (b2) that evaluation
    never reaches. Mirrors interpret.rs Inst::Invoke: run like Call, bind
    node results, then take the NORMAL edge. -/
def invokeCallerCFG : CFG := fun bid =>
  if bid.index == 0 then
    some { params := [(v0, .I32)]
           body := []
           terminator := .Invoke f1 [v0] b1 [v1] b2
           terminatorResultDests := [v1] }
  else if bid.index == 1 then
    some { params := [(v2, .I32)]
           body := []
           terminator := .Return [v2] }
  else if bid.index == 2 then
    some { params := []
           body := [.LandingPad true []]
           terminator := .Unreachable }
  else none

def invokeCallerFunction : EvalFunction :=
  { body := { paramTys := [.I32], returnTys := [.I32] }
    cfg := invokeCallerCFG
    entryBlock := b0 }

def invokeContext : EvalContext :=
  { functions := functionMap [(f0, invokeCallerFunction), (f1, i32IdentityFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem invoke_takes_normal_edge_with_results_stable :
    evalValuesStableOutcome
        (evalFunctionInContext invokeContext f0 [.int 32 9] 4)
        MachineState.empty =
      "ok:return:[int32:9]" := by
  native_decide

/-- An undefined invoke callee is the same structured type error as an
    undefined call callee. -/
def missingInvokeContext : EvalContext :=
  { functions := functionMap [(f0, invokeCallerFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem invoke_undefined_function_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext missingInvokeContext f0 [.int 32 9] 4)
        MachineState.empty =
      "error:type_error" := by
  native_decide

def b3 : BlockId := BlockId.mk 3

/-- Two SEQUENTIAL invokes in one caller at maxCallDepth 1: call depth bounds
    NESTING only (each callee runs at depth 0; the caller resumes at its own
    depth after the normal edge), so this must succeed — an Invoke must not
    permanently burn depth budget (regression lock for the normal-edge
    continuation depth, mirroring interpret.rs). -/
def sequentialInvokesCFG : CFG := fun bid =>
  if bid.index == 0 then
    some { params := []
           body := []
           terminator := .Invoke f1 [] b1 [] b3
           terminatorResultDests := [v1] }
  else if bid.index == 1 then
    some { params := []
           body := []
           terminator := .Invoke f1 [] b2 [] b3
           terminatorResultDests := [v2] }
  else if bid.index == 2 then
    some { params := []
           body := []
           terminator := .Return [v2] }
  else if bid.index == 3 then
    some { params := []
           body := [.LandingPad true []]
           terminator := .Unreachable }
  else none

def sequentialInvokesFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := sequentialInvokesCFG
    entryBlock := b0 }

def sequentialInvokesContext : EvalContext :=
  { functions := functionMap
      [(f0, sequentialInvokesFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 1
    globalsTable := fun _ => none }

theorem sequential_invokes_do_not_burn_call_depth_stable :
    evalValuesStableOutcome
        (evalFunctionInContext sequentialInvokesContext f0 [] 8)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

def badReturnCFG : CFG :=
  singletonCFG
    { params := []
      body := []
      terminator := .Return [] }

def badReturnFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := badReturnCFG
    entryBlock := b0 }

def bodyCallReturnArityMismatchContext : EvalContext :=
  { functions := functionMap [(f0, directBodyCallFunction), (f1, badReturnFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem body_call_return_arity_mismatch_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext bodyCallReturnArityMismatchContext f0 [] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

def indirectCallCFG : CFG :=
  singletonCFG
    { params := [(v0, .Ptr)]
      body := []
      terminator := .CallIndirect v0 sig0 [] .C }

def indirectCallFunction : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [.I32] }
    cfg := indirectCallCFG
    entryBlock := b0 }

def indirectCallContext : EvalContext :=
  { functions := functionMap [(f0, indirectCallFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap [(ptr0, f1)]
    funcTys := funcTyMap
      [(sig0, { params := [], returns := [.I32], isVararg := false })]
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem indirect_call_eval_stable :
    evalValuesStableOutcome
        (evalFunctionInContext indirectCallContext f0 [.ptr ptr0 none] 2)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

def indirectBodyCallCFG : CFG :=
  singletonCFG
    { params := [(v0, .Ptr)]
      body := [.CallIndirect v0 sig0 [] .C]
      bodyResultDests := [[v1]]
      terminator := .Return [v1] }

def indirectBodyCallFunction : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [.I32] }
    cfg := indirectBodyCallCFG
    entryBlock := b0 }

def indirectBodyCallContext : EvalContext :=
  { functions := functionMap [(f0, indirectBodyCallFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap [(ptr0, f1)]
    funcTys := funcTyMap
      [(sig0, { params := [], returns := [.I32], isVararg := false })]
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem indirect_body_call_eval_stable :
    evalValuesStableOutcome
        (evalFunctionInContext indirectBodyCallContext f0 [.ptr ptr0 none] 2)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

/-- `f0 : (ptr) -> i32` with `CallIndirect`'s unwinding twin (amendment D,
    Part 2): `invoke_indirect` resolves the pointer to `f1` (returns 41),
    binds its result to the node's own result `v1`, and passes it to `bb1` on
    the NORMAL edge; `bb2` is a cleanup pad the panic=abort projection never
    reaches (Rust: `invoke_indirect_takes_the_normal_edge`). -/
def invokeIndirectCallerFunction : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [.I32] }
    cfg := fun bid =>
      if bid.index == 0 then
        some { params := [(v0, .Ptr)]
               body := []
               terminator := .InvokeIndirect v0 sig0 [] .C (BlockId.mk 1) [v1] (BlockId.mk 2)
               terminatorResultDests := [v1] }
      else if bid.index == 1 then
        some { params := [(ValueId.mk 2, .I32)]
               body := []
               terminator := .Return [ValueId.mk 2] }
      else if bid.index == 2 then
        some { params := []
               body := [.LandingPad true []]
               bodyResultDests := [[ValueId.mk 3, ValueId.mk 4]]
               terminator := .Resume (ValueId.mk 3) }
      else none
    entryBlock := b0 }

def invokeIndirectContext : EvalContext :=
  { functions := functionMap [(f0, invokeIndirectCallerFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap [(ptr0, f1)]
    funcTys := funcTyMap
      [(sig0, { params := [], returns := [.I32], isVararg := false })]
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem invoke_indirect_takes_normal_edge_stable :
    evalValuesStableOutcome
        (evalFunctionInContext invokeIndirectContext f0 [.ptr ptr0 none] 4)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

def indirectSignatureMismatchContext : EvalContext :=
  { functions := functionMap [(f0, indirectCallFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap [(ptr0, f1)]
    funcTys := funcTyMap
      [(sig0, { params := [], returns := [.I64], isVararg := false })]
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem indirect_call_signature_mismatch_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext indirectSignatureMismatchContext f0 [.ptr ptr0 none] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

def invalidFunctionPointerContext : EvalContext :=
  { functions := functionMap [(f0, indirectCallFunction), (f1, const42Function)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap
      [(sig0, { params := [], returns := [.I32], isVararg := false })]
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem indirect_call_invalid_pointer_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext invalidFunctionPointerContext f0 [.ptr ptr0 none] 2)
        MachineState.empty =
      "error:ub" := by
  native_decide

def recursiveCallCFG : CFG :=
  singletonCFG
    { params := []
      body := []
      terminator := .Call f0 [] }

def recursiveCallFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [] }
    cfg := recursiveCallCFG
    entryBlock := b0 }

def recursiveCallContext : EvalContext :=
  { functions := functionMap [(f0, recursiveCallFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 64
    globalsTable := fun _ => none }

theorem recursive_call_fuel_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext recursiveCallContext f0 [] 2)
        MachineState.empty =
      "error:out_of_fuel" := by
  native_decide

-- GlobalAddr FULL FIDELITY (semGlobalAddrWithCtx via stepNWithContext): a scalar
-- global with an initializer is allocated at its TRUE byte size, the initializer
-- is written, and a Load through the materialized pointer reads it back — proving
-- the upgrade over the bare size-1 partial (which has no initializer, so a Load
-- there would not return the value).
def globalLoadCFG : CFG :=
  singletonCFG
    { params := []
      body := [.GlobalAddr (GlobalId.mk 0), .Load .I32 v0 false none]
      terminator := .Return [v1] }

def globalLoadFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := globalLoadCFG
    entryBlock := b0 }

def globalLoadContext : EvalContext :=
  { functions := functionMap [(f0, globalLoadFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun g =>
      if g == GlobalId.mk 0 then some { ty := .I32, initializer := some (.int 42) }
      else none }

theorem global_addr_full_fidelity_load_stable :
    evalValuesStableOutcome
        (evalFunctionInContext globalLoadContext f0 [] 4)
        MachineState.empty =
      "ok:return:[int32:42]" := by
  native_decide

-- BSS / .tbss zero-fill: a global with NO initializer is zero-filled at load
-- time, so a Load through its pointer reads a DEFINED zero — not uninitialized
-- (which, post copy-propagates-poison, would read back a `.partial` image).
-- Reuses `globalLoadFunction` (GlobalAddr then Load .I32) but with an
-- initializer-less global. Mirrors interpret.rs commit 2b3954e.
def globalBssContext : EvalContext :=
  { functions := functionMap [(f0, globalLoadFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun g =>
      if g == GlobalId.mk 0 then some { ty := .I32, initializer := none }
      else none }

theorem global_addr_bss_zero_fill_load_stable :
    evalValuesStableOutcome
        (evalFunctionInContext globalBssContext f0 [] 4)
        MachineState.empty =
      "ok:return:[int32:0]" := by
  native_decide

-- WS2.18: a global whose initializer is a relocatable symbol address (a
-- vtable / fn-pointer table slot) has no load-time value the model can write:
-- the full-fidelity path refuses it instead of encoding a placeholder.
def globalSymbolAddrContext : EvalContext :=
  { functions := functionMap [(f0, globalLoadFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun g =>
      if g == GlobalId.mk 0 then some { ty := .Ptr, initializer := some (.symbolAddr "f" 0) }
      else none }

theorem global_addr_symbol_addr_initializer_refused_stable :
    evalValuesStableOutcome
        (evalFunctionInContext globalSymbolAddrContext f0 [] 4)
        MachineState.empty =
      "error:unsupported.link_time_address" := by
  native_decide

def nullGlobalPointerCorrect (model : ByteModel) (ty : Ty) : Bool :=
  let table : GlobalsTable := fun _ =>
    some { ty := ty, initializer := some (nullPointerSpelling ty) }
  match Sem.run (do
      let address ← semGlobalAddrWithCtx table (GlobalId.mk 0) model
      let loaded ← semLoad ty address false none model
      Sem.lookupValue loaded) MachineState.empty with
  | .ok (value, _) => nullPointerValueCorrect model ty value
  | .error _ => false

/-- Null global images already have the target's pointer width. Materialize
    and load every kind to check constructors, metadata and provenance too. -/
theorem global_null_pointer_kinds_round_trip_stable :
    fixtureByteModels.all (fun model => nullPointerKinds.all (nullGlobalPointerCorrect model)) =
      true := by
  native_decide

def globalInitializerMalformedTypeRejected (model : ByteModel) : Bool :=
  let table : GlobalsTable := fun _ =>
    some { ty := .I32, initializer := some (.bool true) }
  match Sem.run (semGlobalAddrWithCtx table (GlobalId.mk 0) model) MachineState.empty with
  | .error (.typeError message) =>
    message == "constant does not match its declared type"
  | _ => false

/-- A malformed bool-at-I32 initializer is now rejected by type conversion,
    before byte encoding. The independent exact-image-length guard remains
    at materialization; this fixture does not claim that guard was reached. -/
theorem global_initializer_malformed_type_rejected_stable :
    fixtureByteModels.all globalInitializerMalformedTypeRejected = true := by
  native_decide

def encodedBytesMatch (encoded : Except SemError (List UInt8))
    (expected : List UInt8) : Bool :=
  match encoded with
  | .ok bytes => bytes == expected
  | .error _ => false

def encodedBytesStableOutcome : Except SemError (List UInt8) → String
  | .ok bytes => s!"ok:{bytes.length}"
  | .error error => "error:" ++ error.code

theorem unit_memory_typed_empty_image_stable :
    fixtureByteModels.all (fun model =>
      encodedBytesMatch (encodeMemoryAt model .Unit (.aggregate [])) []) = true := by
  native_decide

theorem unit_memory_empty_image_round_trip_stable :
    fixtureByteModels.map (fun model => checkedConstantStableOutcome (do
      let bytes ← encodeMemoryAt model .Unit (.aggregate [])
      decodeMemoryAt model Memory.empty .Unit bytes)) =
      ["ok:aggregate[]", "ok:aggregate[]"] := by
  native_decide

theorem unit_memory_empty_aggregate_other_type_refused_stable :
    fixtureByteModels.map (fun model =>
      encodedBytesStableOutcome (encodeMemoryAt model .I8 (.aggregate []))) =
      ["error:type_error", "error:type_error"] := by
  native_decide

def vectorScalarLayoutCases : List (Ty × Nat) :=
  [(.Bool, 1), (.I8, 1), (.U8, 1), (.I16, 2), (.U16, 2), (.F16, 2),
   (.I32, 4), (.U32, 4), (.F32, 4), (.I64, 8), (.U64, 8), (.F64, 8)]

/-- Packed vectors use element alignment, including odd lane counts; their
    admitted fixed-width lanes have the same layout on both targets. -/
theorem vector_memory_scalar_layouts_stable :
    fixtureByteModels.all (fun model => vectorScalarLayoutCases.all (fun (elemTy, size) =>
      (Ty.Vector 3 elemTy).byteSizeFor model == some (3 * size) &&
      (Ty.Vector 3 elemTy).byteAlignFor model == some size)) = true := by
  native_decide

theorem vector_memory_bool_mask_image_stable :
    fixtureByteModels.all (fun model => encodedBytesMatch
      (encodeMemoryAt model (.Vector 3 .Bool) (.vector [.bool true, .bool false, .bool true]))
      [255, 0, 255]) = true := by
  native_decide

/-- The typed constant rounds to binary32 once. Its image also retains the
    negative-zero sign bit, which float equality alone cannot distinguish. -/
theorem vector_memory_f32_rounded_image_stable :
    fixtureByteModels.all (fun model => encodedBytesMatch
      (encodeMemoryAt model (.Vector 2 .F32)
        (constValueAt (.Vector 2 .F32) (.vector [.float 0.1, .float (-0.0)]) model))
      [205, 204, 204, 61, 0, 0, 0, 128]) = true := by
  native_decide

def vectorMemoryRoundTripOutcome (model : ByteModel) (ty : Ty) (value : Value) : String :=
  checkedConstantStableOutcome (do
    let bytes ← encodeMemoryAt model ty value
    decodeMemoryAt model Memory.empty ty bytes)

theorem vector_memory_integer_and_mask_round_trip_stable :
    fixtureByteModels.map (fun model =>
      [vectorMemoryRoundTripOutcome model (.Vector 2 .I8) (.vector [.int 8 249, .int 8 2]),
       vectorMemoryRoundTripOutcome model (.Vector 3 .Bool)
         (.vector [.bool true, .bool false, .bool true])]) =
      List.replicate 2 ["ok:vector[int8:249,int8:2]", "ok:vector[bool:true,bool:false,bool:true]"] := by
  native_decide

def vectorF32RoundTripCorrect (model : ByteModel) : Bool :=
  let ty := Ty.Vector 2 .F32
  let value := constValueAt ty (.vector [.float 0.1, .float 1.0006]) model
  match (do
      let bytes ← encodeMemoryAt model ty value
      decodeMemoryAt model Memory.empty ty bytes) with
  | .ok (.vector [.float first, .float second]) =>
    first == constFloatAt .F32 0.1 && second == constFloatAt .F32 1.0006
  | _ => false

theorem vector_memory_f32_round_trip_stable :
    fixtureByteModels.all vectorF32RoundTripCorrect = true := by
  native_decide

/-- No missing lane, extra lane, scalar substitute or wrong-width lane may
    be materialized as a vector image. -/
theorem vector_memory_malformed_values_refused_stable :
    fixtureByteModels.map (fun model =>
      [.vector [.int 8 1], .vector [.int 8 1, .int 8 2, .int 8 3],
       .int 16 513, .vector [.int 16 1, .int 8 2]].map (fun value =>
        encodedBytesStableOutcome (encodeMemoryAt model (.Vector 2 .I8) value))) =
      List.replicate 2 (List.replicate 4 "error:type_error") := by
  native_decide

theorem vector_memory_wrong_image_lengths_refused_stable :
    fixtureByteModels.map (fun model =>
      [[1], [1, 2, 3]].map (fun bytes => checkedConstantStableOutcome
        (decodeMemoryAt model Memory.empty (.Vector 2 .U8) bytes))) =
      List.replicate 2 ["error:type_error", "error:type_error"] := by
  native_decide

theorem vector_memory_zero_lanes_refused_stable :
    fixtureByteModels.all (fun model =>
      (Ty.Vector 0 .U8).byteSizeFor model == none &&
      (Ty.Vector 0 .U8).byteAlignFor model == none &&
      encodedBytesStableOutcome (encodeMemoryAt model (.Vector 0 .U8) (.vector [])) ==
        "error:unsupported.vector_shape" &&
      checkedConstantStableOutcome (decodeMemoryAt model Memory.empty (.Vector 0 .U8) []) ==
        "error:unsupported.vector_shape") = true := by
  native_decide

/-- The type boundary follows the validator, excluding pointer, pointer-sized,
    128-bit and nested lanes instead of admitting arbitrary scalar fallbacks. -/
theorem vector_memory_unadmitted_lane_types_refused_stable :
    fixtureByteModels.all (fun model =>
      [Ty.Ptr, .Usize, .I128, .Vector 1 .Bool].all (fun elemTy =>
        (Ty.Vector 1 elemTy).byteSizeFor model == none &&
        (Ty.Vector 1 elemTy).byteAlignFor model == none &&
        encodedBytesStableOutcome (encodeMemoryAt model (.Vector 1 elemTy) (.vector [.nullPtr])) ==
          "error:type_error" &&
        checkedConstantStableOutcome
          (decodeMemoryAt model Memory.empty (.Vector 1 elemTy) [0]) == "error:type_error")) =
      true := by
  native_decide

/-- Typed vector support grants no untyped byte-image fallback. -/
theorem vector_memory_untyped_image_stays_refused_stable :
    encodeValue (.vector [.int 8 1, .int 8 2]) = none := by
  native_decide

def directCallDepthZeroContext : EvalContext :=
  { directCallContext with maxCallDepth := 0 }

theorem direct_call_depth_limit_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext directCallDepthZeroContext f0 [.int 32 7] 2)
        MachineState.empty =
      "error:out_of_fuel" := by
  native_decide

theorem out_of_fuel_code_stable :
    evalValuesStableOutcome (evalFunction returnConstCFG b0 [] 0)
        MachineState.empty =
      "error:out_of_fuel" := by
  native_decide

/-!
## SeqMap (general element-op loop instruction)

`Inst.SeqMap ty seq fwd` applies the element function `fwd : fn(&mut elem)`
to every element of a sequence via the standard call machinery (per-element
memory cell, frame save/restore, ONE call-depth level for the whole map).
These fixtures are the Lean side of the Rust/Lean agreement pins mirrored by
`crates/trust-ir/src/interpret.rs` tests
(`seq_map_*` — see designs/2026-06-30-general-seqmap-instruction.md):
success, element type error, depth accounting (depth bounds NESTING, not
sequence length), missing element function, bad element-function signature,
and the bare-evaluator fail-closed path.
-/

/-- The element function `incr_elem(x: &mut i32) { *x += 1 }`:
    load through the &mut param, add 1, store back, return unit.
    Fresh SSA ids: v1 = load, v2 = const 1, v3 = v1 + v2. -/
def seqMapIncrElemCFG : CFG :=
  singletonCFG
    { params := [(v0, .RefMut .I32)]
      body := [.Load .I32 v0 false none,
               .Const .I32 (.int 1),
               .BinOp .Add .I32 v1 v2,
               .Store .I32 v0 v3 false none]
      terminator := .Return [] }

def seqMapIncrElemFunction : EvalFunction :=
  { body := { paramTys := [.RefMut .I32], returnTys := [] }
    cfg := seqMapIncrElemCFG
    entryBlock := b0 }

/-- The loop function `incr_all(l: Seq<i32>) -> Seq<i32>`:
    one `SeqMap` body instruction binding its mapped sequence to v1. -/
def seqMapLoopCFG : CFG :=
  singletonCFG
    { params := [(v0, .Sequence (TyId.mk 0))]
      body := [.SeqMap (.Sequence (TyId.mk 0)) v0 f1]
      bodyResultDests := [[v1]]
      terminator := .Return [v1] }

def seqMapLoopFunction : EvalFunction :=
  { body := { paramTys := [.Sequence (TyId.mk 0)]
              returnTys := [.Sequence (TyId.mk 0)] }
    cfg := seqMapLoopCFG
    entryBlock := b0 }

/-- maxCallDepth = 1: ONE nesting level suffices for ANY element count —
    the depth pin below proves SeqMap does not burn depth per element. -/
def seqMapContext : EvalContext :=
  { functions := functionMap [(f0, seqMapLoopFunction), (f1, seqMapIncrElemFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 1
    globalsTable := fun _ => none }

/-- 3 elements at maxCallDepth 1 SUCCEED: depth bounds NESTING, not length. -/
theorem seq_map_incr_all_eval_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapContext f0
          [.sequence [.int 32 1, .int 32 2, .int 32 3]] 2)
        MachineState.empty =
      "ok:return:[sequence[int32:2,int32:3,int32:4]]" := by
  native_decide

/-- The empty sequence maps to the empty sequence (still costs a depth level). -/
theorem seq_map_empty_sequence_eval_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapContext f0 [.sequence []] 2)
        MachineState.empty =
      "ok:return:[sequence[]]" := by
  native_decide

/-- Element-op TYPE ERROR: a Bool element against `fn(&mut i32)` fails closed. -/
theorem seq_map_element_type_error_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapContext f0
          [.sequence [.int 32 1, .bool true]] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

/-- A non-sequence operand is a type error (from stepInst, before any call). -/
theorem seq_map_non_sequence_operand_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapContext f0 [.int 32 7] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

/-- Same-byte-width CROSS-TYPE element is a type error, never a silent
    reinterpret: a Bool element (1 byte) against `fn(&mut i8)` (1 byte) must
    be rejected by the TYPE guard, mirroring interpret.rs `elem.ty != elem_ty`
    — the byte-length check alone would wrongly accept it. -/
def seqMapIncrElemI8CFG : CFG :=
  singletonCFG
    { params := [(v0, .RefMut .I8)]
      body := [.Load .I8 v0 false none,
               .Const .I8 (.int 1),
               .BinOp .Add .I8 v1 v2,
               .Store .I8 v0 v3 false none]
      terminator := .Return [] }

def seqMapIncrElemI8Function : EvalFunction :=
  { body := { paramTys := [.RefMut .I8], returnTys := [] }
    cfg := seqMapIncrElemI8CFG
    entryBlock := b0 }

def seqMapI8Context : EvalContext :=
  { functions := functionMap [(f0, seqMapLoopFunction), (f1, seqMapIncrElemI8Function)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 1
    globalsTable := fun _ => none }

theorem seq_map_same_width_cross_type_rejected_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapI8Context f0
          [.sequence [.bool true]] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

/-- Float elements round-trip through the typed float codec at the element
    type (WS2.23): the identity element function returns the element intact
    (the former placeholder codec would have zeroed it, which is why this was
    a structured refusal before the IEEE images landed). -/
def seqMapIncrElemF64CFG : CFG :=
  singletonCFG
    { params := [(v0, .RefMut .F64)]
      body := []
      terminator := .Return [] }

def seqMapIncrElemF64Function : EvalFunction :=
  { body := { paramTys := [.RefMut .F64], returnTys := [] }
    cfg := seqMapIncrElemF64CFG
    entryBlock := b0 }

def seqMapF64Context : EvalContext :=
  { functions := functionMap [(f0, seqMapLoopFunction), (f1, seqMapIncrElemF64Function)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 1
    globalsTable := fun _ => none }

theorem seq_map_float_elements_roundtrip_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapF64Context f0
          [.sequence [.float 1.5]] 2)
        MachineState.empty =
      "ok:return:[sequence[float:1.500000]]" := by
  native_decide

def seqMapDepthZeroContext : EvalContext :=
  { seqMapContext with maxCallDepth := 0 }

/-- DEPTH: at maxCallDepth 0 the whole map is out of depth (even before any
    element runs) — mirrors the Rust interpreter's `ensure_call_depth`. -/
theorem seq_map_depth_limit_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapDepthZeroContext f0
          [.sequence [.int 32 1]] 2)
        MachineState.empty =
      "error:out_of_fuel" := by
  native_decide

def seqMapMissingFwdContext : EvalContext :=
  { seqMapContext with functions := functionMap [(f0, seqMapLoopFunction)] }

/-- An element function missing from the module fails closed. -/
theorem seq_map_undefined_fwd_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapMissingFwdContext f0
          [.sequence [.int 32 1]] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

/-- An element function that is NOT the single-&mut form `fn(&mut elem)`
    (here: by-value `fn(i32) -> i32`) is rejected. -/
def seqMapByValueElemFunction : EvalFunction :=
  { body := { paramTys := [.I32], returnTys := [.I32] }
    cfg := i32IdentityCFG
    entryBlock := b0 }

def seqMapBadSigContext : EvalContext :=
  { seqMapContext with
    functions := functionMap [(f0, seqMapLoopFunction), (f1, seqMapByValueElemFunction)] }

theorem seq_map_bad_fwd_signature_code_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapBadSigContext f0
          [.sequence [.int 32 1]] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

/-- The bare single-function evaluator (no function table) fails closed on
    SeqMap with the structured interprocedural unsupported code. -/
def seqMapNoContextCFG : CFG :=
  singletonCFG
    { params := [(v0, .Sequence (TyId.mk 0))]
      body := [.SeqMap (.Sequence (TyId.mk 0)) v0 f1]
      terminator := .Return [] }

theorem seq_map_requires_context_code_stable :
    evalValuesStableOutcome
        (evalFunction seqMapNoContextCFG b0 [.sequence []] 1)
        MachineState.empty =
      "error:unsupported.interprocedural_call" := by
  native_decide

-- Copy-propagates-poison (mirror of trust-ir interpret.rs commit 530fdd5):
-- transporting uninitialized bytes is fine; consuming them is UB.

/-- Two 8-byte stack cells. The source (`v0`) has its low four bytes written and
    its high four bytes never written; the destination (`v1`) is fresh. -/
def partialTransportState : MachineState :=
  let (a0, mem) := Memory.empty.alloc 8 8 0 .rustStack
  let mem := mem.writeBytes a0 [1, 2, 3, 4]      -- a0..a0+4 init; a0+4..a0+8 uninit
  let (a1, mem) := mem.alloc 8 8 0 .rustStack
  { (stateWith [(v0, .ptr a0 (some (AllocId.mk 0))), (v1, .ptr a1 (some (AllocId.mk 1)))] 2) with memory := mem }

/-- Observable value of a non-strict scalar load of the partially-initialized
    cell. -/
def partialScalarLoadOutcome : String :=
  match Sem.run (do
      let id ← semLoad .I64 v0
      Sem.lookupValue id) partialTransportState with
  | .ok (v, _) => "ok:" ++ stableValueString v
  | .error e   => "error:" ++ e.code

/-- (i) A plain (non-strict) scalar load whose range straddles never-written
    bytes yields a `.partial` poison image (8 bytes, 4 uninit) — NOT UB. -/
theorem partial_scalar_load_yields_partial_stable :
    partialScalarLoadOutcome = "ok:partial(8)" := by native_decide

/-- Load the poison image out of `v0`, store it verbatim into the fresh cell
    `v1` (the store half of copy-propagates-poison), then reload it. -/
def partialTransportOutcome : String :=
  match Sem.run (do
      let id ← semLoad .I64 v0
      semStore .I64 v1 id
      let id2 ← semLoad .I64 v1
      Sem.lookupValue id2) partialTransportState with
  | .ok (v, _) => "ok:" ++ stableValueString v
  | .error e   => "error:" ++ e.code

/-- (i, cont.) The poison image transports through `Store` + reload with NO UB,
    preserving which bytes stay uninitialized (still `partial(8)`). -/
theorem partial_store_transports_poison_stable :
    partialTransportOutcome = "ok:partial(8)" := by native_decide

/-- A poison i64 in `v0` and a defined i64 in `v1`. -/
def partialConsumeState : MachineState :=
  stateWith
    [ (v0, .partial [some 1, none, some 3, some 4, some 5, some 6, some 7, some 8])
    , (v1, .int 64 5) ] 2

/-- Outcome of an integer `Add` consuming the poison operand. -/
def partialArithOutcome : String :=
  match Sem.run (semBinOp .Add .I64 v0 v1) partialConsumeState with
  | .ok _    => "ok"
  | .error e => "error:" ++ e.code

/-- (ii) INSPECTING a poison value is undefined behaviour: arithmetic that
    consumes a `.partial` operand faults with `SemError.ub`. -/
theorem partial_arith_consumption_is_ub_stable :
    partialArithOutcome = "error:ub" := by native_decide

/-- Outcome of an integer comparison consuming the poison operand. -/
def partialICmpOutcome : String :=
  match Sem.run (semICmpInst .Eq .I64 v0 v1) partialConsumeState with
  | .ok _    => "ok"
  | .error e => "error:" ++ e.code

/-- (ii, cont.) A comparison consuming a `.partial` operand is likewise UB. -/
theorem partial_compare_consumption_is_ub_stable :
    partialICmpOutcome = "error:ub" := by native_decide

-- Undef is POISON (roadmap WS2.10; mirror interpret.rs `Inst::Undef` and
-- crates/trust-ir-conformance/tests/undef_poison.rs): executing `undef` is not
-- UB, transporting the value (a non-strict store writes uninitialized bytes)
-- is fine, and inspecting it — arithmetic, a branch condition, a call
-- boundary — is UB, exactly as for a `.partial` image.

/-- `%0 = undef u64; %1 = alloca u64; store %0, %1; %2 = 7; ret %2`. -/
def undefStoreCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Undef .U64, .Alloca .U64 none none, .Store .U64 v1 v0 false none,
               .Const .U64 (.int 7)]
      terminator := .Return [v2] }

/-- Positive: storing an undef only transports poison — the function returns 7
    (the Rust interpreter agrees since WS2.10; it used to trap at the undef). -/
theorem undef_store_then_ret_7_stable :
    evalValuesStableOutcome (evalFunction undefStoreCFG b0 [] 1)
        MachineState.empty =
      "ok:return:[int64:7]" := by
  native_decide

/-- `%0 = undef u64; %1 = 1; %2 = add %0, %1; ret %2`. -/
def undefAddCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Undef .U64, .Const .U64 (.int 1), .BinOp .Add .U64 v0 v1]
      terminator := .Return [v2] }

/-- Negative twin: arithmetic INSPECTING the undef is undefined behaviour
    (before WS2.10 Lean reported a type error here, Rust an eager UB). -/
theorem undef_add_is_ub_stable :
    evalValuesStableOutcome (evalFunction undefAddCFG b0 [] 1)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- Mutation control: `condbr (undef bool)` — branching on poison is UB. -/
def undefCondBrCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Undef .Bool]
      terminator := .CondBr v0 b0 [] b0 [] }

theorem undef_condbr_is_ub_stable :
    evalValuesStableOutcome (evalFunction undefCondBrCFG b0 [] 1)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- Store an undef, then reload it with a plain load: the reload observes the
    same poison (8 uninitialized bytes), not a value. -/
def undefStoreReloadCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Undef .U64, .Alloca .U64 none none, .Store .U64 v1 v0 false none,
               .Load .U64 v1 false none]
      terminator := .Return [v2] }

theorem undef_store_reload_is_poison_stable :
    evalValuesStableOutcome (evalFunction undefStoreReloadCFG b0 [] 1)
        MachineState.empty =
      "ok:return:[partial(8)]" := by
  native_decide

/-- A VOLATILE (strict) store of an undef is UB. -/
def undefVolatileStoreCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Undef .U64, .Alloca .U64 none none, .Store .U64 v1 v0 true none,
               .Const .U64 (.int 7)]
      terminator := .Return [v2] }

theorem undef_volatile_store_is_ub_stable :
    evalValuesStableOutcome (evalFunction undefVolatileStoreCFG b0 [] 1)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- The call boundary inspects: `f0() { %0 = undef i32; call f1(%0) }` with
    `f1` the i32 identity. -/
def undefCallArgFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := singletonCFG
      { params := []
        body := [.Undef .I32]
        terminator := .Call f1 [v0] }
    entryBlock := b0 }

/-- `f0() -> i32 { %0 = undef i32; ret %0 }`. -/
def undefReturnFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := singletonCFG
      { params := []
        body := [.Undef .I32]
        terminator := .Return [v0] }
    entryBlock := b0 }

def undefCallContext (entry : EvalFunction) : EvalContext :=
  { functions := functionMap [(f0, entry), (f1, i32IdentityFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

/-- Passing poison as a call argument is UB (mirror interpret.rs
    `check_signature_values`: poison crosses a call only through memory). -/
theorem undef_call_argument_is_ub_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (undefCallContext undefCallArgFunction) f0 [] 2)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- Returning poison is UB at the (entry) call boundary too. -/
theorem undef_return_is_ub_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (undefCallContext undefReturnFunction) f0 [] 2)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- The same boundary check covers a `.partial` image, which it did not before
    WS2.10 (Lean passed a poison load across a call; Rust refused it): here
    the poison is the ENTRY argument, refused before the body runs. -/
theorem partial_entry_argument_is_ub_stable :
    evalValuesStableOutcome
        (evalFunctionInContext directCallContext f0
          [.partial [some 1, none, none, none]] 2)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- Documented residue (not agreement): Lean binds an `.undef` of ANY type, so
    an unused non-scalar undef runs to completion here, while the Rust
    interpreter FAILS CLOSED on it ("undef of non-scalar type … aggregate
    poison unmodelled"). The engines disagree only by Rust refusing. -/
def undefTupleCFG : CFG :=
  singletonCFG
    { params := []
      body := [.Undef (.Tuple [.U64, .U64]), .Const .U64 (.int 7)]
      terminator := .Return [v1] }

theorem undef_tuple_unused_runs_in_lean_stable :
    evalValuesStableOutcome (evalFunction undefTupleCFG b0 [] 1)
        MachineState.empty =
      "ok:return:[int64:7]" := by
  native_decide

-- WS2.10 review: poison may not HIDE inside a defined value. Embedding an
-- element in an array inspects it (as `InsertField` already did), so a poison
-- lane can never ride an aggregate past a call/return boundary; and a
-- `CmpXchg` comparison inspects `expected`. Mirrors of interpret.rs
-- `eval_insert_element` / `Inst::CmpXchg` and undef_poison.rs.

def undefArrayInsertState (elem : Value) : MachineState :=
  stateWith [(v0, .aggregate [.int 64 1, .int 64 2]), (v1, .int 64 0), (v2, elem)] 3

/-- Negative: inserting an `undef` element into an array is UB. -/
theorem undef_insert_element_into_array_is_ub_stable :
    stepInstStableOutcome (.InsertElement (.Array (TyId.mk 0) 2) v0 v1 v2)
        (undefArrayInsertState (.undef .U64)) =
      "error:ub" := by
  native_decide

/-- The same for a `.partial` image (the pre-WS2.10 poison carrier). -/
theorem partial_insert_element_into_array_is_ub_stable :
    stepInstStableOutcome (.InsertElement (.Array (TyId.mk 0) 2) v0 v1 v2)
        (undefArrayInsertState (.partial [some 1, none, none, none, none, none, none, none])) =
      "error:ub" := by
  native_decide

/-- Mutation control: a defined element inserts normally. -/
theorem defined_insert_element_into_array_stable :
    stepInstStableOutcome (.InsertElement (.Array (TyId.mk 0) 2) v0 v1 v2)
        (undefArrayInsertState (.int 64 9)) =
      "ok:value:aggregate[int64:9,int64:2]" := by
  native_decide

/-- `%0 = alloca u64; %1 = 5; store %1, %0; %2 = <expected>; %3 = 9;
    %4 = cmpxchg %0, %2, %3; ret %1`. -/
def cmpxchgExpectedCFG (expected : Inst) : CFG :=
  singletonCFG
    { params := []
      body := [.Alloca .U64 none none, .Const .U64 (.int 5), .Store .U64 v0 v1 false none,
               expected, .Const .U64 (.int 9),
               .CmpXchg .U64 v0 v2 v3 .SeqCst .SeqCst false]
      terminator := .Return [v1] }

/-- Negative: a poison `expected` is UB, not a silent failed exchange. -/
theorem undef_cmpxchg_expected_is_ub_stable :
    evalValuesStableOutcome (evalFunction (cmpxchgExpectedCFG (.Undef .U64)) b0 [] 1)
        MachineState.empty =
      "error:ub" := by
  native_decide

/-- Mutation control: a defined (unequal) `expected` runs to completion. -/
theorem defined_cmpxchg_expected_stable :
    evalValuesStableOutcome
        (evalFunction (cmpxchgExpectedCFG (.Const .U64 (.int 4))) b0 [] 1)
        MachineState.empty =
      "ok:return:[int64:5]" := by
  native_decide

-- Load/Store alignment (mirror interpret.rs `checked_access`, commit dd27b78):
-- a non-atomic access under-aligned for its declared alignment is UB.

/-- A 16-byte cell whose first eight bytes are written. `v0` points at the base
    (address 1024, 8-aligned), `v1` at base+1 (address 1025, odd), and `v2`
    holds a byte value to store. -/
def alignTestState : MachineState :=
  let (base, mem) := Memory.empty.alloc 16 8 0 .rustStack   -- base = 1024
  let mem := mem.writeBytes base [10, 11, 12, 13, 14, 15, 16, 17]
  { (stateWith [(v0, .ptr base (some (AllocId.mk 0))), (v1, .ptr (base + 1) (some (AllocId.mk 0))), (v2, .int 8 99)] 3)
      with memory := mem }

/-- Observable outcome of a `semLoad` with the given declared alignment. -/
def alignLoadOutcome (ty : Ty) (ptrId : ValueId) (align : Option Nat) : String :=
  match Sem.run (do
      let id ← semLoad ty ptrId false align
      Sem.lookupValue id) alignTestState with
  | .ok (v, _) => "ok:" ++ stableValueString v
  | .error e   => "error:" ++ e.code

/-- An aligned in-bounds scalar load succeeds (address 1024 % 8 = 0). -/
theorem aligned_load_succeeds_stable :
    alignLoadOutcome .I8 v0 (some 8) = "ok:int8:10" := by native_decide

/-- An in-bounds but UNDER-aligned scalar load faults with `SemError.ub`
    (address 1025 % 8 ≠ 0). -/
theorem underaligned_load_is_ub_stable :
    alignLoadOutcome .I8 v1 (some 8) = "error:ub" := by native_decide

/-- `align 1` always succeeds (every address is 1-aligned). -/
theorem align_one_load_always_succeeds_stable :
    alignLoadOutcome .I8 v1 (some 1) = "ok:int8:11" := by native_decide

/-- Omitted alignment (`none`) imposes no constraint — the odd address loads. -/
theorem omitted_align_load_succeeds_stable :
    alignLoadOutcome .I8 v1 none = "ok:int8:11" := by native_decide

/-- End-to-end through `stepInst .Load`: the `align` field threaded by `Step`
    faults an under-aligned access, and passes an aligned one. -/
theorem step_load_underaligned_is_ub_stable :
    stepInstStableOutcome (.Load .I8 v1 false (some 8)) alignTestState
      = "error:ub" := by native_decide

theorem step_load_align_one_succeeds_stable :
    stepInstStableOutcome (.Load .I8 v1 false (some 1)) alignTestState
      = "ok:value:int8:11" := by native_decide

/-- Stores share the same gate: an under-aligned store is UB, an aligned one
    succeeds. -/
def alignStoreOutcome (ptrId : ValueId) (align : Option Nat) : String :=
  match Sem.run (semStore .I8 ptrId v2 false align) alignTestState with
  | .ok _    => "ok"
  | .error e => "error:" ++ e.code

theorem underaligned_store_is_ub_stable :
    alignStoreOutcome v1 (some 8) = "error:ub" := by native_decide

theorem aligned_store_succeeds_stable :
    alignStoreOutcome v0 (some 8) = "ok" := by native_decide

-- ==========================================================-- Enum InsertField lane 0 (roadmap WS2.2 item 2 / item 5 Lean mirror)
-- ==========================================================
/-- An enum value `a(7)` in the `[tag, fields..]` model: `[u8 0, u64 7]`,
    beside a u8 `1` (the tag of another variant) and a u64 `9`. -/
def enumLaneState : MachineState :=
  stateWith [(v0, .aggregate [.int 8 0, .int 64 7]), (v1, .int 8 1), (v2, .int 64 9)] 3

/-- insert_field lane 0 of an enum throws: rewriting the discriminant would
    leave `a`'s payload under `b`'s tag (partb c06 `p1_insert_tag_overwrite`,
    which the Rust interpreter used to run to `Ok 7`). -/
theorem insert_field_lane0_of_an_enum_throws_stable :
    stepInstStableOutcome (.InsertField (.Enum (EnumId.mk 0)) v0 0 v1) enumLaneState
      = "error:ub" := by native_decide

/-- Twin: the same enum, payload lane 1, is an ordinary write. -/
theorem insert_field_payload_lane_of_an_enum_succeeds_stable :
    stepInstStableOutcome (.InsertField (.Enum (EnumId.mk 0)) v0 1 v2) enumLaneState
      = "ok:value:aggregate[int8:0,int64:9]" := by native_decide

/-- Control: lane 0 of a NON-enum aggregate stays writable — the refusal is
    the enum's discriminant, not "field 0". -/
theorem insert_field_lane0_of_a_struct_succeeds_stable :
    stepInstStableOutcome (.InsertField (.Struct (StructId.mk 0)) v0 0 v1) enumLaneState
      = "ok:value:aggregate[int8:1,int64:7]" := by native_decide

/-- Reading the tag lane of an enum is ordinary. -/
theorem extract_field_tag_of_an_enum_succeeds_stable :
    stepInstStableOutcome (.ExtractField .U8 v0 0) enumLaneState
      = "ok:value:int8:0" := by native_decide

-- ==========================================================-- MakeAggregate (WS3.5): the register-level aggregate seed
-- ==========================================================
/-- A struct built from two register lanes is exactly the `[lane0, lane1]`
    aggregate `Const` would produce. -/
theorem make_aggregate_struct_builds_its_lanes_stable :
    stepInstStableOutcome
        (.MakeAggregate (.Struct (StructId.mk 0)) none [v1, v2]) enumLaneState
      = "ok:value:aggregate[int8:1,int64:9]" := by native_decide

/-- A fieldless tuple is the empty aggregate, and `variant` is absent. -/
theorem make_aggregate_empty_tuple_stable :
    stepInstStableOutcome (.MakeAggregate (.Tuple []) none []) enumLaneState
      = "ok:value:aggregate[]" := by native_decide

/-- Honest partial: an enum construction needs `discriminants[variant]`, a
    module-table fact the executable model does not carry — it fails closed
    as `unsupported.enum_def_table` rather than fabricate a tag lane. -/
theorem make_aggregate_enum_is_unsupported_stable :
    stepInstStableOutcome
        (.MakeAggregate (.Enum (EnumId.mk 0)) (some 1) [v2]) enumLaneState
      = "error:unsupported.enum_def_table" := by native_decide

/-- A `variant` clause on a struct is a type error (the validator's
    `InvalidMakeAggregate`), and so is a scalar type. -/
theorem make_aggregate_variant_on_struct_is_type_error_stable :
    stepInstStableOutcome
        (.MakeAggregate (.Struct (StructId.mk 0)) (some 0) [v1, v2]) enumLaneState
      = "error:type_error" := by native_decide

theorem make_aggregate_scalar_is_type_error_stable :
    stepInstStableOutcome (.MakeAggregate .I64 none [v2]) enumLaneState
      = "error:type_error" := by native_decide

/-- A poison lane is UB: the result is fully initialised by definition. -/
theorem make_aggregate_poison_lane_is_ub_stable :
    stepInstStableOutcome
        (.MakeAggregate (.Tuple [.I64]) none [v0])
        (stateWith [(v0, .partial [none])] 1)
      = "error:ub" := by native_decide

-- ==========================================================-- ArraySplat / Constant.splat (v50): n copies of one value
-- ==========================================================
/-- `[v; 3]` is one uniform node containing the original register value.
    (A fixture length is small; the law `extract_array_splat` is for every
    `n`, and the Rust interpreter's value is O(1) in `n`.) -/
theorem array_splat_builds_n_copies_stable :
    stepInstStableOutcome (.ArraySplat (.Array (TyId.mk 0) 3) v2) enumLaneState
      = "ok:value:array:uniform(3;int64:9)" := by native_decide

/-- Zero copies is the empty array (canonically spelled `make_aggregate`, but
    the semantics of the non-canonical spelling is still the empty value). -/
theorem array_splat_zero_copies_stable :
    stepInstStableOutcome (.ArraySplat (.Array (TyId.mk 0) 0) v2) enumLaneState
      = "ok:value:array:uniform(0)" := by native_decide

/-- A type that is not an array is a type error (the validator's
    `InvalidArraySplat`). -/
theorem array_splat_scalar_is_type_error_stable :
    stepInstStableOutcome (.ArraySplat .I64 v2) enumLaneState
      = "error:type_error" := by native_decide

/-- A poison element is UB: embedding it inspects it. -/
theorem array_splat_poison_is_ub_stable :
    stepInstStableOutcome (.ArraySplat (.Array (TyId.mk 0) 2) v0)
        (stateWith [(v0, .partial [none])] 1)
      = "error:ub" := by native_decide

/-- The constant twin: `splat[ 5; 3 ]` materializes the same replicated
    aggregate a `Const` of `array[ 5, 5, 5 ]` would (the §3 rule makes the
    splat the one spelling of it). -/
theorem const_splat_materializes_n_copies_stable :
    stepInstStableOutcome (.Const (.Array (TyId.mk 0) 3) (.splat (.int 5) 3)) enumLaneState
      = stepInstStableOutcome (.Const (.Array (TyId.mk 0) 3) (.array [.int 5, .int 5, .int 5]))
          enumLaneState := by native_decide

-- ==========================================================-- Multi-result binding (WS2.24): `Overflow` / `CmpXchg` bind TWO SSA
-- destinations positionally, exactly as the Rust reference interpreter binds
-- `InstrNode.results` (interpret.rs `bind_results`). There is no packed
-- aggregate form. Lean `Value.int` carries the two's-complement residue, so
-- i8 `-128` renders as `int8:128`.
-- ==========================================================
/-- Single-instruction view: `add_overflow i8 127, 1` yields two separate
    values, the wrapped result (`-128`) and the overflow flag (`true`). -/
theorem overflow_step_yields_two_values_stable :
    stepInstStableOutcome (.Overflow .AddOverflow .I8 v0 v1)
        (stateWith [(v0, .int 8 127), (v1, .int 8 1)] 2) =
      "ok:values:[int8:128,bool:true]" := by
  native_decide

/-- Single-instruction view of CmpXchg over a pre-initialized cell: two
    separate values, the old contents and the success flag. -/
theorem cmpxchg_step_yields_two_values_stable :
    stepThreeInstStableOutcome (.Alloca .I32 none none)
        (.Store .I32 (ValueId.mk 2) v0 false none)
        (.CmpXchg .I32 (ValueId.mk 2) v0 v1 .SeqCst .SeqCst false)
        (stateWith [(v0, .int 32 5), (v1, .int 32 9)] 2) =
      "ok:values:[int32:5,bool:true]" := by
  native_decide

/-- A one-function context over `cfg` (entry `b0`, the given signature). -/
def multiResultContext (paramTys returnTys : List Ty) (cfg : CFG) : EvalContext :=
  { functions := functionMap
      [(f0, { body := { paramTys := paramTys, returnTys := returnTys }
              cfg := cfg
              entryBlock := b0 })]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

/-- Outcome with the FULL error (code and detail), so a refusal is asserted by
    its named reason rather than by its code alone. -/
def evalValuesDetailedOutcome (m : Sem (List Value)) (state : MachineState) :
    String :=
  match Sem.run m state with
  | .ok (values, _) => "ok:return:" ++ stableValueListString values
  | .error err => "error:" ++ err.stable

/-- `%v, %o = add_overflow i8 %a, %b; return %v, %o`, with the node's result
    destinations given explicitly (`dests`), as a Rust two-result node. -/
def overflowNodeCFG (dests : List ValueId) : CFG :=
  singletonCFG
    { params := [(v0, .I8), (v1, .I8)]
      body := [.Overflow .AddOverflow .I8 v0 v1]
      bodyResultDests := [dests]
      terminator := .Return [v2, v3] }

def overflowNodeOutcome (dests : List ValueId) (a b : Int) : String :=
  evalValuesDetailedOutcome
    (evalFunctionInContext
      (multiResultContext [.I8, .I8] [.I8, .Bool] (overflowNodeCFG dests))
      f0 [.int 8 a, .int 8 b] 4)
    MachineState.empty

/-- POSITIVE (WS2.24): the Rust-shaped node `%v, %o = add_overflow i8 127, 1`
    binds `%v = -128` and `%o = true` — each destination holds its own
    component, no aggregate projection. -/
theorem overflow_binds_two_destinations_positionally_stable :
    overflowNodeOutcome [v2, v3] 127 1 = "ok:return:[int8:128,bool:true]" := by
  native_decide

/-- NEGATIVE TWIN: the same node with ONE destination is refused with the
    result-count TypeError (Rust: `MalformedInstruction` "instruction result
    arity mismatch"), never silently bound to the first component. -/
theorem overflow_one_destination_is_count_mismatch_stable :
    overflowNodeOutcome [v2] 127 1 =
      "error:type_error:instruction result count mismatch" := by
  native_decide

/-- Twin: three destinations are the same refusal (arity is exact). -/
theorem overflow_three_destinations_is_count_mismatch_stable :
    overflowNodeOutcome [v2, v3, ValueId.mk 4] 127 1 =
      "error:type_error:instruction result count mismatch" := by
  native_decide

/-- Twin: an absent destination row is ALSO refused — a multi-result node has
    no historical fresh-result convention to fall back on. -/
theorem overflow_no_destination_row_is_count_mismatch_stable :
    overflowNodeOutcome [] 127 1 =
      "error:type_error:instruction result count mismatch" := by
  native_decide

/-- MUTATION CONTROL: swapping the two destinations swaps what the SAME
    `return %v2, %v3` observes. An order-insensitive binder (or one that bound
    the components by type) would return the positive fixture's string here. -/
theorem overflow_swapped_destinations_swap_the_components_stable :
    overflowNodeOutcome [v3, v2] 127 1 = "ok:return:[bool:true,int8:128]" := by
  native_decide

/-- Control: a non-overflowing add still binds two components (flag false),
    so the positive fixture's `true` is the operands', not the binder's. -/
theorem overflow_no_overflow_binds_false_flag_stable :
    overflowNodeOutcome [v2, v3] 100 1 = "ok:return:[int8:101,bool:false]" := by
  native_decide

/-- `%p = alloca i32; store %init, %p; %old, %ok = cmpxchg %p, %exp, %new;
    %now = load %p; return %old, %ok, %now` with explicit destinations. -/
def cmpXchgNodeCFG (dests : List ValueId) : CFG :=
  singletonCFG
    { params := [(v0, .I32), (v1, .I32), (v2, .I32)]
      body := [.Alloca .I32 none none,
               .Store .I32 v3 v0 false none,
               .CmpXchg .I32 v3 v1 v2 .SeqCst .SeqCst false,
               .Load .I32 v3 false none]
      bodyResultDests := [[v3], [], dests, [ValueId.mk 6]]
      terminator := .Return [ValueId.mk 4, ValueId.mk 5, ValueId.mk 6] }

def cmpXchgNodeOutcome (dests : List ValueId) (init expected desired : Int) :
    String :=
  evalValuesDetailedOutcome
    (evalFunctionInContext
      (multiResultContext [.I32, .I32, .I32] [.I32, .Bool, .I32]
        (cmpXchgNodeCFG dests))
      f0 [.int 32 init, .int 32 expected, .int 32 desired] 8)
    MachineState.empty

/-- POSITIVE: a successful cmpxchg binds `%old = 5`, `%ok = true` to its two
    destinations, and memory now holds the desired `9`. -/
theorem cmpxchg_success_binds_two_destinations_stable :
    cmpXchgNodeOutcome [ValueId.mk 4, ValueId.mk 5] 5 5 9 =
      "ok:return:[int32:5,bool:true,int32:9]" := by
  native_decide

/-- A failing cmpxchg binds `%old = 5`, `%ok = false`; memory is unchanged. -/
theorem cmpxchg_failure_binds_old_and_false_stable :
    cmpXchgNodeOutcome [ValueId.mk 4, ValueId.mk 5] 5 7 9 =
      "ok:return:[int32:5,bool:false,int32:5]" := by
  native_decide

/-- NEGATIVE TWIN: one destination is the result-count TypeError. -/
theorem cmpxchg_one_destination_is_count_mismatch_stable :
    cmpXchgNodeOutcome [ValueId.mk 4] 5 5 9 =
      "error:type_error:instruction result count mismatch" := by
  native_decide

/-- MUTATION CONTROL: swapped destinations swap the observed components. -/
theorem cmpxchg_swapped_destinations_swap_the_components_stable :
    cmpXchgNodeOutcome [ValueId.mk 5, ValueId.mk 4] 5 5 9 =
      "ok:return:[bool:true,int32:5,int32:9]" := by
  native_decide

-- -----------------------------------------------------------------
-- WS2.24 review: adversarial multi-result shapes.
-- -----------------------------------------------------------------

/-- `%v, %o = add_overflow i8 %a, %b` bound to `dests`, then `return ret`. -/
def overflowReturnCFG (dests ret : List ValueId) : CFG :=
  singletonCFG
    { params := [(v0, .I8), (v1, .I8)]
      body := [.Overflow .AddOverflow .I8 v0 v1]
      bodyResultDests := [dests]
      terminator := .Return ret }

def overflowReturnOutcome (dests ret : List ValueId) (a b : Int) : String :=
  evalValuesDetailedOutcome
    (evalFunctionInContext
      (multiResultContext [.I8, .I8] [.I8, .Bool] (overflowReturnCFG dests ret))
      f0 [.int 8 a, .int 8 b] 4)
    MachineState.empty

/-- NON-ADJACENT destinations: the positive fixture's `[%2, %3]` coincide with
    the fresh ids the instruction binds, so a binder that IGNORED the node's
    destinations would still pass it. `[%7, %5]` do not coincide: each lands
    on its own declared name. -/
theorem overflow_binds_non_adjacent_destinations_stable :
    overflowReturnOutcome [ValueId.mk 7, ValueId.mk 5] [ValueId.mk 7, ValueId.mk 5]
        127 1 = "ok:return:[int8:128,bool:true]" := by
  native_decide

/-- The node defines EXACTLY its destinations: the fresh component ids are
    retired, so reading `%2` / `%3` after binding `[%7, %5]` is the same
    undefined-value error Rust's interpreter raises (it has no temporaries).
    Before the retirement this returned the stale `[int8:128,bool:true]`. -/
theorem overflow_fresh_component_ids_are_not_defined_stable :
    overflowReturnOutcome [ValueId.mk 7, ValueId.mk 5] [v2, v3] 127 1 =
      "error:type_error:undefined SSA value: { index := 2 }" := by
  native_decide

/-- The overflow FLAG is a first-class `Bool` SSA value: it drives a `CondBr`
    directly (the retired packed aggregate could not — branching on it was a
    type error). Overflow takes the `then` edge (returns the lhs); no overflow
    takes the `else` edge carrying the wrapped sum. -/
def overflowBranchCFG : CFG := fun bid =>
  if bid.index == 0 then
    some { params := [(v0, .I8), (v1, .I8)]
           body := [.Overflow .AddOverflow .I8 v0 v1]
           bodyResultDests := [[v2, v3]]
           terminator := .CondBr v3 b1 [] b2 [v2] }
  else if bid.index == 1 then
    some { params := [], body := [], terminator := .Return [v0] }
  else if bid.index == 2 then
    some { params := [(ValueId.mk 4, .I8)], body := []
           terminator := .Return [ValueId.mk 4] }
  else none

def overflowBranchOutcome (a b : Int) : String :=
  evalValuesDetailedOutcome
    (evalFunctionInContext (multiResultContext [.I8, .I8] [.I8] overflowBranchCFG)
      f0 [.int 8 a, .int 8 b] 8)
    MachineState.empty

theorem overflow_flag_drives_condbr_taken_stable :
    overflowBranchOutcome 127 1 = "ok:return:[int8:127]" := by
  native_decide

theorem overflow_flag_drives_condbr_not_taken_stable :
    overflowBranchOutcome 100 1 = "ok:return:[int8:101]" := by
  native_decide

/-- A consumer of the RETIRED packed form (`extractvalue %v, 1`) is refused:
    `%v` is the wrapped integer, not an aggregate carrying the flag. -/
def overflowExtractCFG : CFG :=
  singletonCFG
    { params := [(v0, .I8), (v1, .I8)]
      body := [.Overflow .AddOverflow .I8 v0 v1, .ExtractField .Bool v2 1]
      bodyResultDests := [[v2, v3], [ValueId.mk 4]]
      terminator := .Return [ValueId.mk 4] }

theorem overflow_packed_form_projection_is_refused_stable :
    evalValuesDetailedOutcome
        (evalFunctionInContext (multiResultContext [.I8, .I8] [.Bool] overflowExtractCFG)
          f0 [.int 8 127, .int 8 1] 4)
        MachineState.empty =
      "error:type_error:ExtractField: operand is not an aggregate" := by
  native_decide

/-- Component ORDER for the other overflow ops (value first, flag second),
    at the residue boundary: `sub_overflow u8 0, 1` wraps to 255 and
    overflows; `mul_overflow i8 -128, -1` wraps to -128 (residue 128) and
    overflows. -/
theorem sub_overflow_u8_binds_value_then_flag_stable :
    stepInstStableOutcome (.Overflow .SubOverflow .U8 v0 v1)
        (stateWith [(v0, .int 8 0), (v1, .int 8 1)] 2) =
      "ok:values:[int8:255,bool:true]" := by
  native_decide

theorem mul_overflow_i8_min_times_neg_one_binds_value_then_flag_stable :
    stepInstStableOutcome (.Overflow .MulOverflow .I8 v0 v1)
        (stateWith [(v0, .int 8 128), (v1, .int 8 255)] 2) =
      "ok:values:[int8:128,bool:true]" := by
  native_decide

/-- CmpXchg twins the implementer's quartet did not cover: an ABSENT row and
    THREE destinations are the same named refusal. -/
theorem cmpxchg_no_destination_row_is_count_mismatch_stable :
    cmpXchgNodeOutcome [] 5 5 9 =
      "error:type_error:instruction result count mismatch" := by
  native_decide

theorem cmpxchg_three_destinations_is_count_mismatch_stable :
    cmpXchgNodeOutcome [ValueId.mk 4, ValueId.mk 5, ValueId.mk 7] 5 5 9 =
      "error:type_error:instruction result count mismatch" := by
  native_decide

-- ---------------------------------------------------------------------------
-- WS2.19 audit: an access at a type with no modelled byte image is
-- `unsupported.layout`, never a type error
-- ---------------------------------------------------------------------------
--
-- The Lean-execution oracle (`lean_exec_differential.rs`) reads a
-- `type_error` on a validator-accepted module as a DISAGREEMENT with the
-- validator, and an `unsupported` refusal as coverage it counts. Every
-- "type has no byte size" site — `Alloca`, `HeapAlloc`, `Load`, `Store`,
-- `GEP`, the four atomics, `GlobalAddr` and the `SeqMap` element type —
-- used to be a type error, so a whole-aggregate memory access (a `Struct` /
-- `Array` / `Tuple` / `Enum` the model has no layout table for) counted as a
-- disagreement. These fixtures pin the reclassification AND its boundary:
-- the refusal is about the TYPE's byte image only; a real UB at a modelled
-- type (null dereference, non-positive count, negative GEP index) is still UB.

def structTy : Ty := .Struct (StructId.mk 0)

theorem alloca_struct_is_unsupported_layout_stable :
    stepInstStableOutcome (.Alloca structTy none none) (stateWith [] 0) =
      "error:unsupported.layout" := by
  native_decide

theorem heap_alloc_array_is_unsupported_layout_stable :
    stepInstStableOutcome (.HeapAlloc (.Array (TyId.mk 0) 4) none none .RustHeap)
      (stateWith [] 0) = "error:unsupported.layout" := by
  native_decide

theorem alloca_tuple_is_unsupported_layout_stable :
    stepInstStableOutcome (.Alloca (.Tuple [.I32, .Bool]) none none) (stateWith [] 0) =
      "error:unsupported.layout" := by
  native_decide

/-- The boundary, allocation side: a non-positive count at a MODELLED type
    is still UB (the count check is not reached for an unmodelled type — the
    type gate comes first — so the two refusals never overlap). -/
theorem alloca_i32_zero_count_is_still_ub_stable :
    stepTypedInstStableOutcome [(v0, .I64)] (.Alloca .I32 (some v0) none)
      (stateWith [(v0, .int 64 0)] 1) = "error:ub" := by
  native_decide

/-- A provenance pointer (the access type is refused before its allocation is
    looked up, so none need exist). -/
def structPtrState : MachineState :=
  stateWith [(v0, .ptr 4096 (some (AllocId.mk 0))), (v1, .aggregate [.int 32 1, .bool true]),
    (v2, .int 64 1)] 3

theorem load_struct_is_unsupported_layout_stable :
    stepInstStableOutcome (.Load structTy v0 false none) structPtrState =
      "error:unsupported.layout" := by
  native_decide

theorem store_struct_is_unsupported_layout_stable :
    stepInstStableOutcome (.Store structTy v0 v1 false none) structPtrState =
      "error:unsupported.layout" := by
  native_decide

theorem gep_struct_pointee_is_unsupported_layout_stable :
    stepInstStableOutcome (.GEP structTy v0 [v2] true) structPtrState =
      "error:unsupported.layout" := by
  native_decide

theorem atomic_load_enum_is_unsupported_layout_stable :
    stepInstStableOutcome (.AtomicLoad (.Enum (EnumId.mk 0)) v0 .SeqCst) structPtrState =
      "error:unsupported.layout" := by
  native_decide

def nullStructPtrState : MachineState :=
  stateWith [(v0, .nullPtr), (v1, .int 32 1), (v2, .int 64 (-1))] 3

/-- The boundary, access side: a null dereference at a MODELLED type is UB,
    and a null dereference at an UNMODELLED type is UB too — the pointer
    check precedes the byte-image check, so reclassifying the latter did not
    demote a real fault. -/
theorem load_i32_null_is_still_ub_stable :
    stepInstStableOutcome (.Load .I32 v0 false none) nullStructPtrState =
      "error:ub" := by
  native_decide

theorem load_struct_null_is_still_ub_stable :
    stepInstStableOutcome (.Load structTy v0 false none) nullStructPtrState =
      "error:ub" := by
  native_decide

def negativeGepState : MachineState :=
  stateWith [(v0, .ptr 4096 none), (v2, .int 64 (-1))] 3

theorem gep_i32_negative_index_is_still_ub_stable :
    stepTypedInstStableOutcome [(v2, .I64)] (.GEP .I32 v0 [v2] true) negativeGepState =
      "error:ub" := by
  native_decide

/-- Mutation control: the same GEP at the unmodelled pointee with the same
    negative index is the LAYOUT refusal — the byte-image gate is checked
    before the index sign, so the classification is decided by the type. -/
theorem gep_struct_negative_index_is_unsupported_layout_stable :
    stepInstStableOutcome (.GEP structTy v0 [v2] true) negativeGepState =
      "error:unsupported.layout" := by
  native_decide

-- ---------------------------------------------------------------------------
-- WS2.19: the module-context evaluator — definition-table constant lowering,
-- the ExtractField lane check, and the declared-callee refusal
-- ---------------------------------------------------------------------------
--
-- Each divergence the W5b oracle measured between this model and the
-- reference interpreter is pinned here beside its twin, so the fix cannot
-- drift and its boundary is stated: the refusal is keyed on what the context
-- CARRIES (a definition table, a declaration), and the UB is keyed on a
-- lane-type disagreement a VALID aggregate cannot produce.

/-- The W5a generator's `GenE`: `enum E { a(i32, bool), b(u64), c }`,
    discriminants 0, 1, 2, so the canonical tag is `u8`. -/
def ws219Enum : EnumDef :=
  { id := EnumId.mk 0, name := "E",
    variants := [{ name := "a", fields := [.I32, .Bool] },
                 { name := "b", fields := [.U64] },
                 { name := "c", fields := [] }] }

/-- `struct S { x: i8, y: i16 }`. -/
def ws219Struct : StructDef :=
  { id := StructId.mk 0, name := "S",
    fields := [{ name := "x", ty := .I8, offset := none },
               { name := "y", ty := .I16, offset := none }],
    size := none, align := none }

/-- `v0 = Const ty c; v1 = ExtractField accessTy v0 lane; return v1`. -/
def ws219ConstExtract (ty : Ty) (c : Constant) (accessTy : Ty) (lane : Nat) : EvalFunction :=
  { body := { paramTys := [], returnTys := [accessTy] }
    cfg := singletonCFG
      { params := []
        body := [.Const ty c, .ExtractField accessTy v0 lane]
        terminator := .Return [v1] }
    entryBlock := b0 }

/-- A context carrying the enum, struct and type tables (`TyId 0` is `i16`). -/
def ws219Tables (f : EvalFunction) : EvalContext :=
  { functions := functionMap [(f0, f)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none
    enums := fun e => if e.index == 0 then some ws219Enum else none
    structs := fun s => if s.index == 0 then some ws219Struct else none
    types := fun t => if t.index == 0 then some .I16 else none }

/-- The same context WITHOUT any definition table. -/
def ws219NoTables (f : EvalFunction) : EvalContext :=
  { functions := functionMap [(f0, f)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

def ws219Run (ctx : EvalContext) : String :=
  evalValuesStableOutcome (evalFunctionInContext ctx f0 [] 4) MachineState.empty

def enumA : Constant := .aggregate [.int 0, .int 5, .bool true]
def enumB : Constant := .aggregate [.int 1, .int 7]

/-- Positive: an active-variant lane is read at its declared width. -/
theorem ws219_enum_active_lane_is_typed_stable :
    ws219Run (ws219Tables (ws219ConstExtract (.Enum (EnumId.mk 0)) enumA .I32 1)) =
      "ok:return:[int32:5]" := by
  native_decide

/-- The tag lane is the canonical `u8`, not the 64-bit default. -/
theorem ws219_enum_tag_lane_is_canonical_stable :
    ws219Run (ws219Tables (ws219ConstExtract (.Enum (EnumId.mk 0)) enumB .U8 0)) =
      "ok:return:[int8:1]" := by
  native_decide

/-- Negative twin (the oracle's first enum divergence): lane 1 of the ACTIVE
    variant `b` is `u64`, so reading it at `i32` is the interpreter's
    "lane 1 belongs to no field of active variant b" UB. -/
theorem ws219_enum_wrong_variant_lane_is_ub_stable :
    ws219Run (ws219Tables (ws219ConstExtract (.Enum (EnumId.mk 0)) enumB .I32 1)) =
      "error:ub" := by
  native_decide

/-- And the converse width: lane 1 of `a` is `i32`, read at `u64`. -/
theorem ws219_enum_wrong_variant_wider_lane_is_ub_stable :
    ws219Run (ws219Tables (ws219ConstExtract (.Enum (EnumId.mk 0)) enumA .U64 1)) =
      "error:ub" := by
  native_decide

/-- Fail closed without the table: the constant is REFUSED by name, never
    lowered at the 64-bit default (which the lane check would then misread
    as a wrong-variant UB). -/
theorem ws219_enum_without_table_is_unsupported_stable :
    ws219Run (ws219NoTables (ws219ConstExtract (.Enum (EnumId.mk 0)) enumA .I32 1)) =
      "error:unsupported.enum_def_table" := by
  native_decide

/-- A struct constant's lanes take the declared field widths. -/
theorem ws219_struct_lane_is_typed_stable :
    ws219Run (ws219Tables
        (ws219ConstExtract (.Struct (StructId.mk 0)) (.aggregate [.int 3, .int 300]) .I16 1)) =
      "ok:return:[int16:300]" := by
  native_decide

theorem ws219_struct_without_table_is_unsupported_stable :
    ws219Run (ws219NoTables
        (ws219ConstExtract (.Struct (StructId.mk 0)) (.aggregate [.int 3, .int 300]) .I16 1)) =
      "error:unsupported.enum_def_table" := by
  native_decide

/-- A tuple constant's integer lanes take their element widths (they kept
    the 64-bit default before WS2.19 — the oracle's `values differ: rust
    int8 vs lean int64`). -/
theorem ws219_tuple_lane_is_typed_stable :
    ws219Run (ws219NoTables
        (ws219ConstExtract (.Tuple [.I8, .Bool]) (.aggregate [.int 2, .bool true]) .I8 0)) =
      "ok:return:[int8:2]" := by
  native_decide

/-- `v0 = Const ty c; v1 = Const valTy val; v2 = InsertField ty v0 lane v1;
    v3 = ExtractField valTy v2 lane; return v3`. -/
def ws219ConstInsert (ty : Ty) (c : Constant) (valTy : Ty) (val : Constant) (lane : Nat) :
    EvalFunction :=
  { body := { paramTys := [], returnTys := [valTy] }
    cfg := singletonCFG
      { params := []
        body := [.Const ty c, .Const valTy val, .InsertField ty v0 lane v1,
                 .ExtractField valTy v2 lane]
        terminator := .Return [v3] }
    entryBlock := b0 }

/-- Positive: a write of the ACTIVE variant's lane type round-trips. -/
theorem ws219_enum_active_lane_insert_stable :
    ws219Run (ws219Tables
        (ws219ConstInsert (.Enum (EnumId.mk 0)) enumB .U64 (.int 9) 1)) =
      "ok:return:[int64:9]" := by
  native_decide

/-- Negative twin (the oracle's last enum divergence): writing an `i32` into
    lane 1 of the active variant `b` (a `u64` lane) is the interpreter's
    wrong-variant UB, for a write as for a read. -/
theorem ws219_enum_wrong_variant_insert_is_ub_stable :
    ws219Run (ws219Tables
        (ws219ConstInsert (.Enum (EnumId.mk 0)) enumB .I32 (.int 9) 1)) =
      "error:ub" := by
  native_decide

/-- Control: a struct lane write at the declared field type is untouched by
    the check. -/
theorem ws219_struct_lane_insert_stable :
    ws219Run (ws219Tables
        (ws219ConstInsert (.Struct (StructId.mk 0)) (.aggregate [.int 3, .int 300]) .I16
          (.int 301) 1)) =
      "ok:return:[int16:301]" := by
  native_decide

/-- Derive fixture declarations from the actual block parameters and result
    destinations, using the same source classifier as ordinary decoded bodies. -/
private def fixtureLocalTypes (block : BasicBlock) : Option LocalTypeTable :=
  match inferLocalTypes (fun _ => none) (fun _ => none) block.params
      (bodyInstsWithResultDests block.body block.bodyResultDests ++
        [(block.terminator, block.terminatorResultDests)]) with
  | .ok table => some table
  | .error _ => none

/-- Context-directed array constant evaluation, with a scalar result so the
    element's declared width is observed independently of the container. -/
def typedArrayConstant (c : Constant) : EvalFunction :=
  let block : BasicBlock :=
    { params := []
      body := [.Const (.Array (TyId.mk 0) 2) c,
               .Const .I64 (.int 1), .ExtractElement .I16 v0 v1]
      bodyResultDests := [[v0], [v1], [v2]]
      terminator := .Return [v2] }
  { body := { paramTys := [], returnTys := [.I16] }
    cfg := singletonCFG block
    entryBlock := b0
    localTypes := fixtureLocalTypes block }

theorem typed_array_splat_keeps_element_width :
    ws219Run (ws219Tables (typedArrayConstant (.splat (.int 300) 2))) =
      "ok:return:[int16:300]" := by native_decide

theorem typed_legacy_array_keeps_element_width :
    ws219Run (ws219Tables (typedArrayConstant (.aggregate [.int 1, .int 300]))) =
      "ok:return:[int16:300]" := by native_decide

theorem typed_array_splat_refuses_wrong_length :
    ws219Run (ws219Tables (typedArrayConstant (.splat (.int 300) 3))) =
      "error:type_error" := by native_decide

theorem typed_legacy_array_refuses_wrong_length :
    ws219Run (ws219Tables (typedArrayConstant (.aggregate [.int 300]))) =
      "error:type_error" := by native_decide

theorem typed_array_splat_refuses_missing_type_table :
    ws219Run (ws219NoTables (typedArrayConstant (.splat (.int 300) 2))) =
      "error:unsupported.enum_def_table" := by native_decide

theorem typed_array_splat_retains_link_time_refusal :
    ws219Run (ws219Tables
      (typedArrayConstant (.splat (.symbolAddr "unknown" 0) 2))) =
      "error:unsupported.link_time_address" := by native_decide

/-- Refusal controls at the actual recursive closure boundary. Production
    checking derives fuel from each value tree; explicit low-fuel calls below
    check the existing internal refusal rather than changing its policy. -/
def captureBoundaryContext : EvalContext :=
  { EvalContext.empty with
    types := (fun id => if id.index == 0 then some .I8 else none)
    records := (fun id => if id.index == 7 then
      some { id := ⟨7⟩, name := "R", fields := [{ name := "a", ty := .I8, offset := none }] }
      else none)
    enums := (fun id => if id.index == 0 then
      some { id := ⟨0⟩
             name := "E"
             variants := [{ name := "Data", fields := [.I8] }, { name := "Empty", fields := [] }]
             discriminants := [some (-1), some 42]
             tagRepr := some .i8 }
      else none) }

def captureBoundaryCode (result : Except SemError Unit) : String :=
  match result with
  | .ok _ => "ok"
  | .error error => error.code

theorem closure_half_member_is_admitted :
    captureBoundaryCode (checkClosureValue captureBoundaryContext .F16 (.float 1.5)) =
      "ok" := by native_decide

theorem closure_half_nonmember_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext .F16 (.float 0.1)) =
      "type_error" := by native_decide

theorem closure_vector_wrong_census_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Vector 2 .I8) (.vector [.int 8 7])) = "type_error" := by native_decide

theorem closure_zero_lane_vector_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Vector 0 .I8) (.vector [])) = "type_error" := by native_decide

theorem closure_record_wrong_label_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Record ⟨7⟩) (.record [("other", .int 8 7)])) = "type_error" := by native_decide

theorem closure_sequence_missing_element_definition_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Sequence ⟨99⟩) (.sequence [])) = "unsupported.enum_def_table" := by native_decide

theorem closure_record_missing_definition_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Record ⟨99⟩) (.record [])) = "unsupported.enum_def_table" := by native_decide

theorem closure_enum_missing_definition_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Enum ⟨99⟩) (.aggregate [.int 8 42])) = "unsupported.enum_def_table" := by native_decide

theorem closure_nested_negative_residue_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Sequence ⟨0⟩) (.sequence [.int 8 (-1)])) = "type_error" := by native_decide

theorem closure_nested_overflowing_residue_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Record ⟨7⟩) (.record [("a", .int 8 256)])) = "type_error" := by native_decide

theorem closure_untrusted_huge_width_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      .I8 (.int 1000000000 0)) = "type_error" := by native_decide

theorem closure_signed_enum_residue_is_admitted :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Enum ⟨0⟩) (.aggregate [.int 8 255, .int 8 7])) = "ok" := by native_decide

theorem closure_enum_wrong_tag_width_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Enum ⟨0⟩) (.aggregate [.int 16 255, .int 8 7])) = "type_error" := by native_decide

theorem closure_enum_unknown_discriminant_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Enum ⟨0⟩) (.aggregate [.int 8 4])) = "type_error" := by native_decide

theorem closure_enum_inactive_payload_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Enum ⟨0⟩) (.aggregate [.int 8 42, .int 8 7])) = "type_error" := by native_decide

theorem closure_nested_uninit_refuses :
    captureBoundaryCode (checkClosureValue captureBoundaryContext
      (.Record ⟨7⟩) (.record [("a", .uninit)])) = "ub" := by native_decide

theorem closure_sequence_internal_fuel_refusal :
    captureBoundaryCode (checkClosureValueAt captureBoundaryContext 1
      (.Sequence ⟨0⟩) (.sequence [.int 8 7])) = "unsupported.closure_def_table" := by native_decide

theorem closure_enum_tag_consumes_child_fuel :
    captureBoundaryCode (checkClosureValueAt captureBoundaryContext 1
      (.Enum ⟨0⟩) (.aggregate [.int 8 42])) = "unsupported.closure_def_table" := by native_decide

/-- The complete Const dispatch refuses missing container definitions even
    when the value is discarded, before binding a default-width value. -/
def containerConstantDiscard (ty : Ty) (c : Constant) : EvalFunction :=
  { body := { paramTys := [], returnTys := [] }
    cfg := singletonCFG { params := [], body := [.Const ty c], terminator := .Return [] }
    entryBlock := b0 }

theorem sequence_constant_without_element_table_refuses :
    ws219Run (ws219NoTables
      (containerConstantDiscard (.Sequence ⟨0⟩) (.sequence [.int 1]))) =
      "error:unsupported.enum_def_table" := by native_decide

theorem set_constant_without_element_table_refuses :
    ws219Run (ws219NoTables
      (containerConstantDiscard (.Set ⟨0⟩ .Boxed) (.set [.int 1]))) =
      "error:unsupported.enum_def_table" := by native_decide

theorem record_constant_without_definition_refuses :
    ws219Run (ws219NoTables
      (containerConstantDiscard (.Record ⟨0⟩) (.record [("a", .int 1)]))) =
      "error:unsupported.enum_def_table" := by native_decide

theorem positional_record_without_definition_refuses :
    ws219Run (ws219NoTables
      (containerConstantDiscard (.Record ⟨0⟩) (.aggregate [.int 1]))) =
      "error:unsupported.enum_def_table" := by native_decide

theorem sequence_constant_retains_link_time_refusal_priority :
    ws219Run (ws219NoTables
      (containerConstantDiscard (.Sequence ⟨0⟩) (.sequence [.symbolAddr "unknown" 0]))) =
      "error:unsupported.link_time_address" := by native_decide

/-- An array literal's elements take the element type the type table names. -/

def ws219ArrayElement : EvalFunction :=
  let block : BasicBlock :=
    { params := []
      body := [.Const (.Array (TyId.mk 0) 2) (.array [.int 1, .int 2]),
               .Const .I64 (.int 1), .ExtractElement .I16 v0 v1]
      bodyResultDests := [[v0], [v1], [v2]]
      terminator := .Return [v2] }
  { body := { paramTys := [], returnTys := [.I16] }
    cfg := singletonCFG block
    entryBlock := b0
    localTypes := fixtureLocalTypes block }

theorem ws219_array_element_is_typed_stable :
    ws219Run (ws219Tables ws219ArrayElement) = "ok:return:[int16:2]" := by
  native_decide

theorem ws219_array_without_type_table_is_unsupported_stable :
    ws219Run (ws219NoTables ws219ArrayElement) = "error:unsupported.enum_def_table" := by
  native_decide

/-- A call to a function the module only DECLARES is the interpreter's
    `UnsupportedCall`; the same context without the declaration keeps the
    `Call: undefined function` type error (`direct_call_undefined_function_code_stable`). -/
def ws219DeclaredCallContext : EvalContext :=
  { missingDirectCallContext with declared := fun f => f.index == 1 }

theorem ws219_declared_callee_is_unsupported_stable :
    evalValuesStableOutcome
        (evalFunctionInContext ws219DeclaredCallContext f0 [.int 32 7] 2)
        MachineState.empty =
      "error:unsupported.interprocedural_call" := by
  native_decide

/-- Mutation control: a declaration of ANOTHER function does not excuse the
    missing callee — the refusal is keyed on the callee id. -/
def ws219OtherDeclaredCallContext : EvalContext :=
  { missingDirectCallContext with declared := fun f => f.index == 2 }

theorem ws219_other_declared_callee_is_still_type_error_stable :
    evalValuesStableOutcome
        (evalFunctionInContext ws219OtherDeclaredCallContext f0 [.int 32 7] 2)
        MachineState.empty =
      "error:type_error" := by
  native_decide

/-- The bare `stepInst` (no context) types a tuple's integer lanes too:
    `constValueAt`'s integer leaf takes the lane type's width. -/
theorem ws219_bare_tuple_const_lanes_are_typed_stable :
    stepInstStableOutcome (.Const (.Tuple [.I8, .Bool]) (.aggregate [.int 2, .bool true]))
        (stateWith [] 0) =
      "ok:value:aggregate[int8:2,bool:true]" := by
  native_decide

-- ==========================================================-- WS3.20 (F-057): bit intrinsics and bulk memory. Each lock states the
-- value the Rust reference interpreter computes for the same program
-- (crates/trust-ir/tests/bulk_memory_ops.rs pins the Rust side against
-- `u32::rotate_left` / `swap_bytes` / `leading_zeros` etc.), so the two
-- engines cannot drift apart on the new sub-ops.
-- ==========================================================
def bitIntrinsicState : MachineState :=
  stateWith [(v0, .int 32 0x12345678), (v1, .int 32 0), (v2, .int 32 40)] 3

/-- `ctlz i32 0x12345678 = 3` (Rust `0x12345678u32.leading_zeros()`). -/
theorem ctlz_u32_stable :
    stepInstStableOutcome (.UnOp .CtLz .I32 v0) bitIntrinsicState =
      "ok:value:int32:3" := by
  native_decide

/-- `ctlz 0 = width` — the one total spelling (no poison operand). -/
theorem ctlz_zero_is_width_stable :
    stepInstStableOutcome (.UnOp .CtLz .I32 v1) bitIntrinsicState =
      "ok:value:int32:32" := by
  native_decide

/-- `cttz i32 0x12345678 = 3` (Rust `trailing_zeros`). -/
theorem cttz_u32_stable :
    stepInstStableOutcome (.UnOp .CtTz .I32 v0) bitIntrinsicState =
      "ok:value:int32:3" := by
  native_decide

/-- `cttz 0 = width`. -/
theorem cttz_zero_is_width_stable :
    stepInstStableOutcome (.UnOp .CtTz .I32 v1) bitIntrinsicState =
      "ok:value:int32:32" := by
  native_decide

/-- `bswap i32 0x12345678 = 0x78563412` (Rust `swap_bytes`). -/
theorem bswap_u32_stable :
    stepInstStableOutcome (.UnOp .BSwap .I32 v0) bitIntrinsicState =
      "ok:value:int32:2018915346" := by
  native_decide

/-- `bitreverse i32 0x12345678 = 0x1E6A2C48` (Rust `reverse_bits`). -/
theorem bitreverse_u32_stable :
    stepInstStableOutcome (.UnOp .BitReverse .I32 v0) bitIntrinsicState =
      "ok:value:int32:510274632" := by
  native_decide

/-- `rotl i32 0x12345678, 40`: the amount is reduced MODULO the width
    (`40 mod 32 = 8`), giving `0x34567812` — total, never UB (Rust
    `rotate_left(40)`). -/
theorem rotl_amount_mod_width_stable :
    stepInstStableOutcome (.BinOp .RotL .I32 v0 v2) bitIntrinsicState =
      "ok:value:int32:878082066" := by
  native_decide

/-- `rotr i32 0x12345678, 40 = 0x78123456` (Rust `rotate_right(40)`). -/
theorem rotr_amount_mod_width_stable :
    stepInstStableOutcome (.BinOp .RotR .I32 v0 v2) bitIntrinsicState =
      "ok:value:int32:2014458966" := by
  native_decide

/-- `ctlz` on a float operand is a type error, the integer-only rule. -/
def bitIntrinsicFloatState : MachineState :=
  stateWith [(v0, .float 1.0)] 1
theorem ctlz_on_float_is_type_error_stable :
    stepInstStableOutcome (.UnOp .CtLz .F32 v0) bitIntrinsicFloatState =
      "error:type_error" := by
  native_decide

/-- `fcopysign 2.5, -1.0 = -2.5`: magnitude of lhs, sign of rhs. -/
def copySignState : MachineState :=
  stateWith [(v0, .float 2.5), (v1, .float (-1.0)), (v2, .float (-0.0))] 3
theorem fcopysign_takes_sign_of_rhs_stable :
    stepInstStableOutcome (.BinOp .FCopySign .F64 v0 v1) copySignState =
      "ok:value:float:-2.500000" := by
  native_decide

/-- `fcopysign 2.5, -0.0 = -2.5`: the sign of a negative zero counts. -/
theorem fcopysign_negative_zero_sign_stable :
    stepInstStableOutcome (.BinOp .FCopySign .F64 v0 v2) copySignState =
      "ok:value:float:-2.500000" := by
  native_decide

-- MemCopy / MemSet. Two live 16-byte allocations: `src` (v0) holds the u32
-- 0x01020304 at [0..4) and 0xAA at [12..16) with [4..12) UNINITIALIZED;
-- `dst` (v1) is wholly uninitialized. v2 is the count 16 (u64), v3 the
-- count 8, v4 the u8 fill 0x5A, v5 the count 0.
def bulkSrcDstState : MachineState :=
  let (src, mem1) := Memory.empty.alloc 16 8 0 .rustStack
  let (dst, mem2) := mem1.alloc 16 8 0 .rustStack
  let mem3 := (mem2.writeBytes src [4, 3, 2, 1]).writeBytes (src + 12) [0xAA, 0xAA, 0xAA, 0xAA]
  { MachineState.empty with
    memory      := mem3
    permissions := (PermissionMap.empty.set (AllocId.mk 0) .owned).set (AllocId.mk 1) .owned
    locals      := [ (v0, Value.ptr src (some (AllocId.mk 0))), (v1, Value.ptr dst (some (AllocId.mk 1))), (v2, Value.int 64 16),
                     (v3, Value.int 64 8), (ValueId.mk 4, Value.int 8 0x5A),
                     (ValueId.mk 5, Value.int 64 0) ].foldl
                     (fun locals binding => locals.set binding.fst binding.snd) ValueMap.empty
    nextValueId := 6 }

/-- After `memcopy 16` the initialized source lanes are readable at the
    destination: `load u32 dst = 0x01020304` (value AND init state copied). -/
theorem memcopy_copies_initialized_bytes_stable :
    stepTwoInstStableOutcome (.MemCopy v1 v0 v2 false) (.Load .U32 v1 false none)
      bulkSrcDstState = "ok:value:int32:16909060" := by
  native_decide

/-- The uninitialized MIDDLE stays uninitialized at the destination: a strict
    (volatile) `u64` load at `dst + 4` is UB ("reading uninitialized memory"),
    exactly as it would be at the source — the copy laundered nothing. -/
theorem memcopy_keeps_middle_uninit_strict_load_ub_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .MemCopy v1 v0 v2 false,
        .GEP .U8 v1 [v3] false,                 -- v6 = dst + 8 (u8 index 8)
        .Load .U32 (ValueId.mk 6) true none ]
      bulkSrcDstState = "error:ub" := by
  native_decide

/-- The same non-strict reload transports the poison image instead
    (`partial(4)`), the copy-propagates-poison discipline. -/
theorem memcopy_keeps_middle_uninit_partial_reload_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .MemCopy v1 v0 v2 false,
        .GEP .U8 v1 [v3] false,
        .Load .U32 (ValueId.mk 6) false none ]
      bulkSrcDstState = "ok:value:partial(4)" := by
  native_decide

/-- Adjacent (touching) ranges do NOT overlap: the 8-byte `memcpy`
    `src[0..8) -> src[8..16)` within one allocation is defined. -/
theorem memcopy_adjacent_ranges_do_not_overlap_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .GEP .U8 v0 [v3] false,                 -- v6 = src + 8
        .MemCopy (ValueId.mk 6) v0 v3 false ]
      bulkSrcDstState = "ok:value:none" := by
  native_decide

/-- Shift that destination one byte earlier and the ranges `[0,8)` / `[7,15)`
    overlap: UB without the `overlap` flag (memcpy)... -/
def bulkOverlapState : MachineState :=
  { bulkSrcDstState with
    locals := bulkSrcDstState.locals.set (ValueId.mk 6) (.int 64 7)
    nextValueId := 7 }
theorem memcopy_true_overlap_without_flag_is_ub_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .GEP .U8 v0 [ValueId.mk 6] false,       -- v7 = src + 7
        .MemCopy (ValueId.mk 7) v0 v3 false ]
      bulkOverlapState = "error:ub" := by
  native_decide

/-- ...and DEFINED with it (`memmove`): the copy is as-if through a temporary,
    so `src[7..11)` now reads the ORIGINAL `src[0..4)` = 0x01020304 (read
    with a declared `align 1`: `src + 7` is not 4-aligned, and an access with
    no declared alignment checks the natural one, as in the interpreter). -/
theorem memcopy_true_overlap_with_flag_moves_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .GEP .U8 v0 [ValueId.mk 6] false,
        .MemCopy (ValueId.mk 7) v0 v3 true,
        .Load .U32 (ValueId.mk 7) false (some 1) ]
      bulkOverlapState = "ok:value:int32:16909060" := by
  native_decide

/-- A zero count is a no-op even on a null destination (`memcpy(p, q, 0)`). -/
def bulkNullState : MachineState :=
  { bulkSrcDstState with
    locals := bulkSrcDstState.locals.set (ValueId.mk 6) .nullPtr
    nextValueId := 7 }
theorem memcopy_zero_count_is_noop_on_null_stable :
    stepInstStableOutcome (.MemCopy (ValueId.mk 6) v0 (ValueId.mk 5) false) bulkNullState =
      "ok:value:none" := by
  native_decide

/-- Out of bounds: 16 bytes from `src + 8` runs past the allocation: UB. -/
theorem memcopy_out_of_bounds_is_ub_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .GEP .U8 v0 [v3] false,
        .MemCopy v1 (ValueId.mk 6) v2 false ]
      bulkSrcDstState = "error:ub" := by
  native_decide

/-- `memset 8 bytes of 0x5A` at `dst + 8` initializes them: `load u32` at
    `dst + 8` reads 0x5A5A5A5A. -/
theorem memset_initializes_bytes_stable :
    stepTypedInstListStableOutcome [(v3, .U64), (ValueId.mk 6, .U64)]
      [ .GEP .U8 v1 [v3] false,                              -- v6 = dst + 8
        .MemSet (ValueId.mk 6) (ValueId.mk 4) v3,
        .Load .U32 (ValueId.mk 6) true none ]
      bulkSrcDstState = "ok:value:int32:1515870810" := by
  native_decide

/-- A `memset` fill that is not a u8 is a type error (the exact-`U8` rule). -/
theorem memset_non_u8_fill_is_type_error_stable :
    stepInstStableOutcome (.MemSet v1 v2 v3) bulkSrcDstState =
      "error:type_error" := by
  native_decide

-- ---------------------------------------------------------------------------
-- B1 scalar locks (`Isize` / `Usize` / `Char`), lowering-target subset v4
-- (WS2.17). The model pins `Isize`/`Usize` at 64 bits and `Char` at 32
-- (`Ty.bitWidth`), and every arithmetic / compare / cast rule is
-- width-generic over that, so these fixtures pin the WIDTH the arms
-- actually execute at — the thing a 32-bit target would change. Subset v4
-- structural condition 5 keeps a wasm32 module out of the subset for
-- exactly this reason.

/-- `usize` operands execute at the model's 64-bit pin. -/
def usizeAddState : MachineState :=
  stateWith [(v0, .int 64 18446744073709551615), (v1, .int 64 2)] 2

/-- `usize::MAX + 2` wraps to 1 at SIXTY-FOUR bits. At a 32-bit `usize` the
    operands would not even be well-typed, and at 128 the sum would not
    wrap — so this outcome is the width lock. -/
theorem usize_add_wraps_at_64_stable :
    stepInstStableOutcome (.BinOp .Add .Usize v0 v1) usizeAddState =
      "ok:value:int64:1" := by
  native_decide

/-- `usize` subtraction wraps in the same 64-bit modulus: `1 - 2 = 2^64 - 1`. -/
theorem usize_sub_wraps_at_64_stable :
    stepInstStableOutcome (.BinOp .Sub .Usize v1 v0)
      (stateWith [(v0, .int 64 2), (v1, .int 64 1)] 2) =
      "ok:value:int64:18446744073709551615" := by
  native_decide

/-- `usize` compare is UNSIGNED: `2^64 - 1` is ABOVE 2, not below it, which
    is what distinguishes `Usize` from `Isize` at the same width. -/
theorem usize_ult_is_unsigned_stable :
    stepInstStableOutcome (.ICmp .Ult .Usize v0 v1) usizeAddState =
      "ok:value:bool:false" := by
  native_decide

/-- `isize` compare at the SAME bit pattern is SIGNED: `-1 < 2`. The two
    theorems together pin `Ty.isSigned .Isize = true`. -/
theorem isize_slt_is_signed_stable :
    stepInstStableOutcome (.ICmp .Slt .Isize v0 v1) usizeAddState =
      "ok:value:bool:true" := by
  native_decide

/-- `zext u32 -> usize` widens to 64 bits, not to a target-dependent width. -/
theorem usize_zext_from_u32_stable :
    stepInstStableOutcome (.Cast .ZExt .U32 .Usize v0)
      (stateWith [(v0, .int 32 4294967295)] 1) =
      "ok:value:int64:4294967295" := by
  native_decide

/-- `trunc usize -> u32` drops the high half of the 64-bit carrier. -/
theorem usize_trunc_to_u32_stable :
    stepInstStableOutcome (.Cast .Trunc .Usize .U32 v0)
      (stateWith [(v0, .int 64 18446744073709551615)] 1) =
      "ok:value:int32:4294967295" := by
  native_decide

/-- The ONE admitted computed `Char` origin (subset v4 condition 6):
    `zext u8 -> char` widens into the 32-bit carrier. `validChar` holds for
    every result by `validChar_of_lt_256`, which is why no range check is
    needed on this edge. -/
theorem char_zext_from_u8_stable :
    stepInstStableOutcome (.Cast .ZExt .U8 .Char v0)
      (stateWith [(v0, .int 8 255)] 1) =
      "ok:value:int32:255" := by
  native_decide

/-- A `char` carrier is 32 bits wide, so it admits patterns the TYPE does
    not inhabit — the surrogate `0xD800` truncates into it happily. This is
    the width fact that makes `validChar` a separate invariant (and makes
    condition 6 refuse `trunc u32 -> char`, which is exactly this step). -/
theorem char_carrier_admits_a_surrogate_bit_pattern_stable :
    stepInstStableOutcome (.Cast .Trunc .U32 .Char v0)
      (stateWith [(v0, .int 32 55296)] 1) =
      "ok:value:int32:55296" := by
  native_decide

-- Crystal lane (E3b): `Constant.uninit`, an UNWRITTEN struct/tuple lane. The interpreter-agreement
-- channel for the Rust reference interpreter's `interpret_uninit_tests.rs`: the lane-on bridge
-- spells `Option<u64>::None` as `const { uninit, uninit }; insertfield 0, tag`. A write replaces
-- an unwritten lane, reading a written lane gives its value, and reading an unwritten lane is
-- undefined behaviour, in both models. `v0` holds the None built that way, `v1` a tag/payload.

/-- `v0` = the None the lane-on bridge builds (`{ tag 0, <unwritten> }`), `v1` = u64 7. -/
def uninitLaneState : MachineState :=
  stateWith [(v0, .aggregate [.int 64 0, .uninit]), (v1, .int 64 7)] 2

/-- A `Const` of `{ uninit, uninit }` binds the aggregate with both lanes unwritten. -/
theorem uninit_lane_const_binds_unwritten_lanes_stable :
    stepInstStableOutcome (.Const (.Tuple [.I64, .U64]) (.aggregate [.uninit, .uninit]))
        uninitLaneState
      = "ok:value:aggregate[uninit,uninit]" := by native_decide

/-- Reading the WRITTEN tag lane gives its value. -/
theorem uninit_lane_written_lane_reads_stable :
    stepInstStableOutcome (.ExtractField .I64 v0 0) uninitLaneState
      = "ok:value:int64:0" := by native_decide

/-- Reading the UNWRITTEN payload lane is undefined behaviour (Rust:
    `reading_an_unwritten_lane_is_undefined_behaviour`). -/
theorem uninit_lane_unwritten_lane_read_is_ub_stable :
    stepInstStableOutcome (.ExtractField .U64 v0 1) uninitLaneState
      = "error:ub" := by native_decide

/-- Writing the unwritten lane REPLACES it (Rust: `writing_an_unwritten_lane_replaces_it`). -/
def uninitLaneWriteThenReadOutcome : String :=
  match Sem.run (do
      let written ← semInsertField (.Tuple [.I64, .U64]) v0 1 v1
      let read ← semExtractField .U64 written 1
      Sem.lookupValue read) uninitLaneState with
  | .ok (v, _) => "ok:" ++ stableValueString v
  | .error e   => "error:" ++ e.code

theorem uninit_lane_write_replaces_it_stable :
    uninitLaneWriteThenReadOutcome = "ok:int64:7" := by native_decide


-- ---------------------------------------------------------------------------
-- One integer representation: an integer constant binds its RESIDUE
-- ---------------------------------------------------------------------------
--
-- Every `Value.int w v` the model makes satisfies `0 ≤ v < 2^w`: parameters
-- (`TrustIrEval/Run.lean` `argValue`) and operation results (`wrap`,
-- `truncateUnsigned`) always did, and the seven places where a
-- `Constant.int` becomes or meets a model value now do too (`Value.intAt`,
-- `Semantics/Aggregate.lean`). Each fixture below states the reference
-- interpreter's verdict; the first seven were FALSE while a `Const` bound the
-- raw literal (`Value.int 32 (-1)` beside `Value.int 32 4294967295`), and the
-- last is the GEP regression guard: once a constant index is a residue, the
-- index sign is read explicitly (`toSigned`), so `const i64 -1` stays UB.
-- These are executable fixtures (`native_decide`): they witness `(test)`,
-- never `(lean-theorem)`; the theorems are `TrustIr/Proofs/IntResidue.lean`.

/-- `icmp ult (const i32 -1), (const i32 0)`: `0xffffffff < 0` is false. -/
theorem icmp_ult_negative_literal_is_unsigned :
    stepInstListStableOutcome
      [.Const .I32 (.int (-1)), .Const .I32 (.int 0), .ICmp .Ult .I32 v0 v1]
      MachineState.empty = "ok:value:bool:false" := by
  native_decide

/-- Lane 0 of `icmp ugt <4 x i32> vec[-1, 0, 0, 0], zeroinitializer` is true. -/
theorem vector_icmp_ugt_negative_literal_lane_is_unsigned :
    stepInstListStableOutcome
      [.Const (.Vector 4 .I32) (.vector [.int (-1), .int 0, .int 0, .int 0]),
       .Const (.Vector 4 .I32) (.vector [.int 0, .int 0, .int 0, .int 0]),
       .ICmp .Ugt (.Vector 4 .I32) v0 v1]
      MachineState.empty = "ok:value:vector[bool:true,bool:false,bool:false,bool:false]" := by
  native_decide

/-- `udiv (const i32 -1), 2` is `0xffffffff / 2 = 0x7fffffff`. -/
theorem udiv_negative_literal_is_unsigned :
    stepInstListStableOutcome
      [.Const .I32 (.int (-1)), .Const .I32 (.int 2), .BinOp .UDiv .I32 v0 v1]
      MachineState.empty = "ok:value:int32:2147483647" := by
  native_decide

/-- `zext (const i8 -1) to i32` is `255`. -/
theorem zext_negative_literal_is_unsigned :
    stepInstListStableOutcome
      [.Const .I8 (.int (-1)), .Cast .ZExt .I8 .I32 v0]
      MachineState.empty = "ok:value:int32:255" := by
  native_decide

/-- `shl 5, (const i32 -1)`: the amount is `0xffffffff ≥ 32`, which is UB. -/
theorem shl_by_negative_literal_is_ub :
    stepInstListStableOutcome
      [.Const .I32 (.int 5), .Const .I32 (.int (-1)), .BinOp .Shl .I32 v0 v1]
      MachineState.empty = "error:ub" := by
  native_decide

/-- `switch i8 %x [ -1: bb1 ], default bb2` at `x = -1` (the parameter residue
    255) takes the case: the scan compares residues. -/
theorem switch_negative_case_matches_residue :
    stepInstStableOutcome
      (.Switch v0 (BlockId.mk 2) [] [{ value := .int (-1), target := BlockId.mk 1, args := [] }]
        false)
      (stateWith [(v0, .int 8 255)] 1) = "ok:terminator:continue:1:[]" := by
  native_decide

/-- `enum Ord { Less = -1, Equal = 0, Greater = 1 }` with `#[repr(i8)]`. -/
def residueOrdEnum : EnumDef :=
  { id := EnumId.mk 0, name := "Ord",
    variants := [{ name := "Less", fields := [] },
                 { name := "Equal", fields := [] },
                 { name := "Greater", fields := [] }],
    discriminants := [some (-1), some 0, some 1],
    tagRepr := some .i8 }

/-- A context carrying only `residueOrdEnum`. -/
def residueOrdTables (f : EvalFunction) : EvalContext :=
  { functions := functionMap [(f0, f)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none
    enums := fun e => if e.index == 0 then some residueOrdEnum else none }

/-- The tag lane of `const Ord::Less` is the `i8` residue of `-1`. -/
theorem enum_negative_tag_is_residue :
    ws219Run (residueOrdTables (ws219ConstExtract (.Enum (EnumId.mk 0)) (.aggregate [.int (-1)]) .I8 0)) =
      "ok:return:[int8:255]" := by
  native_decide

/-- Guard: `gep i32, (alloca i32), const i64 -1` stays UB once the constant is a
    residue, because the index is read signed. -/
theorem gep_const_negative_index_is_still_ub :
    stepTypedInstListStableOutcome [(v1, .I64)]
      [.Alloca .I32 none none, .Const .I64 (.int (-1)), .GEP .I32 v0 [v1] true]
      MachineState.empty = "error:ub" := by
  native_decide


-- ---------------------------------------------------------------------------
-- The narrow x86-64 cell shapes: `<16 x i8>` / `<8 x i16>` lane insert / extract
-- ---------------------------------------------------------------------------

/-- `insertelement <16 x i8> zeroinitializer, (i8 255), 3` writes lane 3, as the
    interpreter does (until 2026-09-30 a `type_error` here). -/
theorem insert_element_v16i8_lane_stable :
    stepInstStableOutcome (.InsertElement (.Vector 16 .I8) v0 v1 v2)
      (stateWith [(v0, v16i8 (List.replicate 16 0)), (v1, .int 64 3), (v2, .int 8 255)] 3) =
      "ok:value:vector[int8:0,int8:0,int8:0,int8:255,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0]" := by
  native_decide

/-- `extractelement <8 x i16> v, 7` reads the last lane. -/
theorem extract_element_v8i16_lane_stable :
    stepInstStableOutcome (.ExtractElement .I16 v0 v1)
      (stateWith [(v0, v8i16 [0, 1, 2, 3, 4, 5, 6, 65535]), (v1, .int 64 7)] 2) =
      "ok:value:int16:65535" := by
  native_decide

/-- A lane of the wrong width is still the type error it was. -/
theorem insert_element_v16i8_wrong_lane_width_is_type_error_stable :
    stepInstStableOutcome (.InsertElement (.Vector 16 .I8) v0 v1 v2)
      (stateWith [(v0, v16i8 (List.replicate 16 0)), (v1, .int 64 3), (v2, .int 16 255)] 3) =
      "error:type_error" := by
  native_decide

-- ---------------------------------------------------------------------------
-- The unsigned lane types of the x86-64 cells (`Ty.executableIntLane?`)
-- ---------------------------------------------------------------------------

/-- `icmp ugt <4 x u32>` executes: a cell is keyed by lane width and count, so
    the unsigned lane type is a shape of the same cell (until 2026-09-30
    `unsupported vector_shape`). Lane 0 compares 2^32-1 with 0. -/
theorem vector_icmp_ugt_v4u32_executes_stable :
    stepInstStableOutcome (.ICmp .Ugt (.Vector 4 .U32) v0 v1)
      (stateWith [(v0, v4i32 4294967295 1 2 3), (v1, v4i32 0 1 3 2)] 2) =
      "ok:value:vector[bool:true,bool:false,bool:false,bool:true]" := by
  native_decide

/-- `insertelement <16 x u8>` writes its lane exactly as the `<16 x i8>` twin. -/
theorem insert_element_v16u8_lane_stable :
    stepInstStableOutcome (.InsertElement (.Vector 16 .U8) v0 v1 v2)
      (stateWith [(v0, v16i8 (List.replicate 16 0)), (v1, .int 64 3), (v2, .int 8 255)] 3) =
      "ok:value:vector[int8:0,int8:0,int8:0,int8:255,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0,int8:0]" := by
  native_decide

-- ---------------------------------------------------------------------------
-- `AtomicRMW` `Max` / `Min` order signed, `UMax` / `UMin` unsigned
-- ---------------------------------------------------------------------------

/-- Over a stored 5, `max` with the `i32` residue of -1 keeps 5, as the
    interpreter's `as_signed` order does (until 2026-09-30 the raw order wrote
    4294967295). -/
theorem atomic_rmw_max_orders_signed :
    applyAtomicRMWOp .Max 32 5 4294967295 = 5 := by
  native_decide

theorem atomic_rmw_min_orders_signed :
    applyAtomicRMWOp .Min 32 5 4294967295 = 4294967295 := by
  native_decide

theorem atomic_rmw_umax_orders_unsigned :
    applyAtomicRMWOp .UMax 32 5 4294967295 = 4294967295 := by
  native_decide

theorem atomic_rmw_umin_orders_unsigned :
    applyAtomicRMWOp .UMin 32 5 4294967295 = 5 := by
  native_decide

-- ---------------------------------------------------------------------------
-- Amendment D (`docs/SPEC_RATIFICATIONS.md` §20): a drop is a call of its
-- type's glue. Rust twins: `interpret_drop_glue_tests.rs`.
-- ---------------------------------------------------------------------------

/-- The dropped type: an owning struct. -/
def dropTy : Ty := .Struct ⟨0⟩

/-- The glue `f1 : (ptr) -> ()`: stores 1 into the dropped `i64` cell. -/
def dropGlueFunction : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [] }
    cfg := singletonCFG
      { params := [(v0, .Ptr)]
        body := [.Const .I64 (.int 1), .Store .I64 v0 v1 false none]
        terminator := .Return [] }
    entryBlock := b0 }

/-- `f0 : () -> i64`: an `i64` cell holding 7, `drop dropTy` through it, then
    load the cell. -/
def dropCallerFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I64] }
    cfg := singletonCFG
      { params := []
        body := [.Alloca .I64 none none, .Const .I64 (.int 7), .Store .I64 v0 v1 false none,
                 .Drop dropTy v0, .Load .I64 v0 false none]
        terminator := .Return [ValueId.mk 2] }
    entryBlock := b0 }

/-- `f0 : () -> i64` with the unwinding twin: the cell holds 5, `drop_invoke`
    passes it to `bb1` on the normal edge, and `bb2` is a cleanup pad that
    evaluation never reaches. -/
def dropInvokeCallerFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I64] }
    cfg := fun bid =>
      if bid.index == 0 then
        some { params := []
               body := [.Alloca .I64 none none, .Const .I64 (.int 5),
                        .Store .I64 v0 v1 false none]
               terminator := .DropInvoke dropTy v0 (BlockId.mk 1) [v0] (BlockId.mk 2) }
      else if bid.index == 1 then
        some { params := [(ValueId.mk 5, .Ptr)]
               body := [.Load .I64 (ValueId.mk 5) false none]
               terminator := .Return [ValueId.mk 6] }
      else if bid.index == 2 then
        some { params := []
               body := [.LandingPad true []]
               terminator := .Resume (ValueId.mk 7) }
      else none
    entryBlock := b0 }

def dropContext (caller : EvalFunction) (table : Bool) : EvalContext :=
  { functions := functionMap [(f0, caller), (f1, dropGlueFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none
    dropGlue := fun t => if table && t == dropTy then some f1 else none }

/-- A resolved drop runs its glue on the place: the glue's store is what the
    caller loads back (Rust: `a_resolved_drop_calls_its_glue_with_the_pointer`). -/
theorem drop_resolved_runs_glue_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (dropContext dropCallerFunction true) f0 [] 8)
        MachineState.empty =
      "ok:return:[int64:1]" := by
  native_decide

/-- A resolved `DropInvoke` runs its glue and takes its NORMAL edge; the
    unwind edge is never taken (Rust:
    `drop_invoke_takes_the_normal_edge_and_never_the_unwind_edge`). -/
theorem drop_invoke_resolved_takes_normal_edge_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (dropContext dropInvokeCallerFunction true) f0 [] 8)
        MachineState.empty =
      "ok:return:[int64:1]" := by
  native_decide

/-- With no row, the same drop is the structured `unsupported.destructor`
    under the context too, never a no-op that would have returned 7 (Rust:
    `an_unresolved_drop_is_unsupported_instruction_never_a_no_op`). -/
theorem drop_unresolved_in_context_is_unsupported_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (dropContext dropCallerFunction false) f0 [] 8)
        MachineState.empty =
      "error:unsupported.destructor" := by
  native_decide

-- -----------------------------------------------------------------
-- Amendment D, Part 2 (`docs/SPEC_RATIFICATIONS.md` §21): unwinding as an
-- exit under `PanicStrategy.unwind`; `.abort` keeps the projection. Rust
-- twins: `crates/trust-ir-conformance/tests/interpret_unwind.rs`.
-- -----------------------------------------------------------------

/-- The panic (message and site) an evaluator run reports, or its stable
    outcome. -/
def evalPanicOutcome (m : Sem (List Value)) (state : MachineState) : String :=
  match Sem.run m state with
  | .error (.panic msg site) => "panic:" ++ msg ++ ";" ++ stablePanicSite site
  | _ => "not-a-panic:" ++ evalValuesStableOutcome m state

def fPanicGlue : FuncId := FuncId.mk 2
def fInner : FuncId := FuncId.mk 3
def fFailing : FuncId := FuncId.mk 4

/-- A glue `f2 : (ptr) -> ()` whose divide-by-zero check fails (sited at
    entry `f1`, location `global 0`). -/
def panickingGlueFunction : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [] }
    cfg := singletonCFG
      { params := [(v0, .Ptr)]
        body := [.Const .Bool (.bool false), .Assert v1 .DivByZero (some ⟨f1, .global g0⟩)]
        terminator := .Return [] }
    entryBlock := b0 }

/-- `f0 : () -> i32`: `drop_invoke` of a cell whose glue panics; the normal
    edge returns 7, the CLEANUP pad at `bb2` returns the selector it bound. -/
def dropInvokeCleanupCaller : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := fun bid =>
      if bid.index == 0 then
        some { params := []
               body := [.Alloca .I64 none none]
               terminator := .DropInvoke dropTy v0 (BlockId.mk 1) [] (BlockId.mk 2) }
      else if bid.index == 1 then
        some { params := []
               body := [.Const .I32 (.int 7)]
               terminator := .Return [v1] }
      else if bid.index == 2 then
        some { params := []
               body := [.LandingPad true []]
               bodyResultDests := [[ValueId.mk 5, ValueId.mk 6]]
               terminator := .Return [ValueId.mk 6] }
      else none
    entryBlock := b0 }

def dropInvokeCleanupContext : EvalContext :=
  { functions := functionMap [(f0, dropInvokeCleanupCaller), (fPanicGlue, panickingGlueFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none
    dropGlue := fun t => if t == dropTy then some fPanicGlue else none }

/-- Under `.unwind` the glue's raise unwinds out of its frame, the
    `drop_invoke` catches it, and the cleanup pad binds selector 0 (Rust:
    `drop_invoke_takes_the_unwind_edge_and_the_cleanup_runs`). -/
theorem drop_invoke_unwinds_to_cleanup_stable :
    evalValuesStableOutcome
        (evalFunctionInContext dropInvokeCleanupContext f0 [] 8 .unwind)
        MachineState.empty =
      "ok:return:[int32:0]" := by
  native_decide

/-- The same module under `.abort` (the default): the glue's panic is the
    run's outcome and the pad is never entered. -/
theorem drop_invoke_abort_keeps_the_panic_stable :
    evalPanicOutcome
        (evalFunctionInContext dropInvokeCleanupContext f0 [] 8)
        MachineState.empty =
      "panic:attempt to divide by zero;entry:1@global:0+0" := by
  native_decide

/-- `f0 : (bool) -> ()`: an `assert_invoke` whose cleanup pad `bb2` resumes
    the exception it bound. -/
def assertInvokeResumeCaller : EvalFunction :=
  { body := { paramTys := [.Bool], returnTys := [] }
    cfg := fun bid =>
      if bid.index == 0 then
        some { params := [(v0, .Bool)]
               body := []
               terminator := .AssertInvoke v0 .DivByZero ⟨f1, .global g0⟩
                 (BlockId.mk 1) [] (BlockId.mk 2) }
      else if bid.index == 1 then
        some { params := [], body := [], terminator := .Return [] }
      else if bid.index == 2 then
        some { params := []
               body := [.LandingPad true []]
               bodyResultDests := [[ValueId.mk 3, ValueId.mk 4]]
               terminator := .Resume (ValueId.mk 3) }
      else none
    entryBlock := b0 }

def assertInvokeResumeContext : EvalContext :=
  { functions := functionMap [(f0, assertInvokeResumeCaller)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

/-- A failing `assert_invoke` enters its cleanup pad, whose `resume`
    re-raises; the escaping unwinding is reported as the ORIGINAL panic —
    the same message and site as the `.abort` run (next theorem) (Rust:
    `assert_invoke_failure_enters_the_pad_and_resume_reraises_the_same_panic`). -/
theorem assert_invoke_unwinds_with_kind_message_stable :
    evalPanicOutcome
        (evalFunctionInContext assertInvokeResumeContext f0 [.bool false] 8 .unwind)
        MachineState.empty =
      "panic:attempt to divide by zero;entry:1@global:0+0" := by
  native_decide

theorem assert_invoke_abort_reports_the_same_panic_stable :
    evalPanicOutcome
        (evalFunctionInContext assertInvokeResumeContext f0 [.bool false] 8 .abort)
        MachineState.empty =
      "panic:attempt to divide by zero;entry:1@global:0+0" := by
  native_decide

/-- `f0 : (bool) -> i32`: an `assert_invoke` whose pad `bb2` has the clauses
    `clauses` and returns the selector it bound. -/
def assertInvokePadCaller (isCleanup : Bool) (clauses : List Nat) : EvalFunction :=
  { body := { paramTys := [.Bool], returnTys := [.I32] }
    cfg := fun bid =>
      if bid.index == 0 then
        some { params := [(v0, .Bool)]
               body := []
               terminator := .AssertInvoke v0 .DivByZero ⟨f1, .global g0⟩
                 (BlockId.mk 1) [] (BlockId.mk 2) }
      else if bid.index == 1 then
        some { params := [], body := [.Const .I32 (.int 9)], terminator := .Return [v1] }
      else if bid.index == 2 then
        some { params := []
               body := [.LandingPad isCleanup clauses]
               bodyResultDests := [[ValueId.mk 3, ValueId.mk 4]]
               terminator := .Return [ValueId.mk 4] }
      else none
    entryBlock := b0 }

def assertInvokePadContext (isCleanup : Bool) (clauses : List Nat) : EvalContext :=
  { functions := functionMap [(f0, assertInvokePadCaller isCleanup clauses)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

/-- A catch-all clause 0 binds selector 1 (trust-cg's convention for a
    function without typed catches; Rust: `a_catch_all_pad_catches_and_binds_selector_one`). -/
theorem catch_all_selector_is_one_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (assertInvokePadContext false [0]) f0 [.bool false] 8 .unwind)
        MachineState.empty =
      "ok:return:[int32:1]" := by
  native_decide

/-- A passing check takes the normal edge under `.unwind` too. -/
theorem assert_invoke_passing_takes_normal_edge_under_unwind_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (assertInvokePadContext false [0]) f0 [.bool true] 8 .unwind)
        MachineState.empty =
      "ok:return:[int32:9]" := by
  native_decide

/-- `.abort` (the default) keeps the ratified projection on the same module:
    the failing check is the terminal panic and the pad is never entered
    (Rust: `abort_strategy_reproduces_todays_projection`). -/
theorem abort_strategy_keeps_projection_stable :
    evalPanicOutcome
        (evalFunctionInContext (assertInvokePadContext false [0]) f0 [.bool false] 8)
        MachineState.empty =
      "panic:attempt to divide by zero;entry:1@global:0+0" := by
  native_decide

/-- A typed catch clause (any index but 0) is refused: the format has no
    typeinfo model (Rust: `a_typed_catch_clause_is_refused_unsupported`). -/
theorem typed_catch_is_refused_stable :
    evalValuesStableOutcome
        (evalFunctionInContext (assertInvokePadContext false [3]) f0 [.bool false] 8 .unwind)
        MachineState.empty =
      "error:unsupported.typed_catch" := by
  native_decide

/-- A pad with no action (no clause, not cleanup) re-propagates: the
    unwinding leaves the frame and the entry reports the original panic
    (Rust: `a_pad_with_no_action_is_skipped`). -/
theorem pad_with_no_action_is_skipped_stable :
    evalPanicOutcome
        (evalFunctionInContext (assertInvokePadContext false []) f0 [.bool false] 8 .unwind)
        MachineState.empty =
      "panic:attempt to divide by zero;entry:1@global:0+0" := by
  native_decide

/-- `f4 : () -> ()` fails its check; `f3 : () -> ()` calls it with a PLAIN
    call; `f0 : () -> i32` invokes `f3` with a catch-all pad that returns its
    selector. The unwinding leaves `f4` and `f3` (a plain call has no pad) and
    `f0`'s invoke catches it (Rust:
    `a_plain_drop_whose_glue_panics_unwinds_out_of_the_frame`). -/
def failingFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [] }
    cfg := singletonCFG
      { params := []
        body := [.Const .Bool (.bool false), .Assert v0 .DivByZero (some ⟨f1, .global g0⟩)]
        terminator := .Return [] }
    entryBlock := b0 }

def plainCallerFunction : EvalFunction :=
  { body := { paramTys := [], returnTys := [] }
    cfg := singletonCFG
      { params := [], body := [.Call fFailing []], terminator := .Return [] }
    entryBlock := b0 }

def invokeCatchAllCaller : EvalFunction :=
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := fun bid =>
      if bid.index == 0 then
        some { params := []
               body := []
               terminator := .Invoke fInner [] (BlockId.mk 1) [] (BlockId.mk 2) }
      else if bid.index == 1 then
        some { params := [], body := [.Const .I32 (.int 9)], terminator := .Return [v0] }
      else if bid.index == 2 then
        some { params := []
               body := [.LandingPad false [0]]
               bodyResultDests := [[ValueId.mk 3, ValueId.mk 4]]
               terminator := .Return [ValueId.mk 4] }
      else none
    entryBlock := b0 }

def plainCallUnwindContext : EvalContext :=
  { functions := functionMap
      [(f0, invokeCatchAllCaller), (fInner, plainCallerFunction), (fFailing, failingFunction)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 8
    globalsTable := fun _ => none }

theorem plain_call_unwinds_out_of_the_frame_stable :
    evalValuesStableOutcome
        (evalFunctionInContext plainCallUnwindContext f0 [] 8 .unwind)
        MachineState.empty =
      "ok:return:[int32:1]" := by
  native_decide

/-- `resume` of a value no landing pad produced is undefined behaviour under
    `.unwind` (Rust: `resume_of_a_non_exception_pointer_is_undefined_behavior`),
    and today's refusal under `.abort`. -/
def resumeNullCaller : EvalFunction :=
  { body := { paramTys := [], returnTys := [] }
    cfg := singletonCFG
      { params := [], body := [.NullPtr], terminator := .Resume v0 }
    entryBlock := b0 }

def resumeNullContext : EvalContext :=
  { functions := functionMap [(f0, resumeNullCaller)]
    funcPtrs := funcPtrMap []
    funcTys := funcTyMap []
    maxCallDepth := 4
    globalsTable := fun _ => none }

theorem resume_of_a_non_exception_is_ub_under_unwind_stable :
    evalValuesStableOutcome
        (evalFunctionInContext resumeNullContext f0 [] 4 .unwind)
        MachineState.empty =
      "error:ub" := by
  native_decide

theorem resume_is_refused_under_abort_stable :
    evalValuesStableOutcome
        (evalFunctionInContext resumeNullContext f0 [] 4)
        MachineState.empty =
      "error:unsupported.host_unwind" := by
  native_decide

/-- Equal-width signedness is supplied by declarations, not integer bits. -/
def exactFieldContext (aggregateTy insertedTy : Ty) : EvalContext :=
  { directCallContext with
    localTypes := some (fun id =>
      if id.index == 0 then some aggregateTy
      else if id.index == 1 then some insertedTy else none)
    enums := fun id => if id.index == 0 then some
      { id := EnumId.mk 0, name := "SignedOrUnsigned"
        variants := [{ name := "Signed", fields := [.I32] },
                     { name := "Unsigned", fields := [.U32] }]
        discriminants := [some (-1), some 7], tagRepr := some .i8 }
      else none }

def exactFieldOutcome (ctx : EvalContext) (inst : Inst) (held inserted : Value) : String :=
  match Sem.run (stepInstWithContext ctx inst)
      (stateWith [(v0, held), (v1, inserted)] 2) with
  | .ok (result, post) => "ok:" ++ InstrResult.stableString post result
  | .error error => "error:" ++ error.code

/-- Identical int32 bits do not authorize reading an I32 lane as U32. -/
theorem exact_tuple_field_read_signedness_stable :
    [.I32, .U32].map (fun ty => exactFieldOutcome
      (exactFieldContext (.Tuple [.I32]) .I32) (.ExtractField ty v0 0)
      (.aggregate [.int 32 9]) (.int 32 3)) =
    ["ok:value:int32:9", "error:type_error"] := by native_decide

/-- Replacement checks the inserted SSA declaration, not only its width. -/
theorem exact_tuple_field_write_signedness_stable :
    [.I32, .U32].map (fun ty => exactFieldOutcome
      (exactFieldContext (.Tuple [.I32]) ty) (.InsertField (.Tuple [.I32]) v0 0 v1)
      (.aggregate [.int 32 9]) (.int 32 3)) =
    ["ok:value:aggregate[int32:3]", "error:type_error"] := by native_decide

/-- Active-variant selection decodes a negative tag's canonical residue. -/
theorem exact_enum_field_read_active_variant_stable :
    [(.int 8 255, Ty.I32), (.int 8 255, Ty.U32),
     (.int 8 7, Ty.U32), (.int 8 7, Ty.I32)].map (fun (tag, ty) =>
      exactFieldOutcome (exactFieldContext (.Enum (EnumId.mk 0)) .I32)
        (.ExtractField ty v0 1) (.aggregate [tag, .int 32 9]) (.int 32 3)) =
    ["ok:value:int32:9", "error:ub", "ok:value:int32:9", "error:ub"] := by
  native_decide

theorem exact_enum_field_write_active_variant_stable :
    [Ty.I32, Ty.U32].map (fun ty => exactFieldOutcome
      (exactFieldContext (.Enum (EnumId.mk 0)) ty)
      (.InsertField (.Enum (EnumId.mk 0)) v0 1 v1)
      (.aggregate [.int 8 255, .int 32 9]) (.int 32 3)) =
    ["ok:value:aggregate[int8:255,int32:3]", "error:ub"] := by native_decide

/-- Pointer identity is independent of the target's equal-width integer lane. -/
theorem exact_tuple_pointer_field_refuses_integer_stable :
    exactFieldOutcome (exactFieldContext (.Tuple [.Ptr]) .U64)
      (.ExtractField .U64 v0 0) (.aggregate [.nullPtr]) (.int 64 0) =
      "error:type_error" := by native_decide

/-- A forbidden tag write is UB even when the replacement has another type.
    It must not be reclassified by the contextual field-type check. -/
theorem exact_enum_tag_write_precedes_replacement_type_stable :
    [Ty.I8, Ty.U8, Ty.U64].map (fun ty => exactFieldOutcome
      (exactFieldContext (.Enum (EnumId.mk 0)) ty)
      (.InsertField (.Enum (EnumId.mk 0)) v0 0 v1)
      (.aggregate [.int 8 255, .int 32 9])
      (.int (if closureTyEq ty .U64 then 64 else 8) 3)) =
    ["error:ub", "error:ub", "error:ub"] := by native_decide

/-- Aggregate result typing precedes field bounds, even for a missing lane. -/
theorem exact_insert_aggregate_type_precedes_bounds_stable :
    [0, 1, 99].map (fun field => exactFieldOutcome
      (exactFieldContext (.Enum (EnumId.mk 0)) .I32)
      (.InsertField (.Tuple [.I32]) v0 field v1)
      (.aggregate [.int 8 255, .int 32 9]) (.int 32 3)) =
    ["error:type_error", "error:type_error", "error:type_error"] := by native_decide

def splatTypedContext (elementTy sourceTy : Ty) : EvalContext :=
  { exactFieldContext .Unit sourceTy with
    types := fun id => if id.index == 0 then some elementTy else none }

/-- Even an empty replication inspects the original operand's exact type. -/
theorem contextual_splat_rejects_same_width_wrong_element_type :
    [0, 1, 3].map (fun count => exactFieldOutcome
      (splatTypedContext .I32 .U32) (.ArraySplat (.Array (TyId.mk 0) count) v1)
      (.aggregate []) (.int 32 9)) =
    ["error:type_error", "error:type_error", "error:type_error"] := by native_decide

theorem contextual_splat_preserves_zero_one_and_repeated_values :
    [0, 1, 3].map (fun count => exactFieldOutcome
      (splatTypedContext .I32 .I32) (.ArraySplat (.Array (TyId.mk 0) count) v1)
      (.aggregate []) (.int 32 9)) =
    ["ok:value:array:uniform(0)", "ok:value:array:uniform(1;int32:9)",
     "ok:value:array:uniform(3;int32:9)"] := by native_decide

theorem contextual_splat_poison_precedes_type_metadata :
    exactFieldOutcome { directCallContext with localTypes := none }
      (.ArraySplat (.Array (TyId.mk 0) 0) v1)
      (.aggregate []) (.partial [none]) = "error:ub" := by native_decide

theorem contextual_splat_requires_original_operand_declaration :
    exactFieldOutcome { splatTypedContext .I32 .I32 with localTypes := none }
      (.ArraySplat (.Array (TyId.mk 0) 3) v1)
      (.aggregate []) (.int 32 9) = "error:unsupported.ssa_type_table" := by native_decide

theorem contextual_splat_requires_original_element_declaration :
    exactFieldOutcome { splatTypedContext .I32 .I32 with types := fun _ => none }
      (.ArraySplat (.Array (TyId.mk 0) 3) v1)
      (.aggregate []) (.int 32 9) = "error:unsupported.enum_def_table" := by native_decide

theorem contextual_splat_nonarray_precedes_missing_metadata :
    exactFieldOutcome directCallContext (.ArraySplat .I32 v1)
      (.aggregate []) (.int 32 9) = "error:type_error" := by native_decide

def contextualSplatValues (ty : Ty) (value : Value) : Option (CompactArray.Packed Value) :=
  match Sem.run (stepInstWithContext (splatTypedContext ty ty)
      (.ArraySplat (.Array (TyId.mk 0) 3) v1))
      (stateWith [(v1, value)] 2) with
  | .ok (.value (some id), post) => match post.lookupValue id with
    | some (.array values) => some values
    | _ => none
  | _ => none

/-- Register replication is not a floating-point byte-image boundary. -/
theorem contextual_splat_transports_nan_without_image_admission :
    (match contextualSplatValues .F32 (.float (0.0 / 0.0)) with
      | some values => values.size == 3 && [0, 1, 2].all (fun index =>
          match values.get? index with | some (.float f) => f.isNaN | _ => false)
      | none => false) = true := by native_decide

/-- Copies retain provenance without dereferencing or checking a byte layout. -/
theorem contextual_splat_preserves_pointer_provenance :
    (match contextualSplatValues .Ptr (.ptr 4096 (some (AllocId.mk 42))) with
      | some values => values.size == 3 && [0, 1, 2].all (fun index =>
          match values.get? index with
          | some (.ptr address provenance) => address == 4096 && provenance == some (AllocId.mk 42)
          | _ => false)
      | none => false) = true := by native_decide


-- Standalone malformed-table controls exercise exact declaration association;
-- they make no validated-module claim. Ty's existing executable BEq is used
-- only for source types, never to infer a carrier's type.
private def ssaCharTypeResultTag : Except SemError (List Ty) → String
  | .error error => "error:" ++ error.code
  | .ok types => "ok:" ++ stableJoin "," (types.map (fun ty =>
      match ty with | .Char => "char" | _ => "other"))

theorem ssa_char_original_type_match_stable :
    ssaCharTypeResultTag (ssaInstructionResultTypes (some (fun _ => some .Char))
      (fun _ => none) (fun _ => none) (.Const .Char (.int 65)) [⟨99⟩] 1) =
      "ok:char" := by native_decide

theorem ssa_char_conflicting_u32_declaration_refused_stable :
    ssaCharTypeResultTag (ssaInstructionResultTypes (some (fun _ => some .U32))
      (fun _ => none) (fun _ => none) (.Const .Char (.int 65)) [⟨99⟩] 1) =
      "error:type_error" := by native_decide

theorem ssa_char_conflicting_char_declaration_refused_stable :
    ssaCharTypeResultTag (ssaInstructionResultTypes (some (fun _ => some .Char))
      (fun _ => none) (fun _ => none) (.Const .U32 (.int 65)) [⟨99⟩] 1) =
      "error:type_error" := by native_decide

private def ssaCharPairHeader (_ : FuncId) : Option FuncTyDef :=
  some { params := [], returns := [.U32, .Char], isVararg := false }

theorem ssa_char_multi_result_order_stable :
    ssaCharTypeResultTag (ssaInstructionResultTypes
      (some (fun id => if id.index == 42 then some .U32 else some .Char))
      ssaCharPairHeader (fun _ => none) (.Call ⟨7⟩ []) [⟨42⟩, ⟨99⟩] 2) =
      "ok:other,char" := by native_decide

theorem ssa_char_swapped_result_declarations_refused_stable :
    ssaCharTypeResultTag (ssaInstructionResultTypes
      (some (fun id => if id.index == 42 then some .Char else some .U32))
      ssaCharPairHeader (fun _ => none) (.Call ⟨7⟩ []) [⟨42⟩, ⟨99⟩] 2) =
      "error:type_error" := by native_decide

/-- These executable functions obtain metadata from the very same source
    nodes and destinations that their CFG executes. -/
private def ssaCharSourceFixture (poison : Bool) (raw : Int) : EvalFunction :=
  let block : BasicBlock :=
    { params := []
      body := if poison then [.Undef .Char, .Const .I32 (.int 42)]
        else [.Const .U64 (.int raw), .Cast .Trunc .U64 .Char ⟨7⟩,
          .Const .I32 (.int 42)]
      bodyResultDests := if poison then [[⟨99⟩], [⟨101⟩]]
        else [[⟨7⟩], [⟨99⟩], [⟨101⟩]]
      terminator := .Return [⟨101⟩] }
  { body := { paramTys := [], returnTys := [.I32] }
    cfg := singletonCFG block
    entryBlock := b0
    localTypes := fixtureLocalTypes block }

theorem ssa_char_source_invalid_discarded_result_refused_stable :
    ws219Run (ws219NoTables (ssaCharSourceFixture false 0xD800)) =
      "error:ub" := by native_decide

theorem ssa_char_source_valid_edge_stable :
    ws219Run (ws219NoTables (ssaCharSourceFixture false 0x10FFFF)) =
      "ok:return:[int32:42]" := by native_decide

theorem ssa_char_source_poison_binding_transports_stable :
    ws219Run (ws219NoTables (ssaCharSourceFixture true 0)) =
      "ok:return:[int32:42]" := by native_decide


/-- Transport checks do not read unwritten tuple/struct fields. -/
def closureUnwrittenContext : EvalContext :=
  { EvalContext.empty with
    structs := fun sid => if sid.index == 0 then some
      { id := ⟨0⟩, name := "Pair", size := none, align := none
        fields := [{name := "first", ty := .U32, offset := none},
          {name := "second", ty := .U32, offset := none}] }
      else none }

def closureTransportCode (ty : Ty) (value : Value) : String :=
  match checkClosureValue closureUnwrittenContext ty value with
  | .ok () => "ok"
  | .error error => error.code

theorem closure_tuple_unwritten_field_transports :
    closureTransportCode (.Tuple [.U32, .U32]) (.aggregate [.uninit, .int 32 42]) = "ok" := by
  native_decide

theorem closure_struct_unwritten_field_transports :
    closureTransportCode (.Struct ⟨0⟩) (.aggregate [.uninit, .int 32 42]) = "ok" := by
  native_decide

theorem closure_nested_unwritten_aggregate_transports :
    closureTransportCode (.Tuple [.Tuple [.U32, .U32]])
      (.aggregate [.aggregate [.uninit, .int 32 42]]) = "ok" := by
  native_decide

theorem closure_whole_unwritten_capture_still_faults :
    closureTransportCode .U32 .uninit = "ub" := by native_decide

theorem closure_whole_poison_capture_still_faults :
    closureTransportCode .U32 (.partial [none, none, none, none]) = "ub" := by native_decide

theorem closure_unwritten_field_does_not_hide_wrong_written_lane :
    closureTransportCode (.Tuple [.U32, .U32]) (.aggregate [.uninit, .bool true]) = "type_error" := by
  native_decide

theorem closure_unwritten_field_does_not_hide_wrong_arity :
    closureTransportCode (.Tuple [.U32, .U32]) (.aggregate [.uninit]) = "type_error" := by
  native_decide

theorem closure_transported_unwritten_lane_faults_at_field_read :
    (match Sem.run (semExtractField .U32 ⟨0⟩ 0)
      { MachineState.empty with locals := ValueMap.empty.set ⟨0⟩ (.aggregate [.uninit, .int 32 42]) } with
      | .error error => error.code
      | .ok _ => "ok") = "ub" := by native_decide
theorem compactArrayRuntimeProbe_ok : compactArrayRuntimeProbe = true := by native_decide
theorem compactArrayDenseProbe_ok : compactArrayDenseProbe = true := by native_decide
theorem compactArrayPointerProbe_ok : compactArrayPointerProbe = true := by native_decide

end ExecutableFixtures

end TrustIr
