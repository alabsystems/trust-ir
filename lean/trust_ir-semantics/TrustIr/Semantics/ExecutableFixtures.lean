-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Executable reference-semantics fixtures with stable observable outcomes.
-- These are intentionally small and target-independent: integer wrapping,
-- casts, vector select, structured unsupported cases, and fuel behavior.

import TrustIr.Semantics.Eval
import TrustIr.Semantics.VectorDialect

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
  | .ptr addr => s!"ptr:{addr}"
  | .aggregate values => s!"aggregate({values.length})"
  | .vector lanes => s!"vector({lanes.length})"
  | .frame values => s!"frame({values.length})"
  | .set values => s!"set({values.length})"
  | .sequence values => s!"sequence({values.length})"
  | .record fields => s!"record({fields.length})"
  | .closure func captures => s!"closure:{func.index}:{captures.length}"
  | .fatPtr data metadata => s!"fatptr:{data}:" ++ stableValueAtomString metadata
  | .partial image => s!"partial({image.length})"
  | .undef ty => s!"undef:{repr ty}"
  | .nullPtr => "null"

/-- Stable rendering for top-level fixture values. -/
def stableValueString : Value → String
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
  | .terminator result => "terminator:" ++ StepResult.stableString result

end InstrResult

/-- Stable observable outcome for a single instruction. -/
def stepInstStableOutcome (inst : Inst) (state : MachineState) : String :=
  match Sem.run (stepInst inst) state with
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

-- Fat-pointer trio locks (PtrData / PtrMetadata / PtrFromParts). The THIN
-- fixtures agree with the reference interpreter (interpret.rs eval_ptr_data /
-- eval_ptr_metadata / eval_ptr_from_parts); the FAT fixtures pin the shared
-- `(data, metadata)` `Value.fatPtr` model and its 16-byte memory image.

def thinPtrState : MachineState := stateWith [(v0, .ptr 4096)] 1

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
  stateWith [(v0, .ptr 4096), (v1, .aggregate [])] 2

/-- Thin `ptr_from_parts` is the identity on the data pointer. -/
theorem ptr_from_parts_thin_identity_stable :
    stepInstStableOutcome (.PtrFromParts .Ptr .Unit v0 v1) thinFromPartsState =
      "ok:value:ptr:4096" := by
  native_decide

def fatSliceTy : Ty := .FatPtr (.Slice (TyId.mk 0))
def fatSliceState : MachineState :=
  stateWith [(v0, .fatPtr 4096 (.int 64 3))] 1

/-- Fat `ptr_data` projects the data lane as a thin pointer. -/
theorem ptr_data_fat_projects_stable :
    stepInstStableOutcome (.PtrData fatSliceTy v0) fatSliceState =
      "ok:value:ptr:4096" := by
  native_decide

def fatSliceNullState : MachineState :=
  stateWith [(v0, .fatPtr 0 (.int 64 3))] 1

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
  stateWith [(v0, .fatPtr 4096 (.int 32 3))] 1

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
  stateWith [(v0, .ptr 4096), (v1, .int 64 3)] 2

/-- Fat `ptr_from_parts` injects (data, metadata) into a `.fatPtr`. -/
theorem ptr_from_parts_fat_injects_stable :
    stepInstStableOutcome (.PtrFromParts fatSliceTy .U64 v0 v1) fatFromPartsState =
      "ok:value:fatptr:4096:int64:3" := by
  native_decide

def fatFromPartsBadMetaState : MachineState :=
  stateWith [(v0, .ptr 4096), (v1, .int 32 3)] 2

/-- The metadata operand must INHABIT the declared metadata type
    (an i32 is not a usize length). -/
theorem ptr_from_parts_fat_bad_metadata_stable :
    stepInstStableOutcome (.PtrFromParts fatSliceTy .U64 v0 v1) fatFromPartsBadMetaState =
      "error:type_error" := by
  native_decide

def dynTraitTy : Ty := .FatPtr (.TraitObject 7)
def dynFromPartsState : MachineState :=
  stateWith [(v0, .ptr 4096), (v1, .ptr 8192)] 2

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

/-- A malformed metadata lane fails closed at the byte-image boundary. -/
theorem fat_ptr_bad_metadata_encoding_rejected :
    encodeValue (.fatPtr 4096 (.int 32 3)) = none := by
  native_decide

theorem fat_ptr_float_metadata_encoding_rejected :
    encodeValue (.fatPtr 4096 (.float 3.0)) = none := by
  native_decide

def fatPtrMemoryState (value : Value) : MachineState :=
  let (addr, mem) := Memory.empty.alloc 16 .rustStack
  { (stateWith [(v0, .ptr addr), (v1, value)] 2) with memory := mem }

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
    fatPtrMemoryRoundTripOutcome fatSliceTy (.fatPtr 4096 (.int 64 3)) =
      "ok:fatptr:4096:int64:3" := by
  native_decide

/-- Trait-object vtable metadata uses the same second pointer-sized lane and
    survives Store/Load without being confused with slice length metadata. -/
theorem fat_trait_memory_round_trip_stable :
    fatPtrMemoryRoundTripOutcome dynTraitTy (.fatPtr 4096 (.ptr 8192)) =
      "ok:fatptr:4096:ptr:8192" := by
  native_decide

/-- Even though a pointer is one lane wide, it cannot be stored as slice
    length metadata: Store checks the kind, not just the encoded byte count. -/
theorem fat_slice_memory_rejects_pointer_metadata_stable :
    fatPtrMemoryRoundTripOutcome fatSliceTy (.fatPtr 4096 (.ptr 8192)) =
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
      let _ ← stepInst (.Alloca .I64 none)
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
-- results; a directly-executed LandingPad binds (null, 0); Resume is a
-- structured unsupported (host unwinding is outside the model).

/-- A directly-executed landing pad binds a null exception pointer and zero
    type selector, packed per the Overflow aggregate-pair convention. -/
theorem landing_pad_direct_binds_null_selector_stable :
    stepInstStableOutcome (.LandingPad true []) (stateWith [] 0) =
      "ok:value:aggregate[null,int32:0]" := by
  native_decide

/-- Resume is a structured unsupported: the executable model never has an
    in-flight host exception (panic=abort; unwind edges are never taken). -/
theorem resume_is_structured_unsupported_stable :
    stepInstStableOutcome (.Resume v0) (stateWith [(v0, .nullPtr)] 1) =
      "error:unsupported.host_unwind" := by
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
    stepInstStableOutcome (.Assert v0) assertBoolTrueState =
      "ok:value:none" := by
  native_decide

def assertBoolFalseState : MachineState := stateWith [(v0, .bool false)] 1
theorem assert_bool_false_panics_stable :
    stepInstStableOutcome (.Assert v0) assertBoolFalseState =
      "error:panic" := by
  native_decide

/-- A NONZERO integer condition is a type error, not a pass: Assert does no
    truthiness coercion. This fixture FAILS under the former int-accepting
    Lean semantics, locking the interpreter alignment. -/
def assertIntOneState : MachineState := stateWith [(v0, .int 32 1)] 1
theorem assert_int_condition_type_error_stable :
    stepInstStableOutcome (.Assert v0) assertIntOneState =
      "error:type_error" := by
  native_decide

def assertIntZeroState : MachineState := stateWith [(v0, .int 32 0)] 1
theorem assert_int_zero_condition_type_error_stable :
    stepInstStableOutcome (.Assert v0) assertIntZeroState =
      "error:type_error" := by
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

def transmuteFloatState : MachineState :=
  stateWith [(v0, .float 1.5)] 1

theorem transmute_float_rejected_stable :
    stepInstStableOutcome (.Cast .Transmute .F64 .I64 v0) transmuteFloatState =
      "error:unsupported.vector_shape" := by
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
-- (1025, after the size-1 reservation advanced the allocator past 1024).
theorem global_addr_distinct_addrs_stable :
    stepTwoInstStableOutcome
      (.GlobalAddr (GlobalId.mk 0)) (.GlobalAddr (GlobalId.mk 1)) MachineState.empty =
      "ok:value:ptr:1025" := by
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

theorem unsupported_v8i8_icmp_code_stable :
    stepInstStableOutcome (.ICmp .Eq (.Vector 8 .I8) v0 v1)
        vectorI8CompareState =
      "error:unsupported.vector_type" := by
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
      "error:unsupported.vector_shape" := by
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

def unsupportedVectorState : MachineState :=
  stateWith [(v0, v8i32), (v1, v8i32)] 2

theorem unsupported_v8i32_binop_code_stable :
    stepInstStableOutcome (.BinOp .Add (.Vector 8 .I32) v0 v1)
        unsupportedVectorState =
      "error:unsupported.vector_type" := by
  native_decide

def unsupportedVectorElementState : MachineState :=
  stateWith [(v0, v8i32), (v1, .int 64 1), (v2, .int 32 99)] 3

theorem unsupported_v8i32_insert_element_code_stable :
    stepInstStableOutcome (.InsertElement (.Vector 8 .I32) v0 v1 v2)
        unsupportedVectorElementState =
      "error:unsupported.vector_shape" := by
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
-- Lean: the alive checks in semDealloc / Memory.isInBounds /
-- getAllocIdFromPtrARC). Symbolic twins: semDealloc_twice_is_ub,
-- semLoad_after_dealloc_is_ub, semRelease_after_last_release_is_ub
-- (Proofs/MemorySafety.lean). Rust twins: b2_heapalloc.rs heap-lifetime tests
-- and interpret.rs use_after_dealloc_reports_undefined_behavior_code.

-- Alloca binds the pointer as v0 from the empty state's nextValueId = 0.
theorem dealloc_once_ok_stable :
    stepTwoInstStableOutcome (.Alloca .I32 none) (.Dealloc v0)
        MachineState.empty =
      "ok:value:none" := by
  native_decide

theorem dealloc_twice_ub_code_stable :
    stepThreeInstStableOutcome (.Alloca .I32 none) (.Dealloc v0) (.Dealloc v0)
        MachineState.empty =
      "error:ub" := by
  native_decide

theorem load_after_dealloc_ub_code_stable :
    stepThreeInstStableOutcome (.Alloca .I32 none) (.Dealloc v0)
        (.Load .I32 v0 false none) MachineState.empty =
      "error:ub" := by
  native_decide

/-- A live ARC allocation with `arcRef` permission and refcount 2 at v0. -/
def arcTwoRefState : MachineState :=
  let (addr, mem) := Memory.empty.alloc 4 .swiftHeap
  { MachineState.empty with
    memory      := mem
    permissions := PermissionMap.empty.set (AllocId.mk 0) .arcRef
    refCounts   := setRefCount RefCountMap.empty (AllocId.mk 0) 2
    locals      := ValueMap.empty.set v0 (.ptr addr)
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
-- Honest model boundary: `semHeapAlloc` grants `owned` for EVERY origin, and
-- the ARC ops require `arcRef` — the permission the producer's RC runtime
-- establishes (Clean: `clean_alloc_ctor`). So, exactly like the swiftHeap
-- fixtures above, the lifecycle fixtures start from the runtime-initialized
-- fresh-cell state (arcRef, refcount 1) rather than from a bare `HeapAlloc`.

/-- `HeapAlloc` with the CleanHeap origin executes: origin is provenance
    only, so the fresh Clean cell gets the same first address as any other
    origin (`Memory.empty` reserves the null page below 1024). -/
theorem heap_alloc_clean_heap_stable :
    stepInstStableOutcome (.HeapAlloc .I32 none .CleanHeap)
        MachineState.empty =
      "ok:value:ptr:1024" := by
  native_decide

/-- `HeapAlloc` outcome parity between the CleanHeap and SwiftHeap origins. -/
theorem heap_alloc_clean_swift_parity_stable :
    stepInstStableOutcome (.HeapAlloc .I32 none .CleanHeap)
        MachineState.empty =
      stepInstStableOutcome (.HeapAlloc .I32 none .SwiftHeap)
        MachineState.empty := by
  native_decide

/-- A fresh Clean Perceus cell as `clean_alloc_ctor` leaves it: cleanHeap
    origin, `arcRef` permission, refcount 1 (one owner), pointer at v0.
    Twin of `arcLastRefState` — the states differ only in the origin tag. -/
def cleanFreshCellState : MachineState :=
  let (addr, mem) := Memory.empty.alloc 4 .cleanHeap
  { MachineState.empty with
    memory      := mem
    permissions := PermissionMap.empty.set (AllocId.mk 0) .arcRef
    refCounts   := setRefCount RefCountMap.empty (AllocId.mk 0) 1
    locals      := ValueMap.empty.set v0 (.ptr addr)
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
      terminator := .CallIndirect v0 sig0 [] }

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
        (evalFunctionInContext indirectCallContext f0 [.ptr ptr0] 2)
        MachineState.empty =
      "ok:return:[int32:41]" := by
  native_decide

def indirectBodyCallCFG : CFG :=
  singletonCFG
    { params := [(v0, .Ptr)]
      body := [.CallIndirect v0 sig0 []]
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
        (evalFunctionInContext indirectBodyCallContext f0 [.ptr ptr0] 2)
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
        (evalFunctionInContext indirectSignatureMismatchContext f0 [.ptr ptr0] 2)
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
        (evalFunctionInContext invalidFunctionPointerContext f0 [.ptr ptr0] 2)
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

/-- Float elements are a STRUCTURED unsupported (the placeholder float byte
    codec would silently zero them; interpret.rs computes real float maps, so
    this is a documented executable-subset boundary, not silent wrongness). -/
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

theorem seq_map_float_elements_structured_unsupported_stable :
    evalValuesStableOutcome
        (evalFunctionInContext seqMapF64Context f0
          [.sequence [.float 1.5]] 2)
        MachineState.empty =
      "error:unsupported.vector_shape" := by
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
  let (a0, mem) := Memory.empty.alloc 8 .rustStack
  let mem := mem.writeBytes a0 [1, 2, 3, 4]      -- a0..a0+4 init; a0+4..a0+8 uninit
  let (a1, mem) := mem.alloc 8 .rustStack
  { (stateWith [(v0, .ptr a0), (v1, .ptr a1)] 2) with memory := mem }

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

-- Load/Store alignment (mirror interpret.rs `checked_access`, commit dd27b78):
-- a non-atomic access under-aligned for its declared alignment is UB.

/-- A 16-byte cell whose first eight bytes are written. `v0` points at the base
    (address 1024, 8-aligned), `v1` at base+1 (address 1025, odd), and `v2`
    holds a byte value to store. -/
def alignTestState : MachineState :=
  let (base, mem) := Memory.empty.alloc 16 .rustStack   -- base = 1024
  let mem := mem.writeBytes base [10, 11, 12, 13, 14, 15, 16, 17]
  { (stateWith [(v0, .ptr base), (v1, .ptr (base + 1)), (v2, .int 8 99)] 3)
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

end ExecutableFixtures

end TrustIr
