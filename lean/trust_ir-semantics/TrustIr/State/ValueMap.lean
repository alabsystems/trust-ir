-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- SSA value map: maps ValueId to concrete values.

import TrustIr.Basic
import TrustIr.Constant
import TrustIr.State.Memory
import TrustIr.State.CompactArray

namespace TrustIr

/-!
# Value Map

The SSA value map tracks the current value of each SSA variable.
In TrustIr's SSA form, each value is assigned exactly once.

## Concrete Values

A `Value` is the runtime representation of a TrustIr value. It carries
its type to enable dynamic type checking in the semantics.
-/

/-- Concrete runtime value. Each value is tagged with its type. -/
inductive Value where
  | int    : (width : Nat) → Int → Value          -- Integer with bit width
  | float  : Float → Value                          -- IEEE 754 float
  | bool   : Bool → Value                           -- Boolean
  /-- A thin pointer: its address and its PROVENANCE, the allocation it was
      derived from (`none`: a no-provenance pointer, the interpreter's
      `DanglingPtr`). -/
  | ptr    : Nat → Option AllocId → Value
  | array : CompactArray.Packed Value → Value
  | aggregate : List Value → Value                   -- Struct/tuple/enum field product
  | vector : List Value → Value                      -- Fixed-width SIMD/vector lanes
  /-- Binding-frame value: heterogeneous slot list for typed binding
      frames. Kept nominally distinct from aggregate so the step
      relation rejects cross-flow (aggregate where a frame is required,
      and vice versa). Mirrors the Rust-side validation that forbids
      Store of a BindingFrame to generic memory. See
      designs/2026-04-19-binding-frames-lean-semantics.md section 2.3. -/
  | frame    : (lineage : Nat) → List Value → Value
  -- ty supremacy aggregate runtime values (issue #52 / #31 R3 gap).
  -- Runtime counterparts of Constant.set / .sequence / .record / .closure
  -- and Ty.Set / .Sequence / .Record / .Closure. Kept nominally distinct
  -- from aggregate so the step relation can reject cross-flow.
  | set      : List Value → Value
  | sequence : List Value → Value
  | record   : List (String × Value) → Value
  | closure  : FuncId → List Value → Value
  /-- A typed function item retains its exact signature id and code identity.
      This is not a fabricated machine address or a nominal closure. -/
  | fnDef : FuncTyId → FuncId → Value
  /-- A first-class closure retains its nominal type, code identity and live
      capture values. Typed function items use `fnDef`; the untyped legacy
      constant projection `closure fn []` cannot masquerade as either. -/
  | typedClosure : ClosureTyId → FuncId → List Value → Value
  /-- Fat-pointer runtime value: a data address plus a reified metadata
      lane (B3 depth ledger "Fat-pointer values"). The runtime
      counterpart of `Ty.FatPtr`: slice/str/container-length metadata
      is the element/byte count (`.int 64 _`, the 64-bit model's
      `usize`); trait-object/container-vtable metadata is the vtable
      pointer (`.ptr _` / `.nullPtr`). THIN pointer-like values stay
      `.ptr` / `.nullPtr` — a thin pointer's metadata lane is `Unit` and
      is never reified into a `.fatPtr`. Produced only by `PtrFromParts`
      at a `Ty.FatPtr` type; consumed by `PtrData` / `PtrMetadata`
      (TrustIr/Semantics/Memory.lean). -/
  | fatPtr   : (data : Nat) → (dataProv : Option AllocId) → (metadata : Value) → Value
  /-- PARTIALLY-INITIALIZED scalar byte image — the copy-propagates-poison
      transport value (LLVM `poison` / Miri "uninitialized bytes"). The runtime
      counterpart of the Rust reference interpreter's
      `InterpretValueKind::PartialBytes` (crates/trust-ir/src/interpret.rs,
      commit 530fdd5). Produced by a NON-strict (plain, non-atomic,
      non-volatile) scalar `Load` whose byte range covers one or more
      never-written bytes — the whole-lane copy of an aggregate that reads
      struct-tail padding or an inactive niche-enum variant's payload. The list
      carries every byte of the load, `none` for an uninitialized byte.

      It is an INERT transport value: it may only be MOVED verbatim by `Copy`
      or WRITTEN back verbatim by a (non-strict) `Store` — both preserve which
      bytes stay uninitialized, so a later reload observes the same poison. ANY
      operation that INSPECTS its content (arithmetic, comparison, cast, a
      branch/switch condition, a field projection) is undefined behaviour and
      faults at that true use site (`Sem.rejectPartial`, plus the fact that
      every content-consuming semantic function has no `.partial` matching
      rule). This is NOT a blanket relaxation — transporting uninit is legal,
      consuming it is UB. -/
  | «partial» : List (Option UInt8) → Value
  /-- The POISON value `Undef` binds (ub-numerics-policy §4, roadmap WS2.10),
      also what `LoadSlot` reads from a slot no `BindSlot` has written
      (`initFrame`). It transports exactly like `.partial` (`Copy`, a `Select`
      arm, a non-strict `Store` — which writes `byteSize` uninitialized bytes —
      and a branch-edge block argument) and INSPECTING it is undefined
      behaviour at the same use sites (`Sem.rejectPartial`), including a call
      argument or return (`Sem.rejectPoisonValues`). The Rust reference
      interpreter binds the all-uninitialized `PartialBytes` image at scalar
      types and fails closed on a non-scalar `Undef`. -/
  | undef  : Ty → Value
  | nullPtr : Value                                  -- Null pointer
  /-- Crystal lane (E3b): an UNWRITTEN struct/tuple lane, the runtime counterpart of
      `Constant.uninit` and of the Rust reference interpreter's
      `InterpretValueKind::Uninit`. It exists only as an element of an `.aggregate`:
      `InsertField` replaces it, `ExtractField` of it is undefined behaviour (MIR's typed
      read of an uninitialised place, `semExtractField` via `Value.isUninit`), and the
      enclosing aggregate moves whole. It is never bound as an SSA value of its own
      (`Sem.rejectPartial` faults on it wherever it would be), so no content-consuming
      semantic function ever sees it. -/
  | uninit : Value
  /-- The zero-byte singleton of one nominal function-item type. Its identity
      comes from that type, including after an explicit byte reinterpretation. -/
  | fnItem : FuncId → Value
  /-- Source-bound binding-frame snapshot. The two IDs identify the original
      function-local declaration; values never supply their own slot types. -/
  | sourceFrame : (lineage : Nat) → FuncId → BindingFrameDef → List Value → Value
  deriving Repr

mutual
  /-- Actual nesting depth; compact storage edges and logical repetition counts
      do not add value nesting. No proof-only generated sizeOf runs at runtime. -/
  def Value.depthSpec (value : Value) : Nat :=
    match value with
    | .array ⟨size, tree⟩ => arrayTreeDepthRangeSpec tree 0 size + 1
    | .aggregate vs | .vector vs | .frame _ vs | .set vs | .sequence vs
    | .closure _ vs | .typedClosure _ _ vs | .sourceFrame _ _ _ vs => valueListDepthSpec vs + 1
    | .record fields => valueFieldDepthSpec fields + 1
    | .fatPtr _ _ metadata => metadata.depthSpec + 1
    | _ => 1
  termination_by sizeOf value
  decreasing_by all_goals (simp_wf <;> omega)
  def valueListDepthSpec (values : List Value) : Nat :=
    match values with
    | [] => 0
    | v :: vs => max v.depthSpec (valueListDepthSpec vs)
  termination_by sizeOf values
  decreasing_by all_goals (simp_wf <;> omega)
  def valueFieldDepthSpec (fields : List (String × Value)) : Nat :=
    match fields with
    | [] => 0
    | (_, v) :: vs => max v.depthSpec (valueFieldDepthSpec vs)
  termination_by sizeOf fields
  decreasing_by all_goals (simp_wf <;> omega)
  def arrayTreeDepthRangeSpec {size : Nat} (tree : CompactArray.Tree Value size)
      (offset count : Nat) : Nat :=
    let count := min count (size - offset)
    if count = 0 then 0 else
    match tree with
    | .uniform _ value => value.depthSpec
    | .dense _ values => arrayLeafDepthRangeSpec values offset count
    | .split (size := size) _ left right =>
      let before := min count (size / 2 - offset)
      max (arrayTreeDepthRangeSpec left offset before)
        (arrayTreeDepthRangeSpec right (offset + before - size / 2) (count - before))
    | .periodic (period := period) unit _ phase _ =>
      let start := (phase + offset) % period
      let before := min count (period - start)
      max (arrayTreeDepthRangeSpec unit start before)
        (arrayTreeDepthRangeSpec unit 0 (min period (count - before)))
  termination_by sizeOf tree
  decreasing_by all_goals (simp_wf <;> omega)
  def arrayLeafDepthRangeSpec {size : Nat} (leaf : CompactArray.Leaf Value size)
      (offset count : Nat) : Nat :=
    if count = 0 then 0 else
    match leaf with
    | .nil => 0
    | .cons value rest =>
      if offset = 0 then max value.depthSpec (arrayLeafDepthRangeSpec rest 0 (count - 1))
      else arrayLeafDepthRangeSpec rest (offset - 1) count
  termination_by sizeOf leaf
  decreasing_by all_goals (simp_wf <;> omega)
end

def arrayTreeDepthSpec {size : Nat} (tree : CompactArray.Tree Value size) : Nat :=
  arrayTreeDepthRangeSpec tree 0 size

def arrayLeafDepthSpec {size : Nat} (leaf : CompactArray.Leaf Value size) : Nat :=
  arrayLeafDepthRangeSpec leaf 0 size

namespace ValueDepthRuntime

/-- Counters describe traversal, not admission limits or proof authority. -/
structure Stats where
  visits : Nat := 0
  hits : Nat := 0
  deriving Repr

end ValueDepthRuntime

/-- Pure depth remains the logical meaning. Compiled traversal memoizes only
    completed results for retained exact input identities. This implementation
    boundary supplies no kernel theorem about physical pointer identity. -/
@[nospecialize, trustIrExtern 1 "l_TrustIr_Value_depth(#1)"]
def Value.depth (value : Value) : Nat := value.depthSpec

@[nospecialize, trustIrExtern 1 "l_TrustIr_valueListDepth(#1)"]
def valueListDepth (values : List Value) : Nat := valueListDepthSpec values

@[nospecialize, trustIrExtern 1 "l_TrustIr_valueFieldDepth(#1)"]
def valueFieldDepth (fields : List (String × Value)) : Nat := valueFieldDepthSpec fields

@[nospecialize, trustIrExtern 2 "l_TrustIr_arrayTreeDepth(#1, #2)"]
def arrayTreeDepth {size : Nat} (tree : CompactArray.Tree Value size) : Nat := arrayTreeDepthSpec tree

@[nospecialize, trustIrExtern 2 "l_TrustIr_arrayLeafDepth(#1, #2)"]
def arrayLeafDepth {size : Nat} (leaf : CompactArray.Leaf Value size) : Nat := arrayLeafDepthSpec leaf

/-- An address as a pointer VALUE with the provenance it recovers
    (`provenanceAt`); zero is the null pointer. The interpreter's
    `resolve_pointer_kind`. -/
def Memory.resolveAddr (mem : Memory) (addr : Addr) : Value :=
  if addr == 0 then .nullPtr else .ptr addr (mem.provenanceAt addr)

/-- Returns a best-effort type of a concrete value.

    Scalar cases recover the static type exactly (for signed-integer
    widths; see note below). Aggregate, frame, and ty-supremacy
    values are context-dependent: they carry runtime shape (lists or compact array trees)
    but the static Ty (TyId / BindingFrameId / RecordId / ClosureTyId)
    lives on the producing instruction, not on the Value. For those we
    return Ty.Unit as a zero-sized placeholder sentinel -- callers that
    need the precise static type must consult the generating Inst, not
    Value.ty. Issue #55 removed the prior Ty.Void sentinel used here
    in favour of Ty.Unit so the Lean Ty enum mirrors Rust exactly.

    Integer widths fall back to the signed variant when a value's tag
    does not encode signedness (the .int constructor carries only
    bit width). A Rust frontend that needs to preserve signedness
    must not route through Value.ty -- static Ty is the source of
    truth for signedness, and the semantic monad carries it on the
    instruction. -/
def Value.ty : Value → Ty
  | .int 8 _    => .I8
  | .int 16 _   => .I16
  | .int 32 _   => .I32
  | .int 64 _   => .I64
  | .int 128 _  => .I128
  | .int _ _    => .I64   -- fallback: should not happen for well-typed programs
  | .float _    => .F64
  | .bool _     => .Bool
  | .ptr _ _    => .Ptr
  | .array _ => .Unit
  | .aggregate _ => .Unit  -- aggregate type is context-dependent (#55)
  | .vector lanes => .Vector (lanes.length) .Unit
  | .frame _ _  => .Unit   -- frame type is context-dependent (carries BindingFrameId; #55)
  | .sourceFrame _ _ _ _ => .Ptr
  | .set _      => .Unit   -- set type is context-dependent (carries TyId/SetRepr; #55)
  | .sequence _ => .Unit   -- sequence type is context-dependent (carries TyId; #55)
  | .record _   => .Unit   -- record type is context-dependent (carries RecordId; #55)
  | .closure _ _ => .Unit  -- bare function item, without a nominal closure type
  | .fnDef sig _ => .Func sig
  | .fnItem fn => .FnItem fn
  | .typedClosure ty _ _ => .Closure ty
  | .fatPtr _ _ _ => .Unit   -- fat-ptr kind is context-dependent (the FatPtrKind lives on the producing Inst; #55)
  | .partial _  => .Unit   -- inert poison image; type is context-dependent (lives on the producing Load; like aggregate)
  | .undef ty   => ty
  | .nullPtr    => .Ptr
  | .uninit     => .Unit   -- an unwritten lane; its type is its position (like aggregate)

trustIrDenseMatch
/-- Is this value a partially-initialized (poison) transport image? A poison
    value may only be copied or stored verbatim; inspecting it is UB. Mirrors
    the discriminant used by the Rust reference interpreter's `reject_partial`
    guard. -/
def Value.isPartial : Value → Bool
  | .partial _ => true
  | _          => false

trustIrDenseMatch
/-- Is this value an UNWRITTEN aggregate lane (crystal lane, E3b)? Not poison:
    an unwritten lane is the absence of a value, and reading it out of its
    aggregate is undefined behaviour (`semExtractField`). -/
def Value.isUninit : Value → Bool
  | .uninit => true
  | _       => false

trustIrDenseMatch
/-- Is this value POISON — a partially-initialized image (`.partial`) or an
    `Undef` (`.undef`)? Poison may only be transported; inspecting it is UB
    (`Sem.rejectPartial`, `Sem.rejectPoisonValues`). -/
def Value.isPoison : Value → Bool
  | .partial _ => true
  | .undef _   => true
  | _          => false

#trustIrAxiomsExact TrustIr.Value.isPartial == []
#trustIrAxiomsExact TrustIr.Value.isUninit == []
#trustIrAxiomsExact TrustIr.Value.isPoison == []

/-- The value map: a function from ValueId to optional Value.
    Returning `none` means the value is not yet defined (SSA violation). -/
def ValueMap := ValueId → Option Value

/-- Empty value map: no values defined. -/
def ValueMap.empty : ValueMap := fun _ => none

/-- Lookup a value in the map. -/
def ValueMap.get (m : ValueMap) (id : ValueId) : Option Value := m id

/-- Bind a value to an SSA variable. -/
def ValueMap.set (m : ValueMap) (id : ValueId) (v : Value) : ValueMap :=
  fun id' => if id' == id then some v else m id'

instance : Repr ValueMap where
  reprPrec _ _ := "<ValueMap>"

end TrustIr
