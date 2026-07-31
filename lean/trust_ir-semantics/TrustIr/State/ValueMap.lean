-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- SSA value map: maps ValueId to concrete values.

import TrustIr.Basic
import TrustIr.Constant

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
  | ptr    : Nat → Value                            -- Pointer (address)
  | aggregate : List Value → Value                   -- Struct/array/tuple
  | vector : List Value → Value                      -- Fixed-width SIMD/vector lanes
  /-- Binding-frame value: heterogeneous slot list for typed binding
      frames. Kept nominally distinct from aggregate so the step
      relation rejects cross-flow (aggregate where a frame is required,
      and vice versa). Mirrors the Rust-side validation that forbids
      Store of a BindingFrame to generic memory. See
      designs/2026-04-19-binding-frames-lean-semantics.md section 2.3. -/
  | frame    : List Value → Value
  -- ty supremacy aggregate runtime values (issue #52 / #31 R3 gap).
  -- Runtime counterparts of Constant.set / .sequence / .record / .closure
  -- and Ty.Set / .Sequence / .Record / .Closure. Kept nominally distinct
  -- from aggregate so the step relation can reject cross-flow.
  | set      : List Value → Value
  | sequence : List Value → Value
  | record   : List (String × Value) → Value
  | closure  : FuncId → List Value → Value
  /-- Fat-pointer runtime value: a data address plus a reified metadata
      lane (B3 depth ledger "Fat-pointer values"). The runtime
      counterpart of `Ty.FatPtr`: slice/str metadata is the
      element/byte count (`.int 64 _`, the 64-bit model's `usize`);
      trait-object metadata is the vtable pointer (`.ptr _` /
      `.nullPtr`). THIN pointer-like values stay `.ptr` / `.nullPtr` —
      a thin pointer's metadata lane is `Unit` and is never reified
      into a `.fatPtr`. Produced only by `PtrFromParts` at a
      `Ty.FatPtr` type; consumed by `PtrData` / `PtrMetadata`
      (TrustIr/Semantics/Memory.lean). -/
  | fatPtr   : (data : Nat) → (metadata : Value) → Value
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
  | undef  : Ty → Value                             -- Undefined value
  | nullPtr : Value                                  -- Null pointer
  deriving Repr

/-- Returns a best-effort type of a concrete value.

    Scalar cases recover the static type exactly (for signed-integer
    widths; see note below). Aggregate, frame, and ty-supremacy
    values are context-dependent: they carry runtime shape (List Value)
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
  | .ptr _      => .Ptr
  | .aggregate _ => .Unit  -- aggregate type is context-dependent (#55)
  | .vector lanes => .Vector (lanes.length) .Unit
  | .frame _    => .Unit   -- frame type is context-dependent (carries BindingFrameId; #55)
  | .set _      => .Unit   -- set type is context-dependent (carries TyId/SetRepr; #55)
  | .sequence _ => .Unit   -- sequence type is context-dependent (carries TyId; #55)
  | .record _   => .Unit   -- record type is context-dependent (carries RecordId; #55)
  | .closure _ _ => .Unit  -- closure type is context-dependent (carries ClosureTyId; #55)
  | .fatPtr _ _ => .Unit   -- fat-ptr kind is context-dependent (the FatPtrKind lives on the producing Inst; #55)
  | .partial _  => .Unit   -- inert poison image; type is context-dependent (lives on the producing Load; like aggregate)
  | .undef ty   => ty
  | .nullPtr    => .Ptr

/-- Is this value a partially-initialized (poison) transport image? A poison
    value may only be copied or stored verbatim; inspecting it is UB. Mirrors
    the discriminant used by the Rust reference interpreter's `reject_partial`
    guard. -/
def Value.isPartial : Value → Bool
  | .partial _ => true
  | _          => false

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
