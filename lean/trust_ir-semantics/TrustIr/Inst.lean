-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Instruction enum — the complete TrustIr instruction set.
-- Mirrors: crates/trust_ir/src/inst.rs (Inst, SwitchCase)

import TrustIr.Basic
import TrustIr.BinOp
import TrustIr.CmpOp
import TrustIr.CastOp
import TrustIr.Ordering
import TrustIr.Constant
import TrustIr.DialectInst

namespace TrustIr

/-!
# TrustIr Instruction Set

Mirrors Rust `trust_ir::Inst` exactly (all 30+ variants).

Instructions are organized by category:
- Arithmetic: BinOp, UnOp, Overflow
- Comparison: ICmp, FCmp
- Casts: Cast
- Memory: Load, Store, Alloca, GEP, Dealloc, MemCopy, MemSet (WS3.20)
- Atomics: AtomicLoad, AtomicStore, AtomicRMW, CmpXchg, Fence
- Control flow: Br, CondBr, Switch, Call, CallIndirect, Return
- Aggregates: ExtractField, InsertField, MakeAggregate, ArraySplat, ExtractElement, InsertElement
- Constants: Const, NullPtr, Undef
- Proof: Assume, Assert, Unreachable
- Pseudo: Copy, Select
- Binding frames: OpenFrame, BindSlot, LoadSlot, CloseFrame
- Dialect: DialectOp

## Borrow instructions
- Borrow, BorrowMut, EndBorrow (Rust ownership model)
- Retain, Release, IsUnique (Swift ARC model)

These are present in both the Rust Inst enum (crates/trust_ir/src/inst.rs)
and this Lean formalization. The Rust has_side_effects implementation
correctly classifies all Borrow/ARC instructions as side-effecting.

## Dealloc and DialectOp (TrustIr issue 54)

Dealloc mirrors Rust Inst.Dealloc { ptr }. Semantic target:
TrustIr.Semantics.Memory.semDealloc (marks the allocation dead, clears
its permission, and zeros its refcount — observable state change).

DialectOp mirrors Rust Inst.DialectOp(Box DialectInst). Its payload
is the non-semantic DialectInst carrier (see TrustIr.DialectInst).
stepInst refuses to evaluate a DialectOp with a structured unsupported
error: core TrustIr semantics do not include dialect semantics; dialect-aware
passes must lower the op to core instructions before evaluation. The
lowering-correctness obligation is formalised in TrustIr.Semantics.Dialect.
-/

/-- Switch case entry. Mirrors Rust `trust_ir::SwitchCase`. -/
structure SwitchCase where
  value      : Constant
  target     : BlockId
  args       : List ValueId
  deriving Repr

/-!
## Binding frames

Typed binding frames are the lowering target for quantifier and
bounded-iteration constructs. Four instructions (OpenFrame, BindSlot,
LoadSlot, CloseFrame) create and manipulate a typed heterogeneous
record keyed by slot index.

The slot layout lives inline on Inst.OpenFrame via a BindingFrameDef.
Mirrors Rust crates/trust_ir/src/inst.rs. See
designs/2026-04-19-binding-frames-lean-semantics.md section 2.
-/

/-- A single typed slot in a binding frame. Mirrors Rust
    trust_ir::inst::BindingSlot from crates/trust_ir/src/inst.rs.

    Each slot has a name (diagnostics / text format) and a declared Ty.
    The position in BindingFrameDef.slots is the slot index used by
    Inst.BindSlot and Inst.LoadSlot. -/
structure BindingSlot where
  name : String
  ty   : Ty
  deriving Repr

/-- Declaration of a binding frame's slot layout. Inline in
    Inst.OpenFrame, matching Rust trust_ir::inst::BindingFrameDef
    (crates/trust_ir/src/inst.rs).

    The id is unique within a function (Rust-side validation). The
    semantics does not depend on that uniqueness; see
    designs/2026-04-19-binding-frames-lean-semantics.md section 8. -/
structure BindingFrameDef where
  id    : BindingFrameId
  name  : String
  slots : List BindingSlot
  deriving Repr

namespace BindingFrameDef

/-- Number of declared slots. -/
def slotCount (d : BindingFrameDef) : Nat := d.slots.length

end BindingFrameDef

/-- Heap allocation origin, mirroring Rust `trust_ir::AllocOrigin` (a subset of
the memory model's `AllocationOrigin`). Carried by `Inst.HeapAlloc`. -/
inductive AllocOrigin where
  | RustHeap : AllocOrigin
  | SwiftHeap : AllocOrigin
  | CMalloc : AllocOrigin
  | CleanHeap : AllocOrigin
  deriving Repr, DecidableEq

/-- The operation whose overflow an `AssertKind.Overflow` check guards
    (plan item P, wire v52). Mirrors Rust `trust_ir::AssertOverflowOp`. -/
inductive AssertOverflowOp where
  | Add : AssertOverflowOp
  | Sub : AssertOverflowOp
  | Mul : AssertOverflowOp
  | Div : AssertOverflowOp
  | Rem : AssertOverflowOp
  | Shl : AssertOverflowOp
  | Shr : AssertOverflowOp
  | Neg : AssertOverflowOp
  deriving Repr, DecidableEq

/-- WHICH Rust panic a failed `Inst.Assert` is (plan item P, wire v52).
    Mirrors Rust `trust_ir::AssertKind`. The kind changes only the panic
    MESSAGE (`Semantics/Step.lean`, `assertFailMessage`), never whether the
    assert fails: that is still exactly `cond = false`. `Unspecified` is the
    kind of every pre-v52 assert. The operand-carrying kinds name the values
    the message prints, read only on failure. -/
inductive AssertKind where
  | Unspecified : AssertKind
  | Overflow (op : AssertOverflowOp) : AssertKind
  | DivByZero : AssertKind
  | RemByZero : AssertKind
  | BoundsCheck (index : ValueId) (len : ValueId) : AssertKind
  | MisalignedPtr (required : ValueId) (found : ValueId) : AssertKind
  | NullPtr : AssertKind
  deriving Repr

/-- The panic message of an operand-free kind, byte-identical to the Rust
    `AssertKind::constant_panic_message` (and to `core`'s text for every kind
    but `Unspecified`, whose `"assertion failed"` is the engines' own). The
    operand kinds' messages are built in `Semantics/Step.lean`. -/
def AssertKind.constantMessage : AssertKind → String
  | .Unspecified => "assertion failed"
  | .Overflow .Add => "attempt to add with overflow"
  | .Overflow .Sub => "attempt to subtract with overflow"
  | .Overflow .Mul => "attempt to multiply with overflow"
  | .Overflow .Div => "attempt to divide with overflow"
  | .Overflow .Rem => "attempt to calculate the remainder with overflow"
  | .Overflow .Shl => "attempt to shift left with overflow"
  | .Overflow .Shr => "attempt to shift right with overflow"
  | .Overflow .Neg => "attempt to negate with overflow"
  | .DivByZero => "attempt to divide by zero"
  | .RemByZero => "attempt to calculate the remainder with a divisor of zero"
  | .NullPtr => "null pointer dereference occurred"
  | .BoundsCheck _ _ => "index out of bounds"
  | .MisalignedPtr _ _ => "misaligned pointer dereference"

/-- Where a failed check's panic is reported: the LAST argument of its panic
    site's entry (amendment P, wire v54; `docs/SPEC_RATIFICATIONS.md` §19.1).
    Mirrors Rust `trust_ir::PanicLocation`. `global g` is the address of an
    immutable module global holding the record, the one spelling of a
    location known at compile time; `value v` is a run-time location (a
    `#[track_caller]` function forwarding its caller's). No IR semantics
    reads the record's bytes. -/
inductive PanicLocation where
  | global (g : GlobalId) : PanicLocation
  | value (v : ValueId) : PanicLocation
  deriving Repr

/-- How a failed assert is realized (amendment P, wire v54): call
    `entry(kind operands.., location)`. Mirrors Rust `trust_ir::PanicSite`.
    The executable model never executes the entry: a failed check is a
    terminal panic outcome that NAMES it (`Semantics/Step.lean`,
    `semAssertFail`). -/
structure PanicSite where
  entry : FuncId
  location : PanicLocation
  deriving Repr

/-- TrustIr instruction. Mirrors Rust `trust_ir::Inst`.

    This is the core of the TrustIr formalization: every instruction
    variant has a corresponding semantic function in TrustIr.Semantics.

    Note: Borrow/ARC instructions mirror the Rust Inst enum
    (crates/trust_ir/src/inst.rs) including has_side_effects classification. -/
inductive Inst where
  -- Arithmetic
  | BinOp        (op : BinOp) (ty : Ty) (lhs rhs : ValueId) : Inst
  | UnOp         (op : UnOp) (ty : Ty) (operand : ValueId) : Inst
  | Overflow     (op : OverflowOp) (ty : Ty) (lhs rhs : ValueId) : Inst

  -- Comparison
  | ICmp         (op : ICmpOp) (ty : Ty) (lhs rhs : ValueId) : Inst
  | FCmp         (op : FCmpOp) (ty : Ty) (lhs rhs : ValueId) : Inst

  -- Casts
  | Cast         (op : CastOp) (srcTy dstTy : Ty) (operand : ValueId) : Inst

  -- Memory
  -- `volatile`/`align` mirror Rust `Inst::Load`/`Store` (a volatile access is
  -- observable; `align` is the access alignment, misalignment being UB). The
  -- executable subset's `semLoad`/`semStore` model the value transfer; the
  -- volatile observability shows up in `hasSideEffects`, while precise
  -- misalignment-UB is a deferred memory-model refinement.
  | Load         (ty : Ty) (ptr : ValueId) (volatile : Bool) (align : Option Nat) : Inst
  | Store        (ty : Ty) (ptr : ValueId) (value : ValueId) (volatile : Bool) (align : Option Nat) : Inst
  -- `align` mirrors Rust `Inst::Alloca`/`HeapAlloc { align }` (the requested
  -- allocation alignment, `none` = the type's natural alignment). Carried for
  -- field-level parity (WS2.18); the executable model does not yet place
  -- allocations at a requested alignment — a recorded depth gap
  -- (docs/roadmap/B3-lean-ir-parity.md), exactly like `Load`/`Store` `align`.
  | Alloca       (ty : Ty) (count : Option ValueId) (align : Option Nat) : Inst
  | HeapAlloc    (ty : Ty) (count : Option ValueId) (align : Option Nat)
                 (origin : AllocOrigin) : Inst
  -- `inbounds` mirrors Rust `Inst::GEP { inbounds }` (fast-3): a claim that the
  -- computed address stays within the base allocation (poison/UB otherwise).
  -- The poison-on-out-of-bounds semantics + inbounds-folding theorem are the
  -- deferred deep refinement (see TrustIr/Proofs/MemoryProps.lean §"GEP in-
  -- bounds"); the field is modelled here so the Lean Inst matches Rust's shape.
  | GEP          (pointeeTy : Ty) (base : ValueId) (indices : List ValueId) (inbounds : Bool) : Inst
  -- Fat-pointer trio (thin identity regime plus first-class Ty.FatPtr regime).
  | PtrData      (ptrTy : Ty) (ptr : ValueId) : Inst
  | PtrMetadata  (ptrTy : Ty) (metadataTy : Ty) (ptr : ValueId) : Inst
  | PtrFromParts (ptrTy : Ty) (metadataTy : Ty) (data : ValueId) (metadata : ValueId) : Inst
  -- Address-of a module-level global (B1). Materializes a cached pointer.
  | GlobalAddr   (global : GlobalId) : Inst

  -- Atomics
  | AtomicLoad   (ty : Ty) (ptr : ValueId) (ordering : MemOrdering) : Inst
  | AtomicStore  (ty : Ty) (ptr : ValueId) (value : ValueId) (ordering : MemOrdering) : Inst
  | AtomicRMW    (op : AtomicRMWOp) (ty : Ty) (ptr : ValueId)
                 (value : ValueId) (ordering : MemOrdering) : Inst
  -- `weak` mirrors Rust Inst::CmpXchg's `weak` flag (crystal D3). A WEAK
  -- compare-exchange may fail SPURIOUSLY -- report `false` and store nothing
  -- even when the loaded value equals `expected` -- so its outcome is not a
  -- function of the state. `Sem` has no nondeterminism source, so stepping it
  -- as strong would execute one of its two legal outcomes and call that its
  -- semantics. Semantics: TrustIr.Semantics.Step -- a STRUCTURED UNSUPPORTED
  -- (`unsupported.weak_cmpxchg`), matching the reference interpreter, which
  -- refuses it too. `weak = false` is the historical strong instruction.
  | CmpXchg      (ty : Ty) (ptr : ValueId) (expected desired : ValueId)
                 (success failure : MemOrdering) (weak : Bool) : Inst
  | Fence        (ordering : MemOrdering) : Inst

  -- Control flow
  | Br           (target : BlockId) (args : List ValueId) : Inst
  | CondBr       (cond : ValueId) (thenTarget : BlockId) (thenArgs : List ValueId)
                 (elseTarget : BlockId) (elseArgs : List ValueId) : Inst
  -- `exhaustiveEnumUnreachable` mirrors Rust `Inst::Switch
  -- { exhaustive_enum_unreachable }` (binary v15): the producer's claim that
  -- the cases cover every enum discriminant, so the default edge is dead. It
  -- is a codegen license, not a value rule: the reference interpreter takes
  -- the default edge on a miss regardless, and so does `semSwitch`. Carried so
  -- a `true` and a `false` switch are DISTINCT Lean instructions (WS2.18).
  | Switch       (value : ValueId) (default_ : BlockId) (defaultArgs : List ValueId)
                 (cases : List SwitchCase) (exhaustiveEnumUnreachable : Bool) : Inst
  | Call         (callee : FuncId) (args : List ValueId) : Inst
  | CallIndirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId)
                 (callingConv : CallingConv) : Inst
  -- Normative no-crossing unwind boundaries, NOT NoPanic assertions. The
  -- executable model refuses them until host unwinding is modeled.
  | CallCannotUnwind (callee : FuncId) (args : List ValueId) : Inst
  | CallIndirectCannotUnwind (callee : ValueId) (sig : FuncTyId) (args : List ValueId)
                 (callingConv : CallingConv) : Inst
  | Return       (values : List ValueId) : Inst

  -- Aggregates
  | ExtractField   (ty : Ty) (aggregate : ValueId) (field : Nat) : Inst
  | InsertField    (ty : Ty) (aggregate : ValueId) (field : Nat) (value : ValueId) : Inst
  /-- Build a fully-initialised aggregate VALUE from declaration-ordered
      register lanes (WS3.5, F-049 register-seed half). `variant` is `some v`
      exactly for an enum (the tag is `discriminants[v]`, never a lane) and
      `none` for a struct / tuple / record / array. Mirrors Rust
      `Inst::MakeAggregate { ty, variant, fields }`. -/
  | MakeAggregate  (ty : Ty) (variant : Option Nat) (fields : List ValueId) : Inst
  /-- Runtime captures. The executable model refuses this until its closure
      tables and checked physical target signatures are operational. -/
  | MakeClosure (ty : ClosureTyId) (func : FuncId) (captures : List ValueId) : Inst
  /-- `n` copies of one register value: the array `[value; n]` of type
      `ty = Array e n` (wire v50). The register twin of `Constant.splat`,
      denoted `.aggregate (List.replicate n v)`. Mirrors Rust
      `Inst::ArraySplat { ty, value }`. -/
  | ArraySplat     (ty : Ty) (value : ValueId) : Inst
  | ExtractElement (ty : Ty) (array : ValueId) (index : ValueId) : Inst
  | InsertElement  (ty : Ty) (array : ValueId) (index : ValueId) (value : ValueId) : Inst

  -- Constants
  | Const        (ty : Ty) (value : Constant) : Inst
  | NullPtr      : Inst
  | Undef        (ty : Ty) : Inst

  -- Proof instructions
  | Assume       (cond : ValueId) : Inst
  /-- A runtime check; `kind` names the Rust panic its failure is (wire v52)
      and `site` the entry a failure calls and the location it reports
      (amendment P, wire v54; `none` is an unsited check). -/
  | Assert       (cond : ValueId) (kind : AssertKind) (site : Option PanicSite) : Inst
  | Unreachable  : Inst

  -- Pseudo instructions
  | Copy         (ty : Ty) (operand : ValueId) : Inst
  /-- Branchless selection.

      Lean execution accepts scalar `Bool` as whole-value selection and a
      same-lane `<N x Bool>` masks at every positive admitted lane count.
      Physical integer masks such as x86 `<N x i32>` all-ones/zero lanes are
      lowering details, not TrustIr source conditions. -/
  | Select       (ty : Ty) (cond : ValueId) (thenVal elseVal : ValueId) : Inst

  -- Sequence element-op loops (give-back / Aeneas loopFwd). Mirrors Rust
  -- Inst::SeqMapAddK / Inst::SeqMapNot (crates/trust-ir/src/inst.rs).
  /-- Structural element-wise constant increment of a sequence: produces a
      new sequence with every element incremented by the constant `k`, each
      at its own bit width with the SAME wrapping semantics as `BinOp Add`
      (the loop body of `for x in &mut l { *x += k }`). -/
  | SeqMapAddK   (ty : Ty) (seq : ValueId) (k : Nat) : Inst
  /-- Structural element-wise boolean flip of a sequence: produces a new
      sequence with every element negated (`Bool.not`), i.e. the loop body
      of `for b in &mut l { *b = !*b }`. Self-inverse. -/
  | SeqMapNot    (ty : Ty) (seq : ValueId) : Inst

  -- Sequence element-op map (give-back loop instruction family)
  /-- Structural element-wise map of a sequence by a first-class element
      function: `SeqMap ty seq fwd` produces a new sequence with `fwd`'s
      forward semantics applied to every element (Aeneas `loopFwd` for
      `for x in &mut l { *x = fwd(x) }`). `fwd` is the `FuncId` of a
      single-`&mut` element function `fn(&mut elem)`; each element
      round-trips through a per-element memory cell. Applying `fwd` is
      interprocedural, so `stepInst` returns a `StepResult.SeqMapReq` and
      the contextual evaluator (`stepNWithContext`) runs the element calls
      (ONE call-depth level for the whole map — depth bounds NESTING, not
      sequence length). Mirrors Rust `Inst::SeqMap`
      (crates/trust-ir/src/inst.rs); design:
      designs/2026-06-30-general-seqmap-instruction.md. -/
  | SeqMap       (ty : Ty) (seq : ValueId) (fwd : FuncId) : Inst

  -- Borrow instructions (Rust ownership model)
  -- Mirrors Rust Inst enum. Reference: Ho & Protzenko, "Aeneas", ICFP 2022
  | Borrow       (ptr : ValueId) : Inst
  | BorrowMut    (ptr : ValueId) : Inst
  | EndBorrow    (borrowPtr : ValueId) : Inst

  -- ARC instructions (Swift reference counting model)
  -- Mirrors Rust Inst enum.
  | Retain       (ptr : ValueId) : Inst
  | Release      (ptr : ValueId) : Inst
  | IsUnique     (ptr : ValueId) : Inst

  -- Heap deallocation (free / Box::drop). Mirrors Rust Inst::Dealloc
  -- from crates/trust_ir/src/inst.rs. Semantics: TrustIr.Semantics.Memory.semDealloc
  -- marks the allocation dead, clears its permission, and zeros its refcount.
  | Dealloc      (ptr : ValueId) : Inst

  -- Bulk memory (WS3.20, F-057). Mirror Rust Inst::MemCopy / Inst::MemSet
  -- (crates/trust-ir/src/inst.rs). Semantics: TrustIr.Semantics.Memory
  -- `semMemCopy` / `semMemSet` — byte-granular, DYNAMIC count.
  /-- `memcpy` (`overlap = false`) / `memmove` (`overlap = true`): copy
      `bytes` bytes from `src` to `dst`, carrying each byte's VALUE and INIT
      STATE (an uninitialized source byte stays uninitialized at the
      destination — copy-propagates-poison, `readBytesMaybeUninit` /
      `writeBytesMaybeUninit`). Out of bounds is UB; an overlapping copy
      without `overlap` is UB; a zero count is a no-op. -/
  | MemCopy      (dst : ValueId) (src : ValueId) (bytes : ValueId) (overlap : Bool) : Inst
  /-- `memset`: write the `U8` `byte` to each of `bytes` bytes at `dst`;
      every written byte becomes initialized. Out of bounds is UB; a zero
      count is a no-op. -/
  | MemSet       (dst : ValueId) (byte : ValueId) (bytes : ValueId) : Inst
  -- Run `ty`'s DESTRUCTOR on the object at `ptr`. Mirrors Rust Inst::Drop
  -- (crates/trust-ir/src/inst.rs), added by the THIR lowering's wave-DS so a
  -- body's drops are part of the IR rather than silently absent.
  --
  -- A place is named by a POINTER, exactly as Store names one: no new notion of
  -- where a droppable value lives is introduced, and a temporary is materialised
  -- by Alloca and dropped through the pointer that yields.
  --
  -- A PLAIN INSTRUCTION, not a terminator, though MIR's Drop is one; the Rust
  -- shim splits the block when it lowers this.
  --
  -- Semantics: TrustIr.Semantics.Step -- a STRUCTURED UNSUPPORTED, matching the
  -- reference interpreter (interpret.rs), which refuses it with "no destructor
  -- model". Dropping is observable (it frees, it runs user code), so modelling it
  -- as a no-op would silently evaluate a DIFFERENT program; refusing is the only
  -- honest total option until a destructor model exists. `Drop` is therefore
  -- OUTSIDE the lowering-target conformance subset, beside Resume.
  | Drop         (ty : Ty) (ptr : ValueId) : Inst

  -- Binding frames (typed quantifier lowering)
  -- Mirrors Rust Inst enum (crates/trust_ir/src/inst.rs). See
  -- designs/2026-04-19-binding-frames-lean-semantics.md section 2.2.
  /-- Open a new binding frame with the given slot layout.
      Produces a fresh frame handle; each slot initialised to Value.undef
      at its declared Ty. -/
  | OpenFrame    (def_ : BindingFrameDef) : Inst
  /-- Functionally update a binding frame: bind value into slot slot.
      Returns a fresh frame handle whose chosen slot is the new value.
      The input frame handle remains valid (SSA). -/
  | BindSlot     (frame : ValueId) (slot : Nat) (value : ValueId) : Inst
  /-- Read slot of binding frame frame; the ty parameter is the
      expected slot type (matched by validation; ignored at the
      denotation layer). -/
  | LoadSlot     (frame : ValueId) (slot : Nat) (ty : Ty) : Inst
  /-- Close a binding frame. Discipline marker: has no runtime effect on
      the machine state but is side-effecting for DCE purposes (dominator
      LIFO nesting is a Rust-side validation property). -/
  | CloseFrame   (frame : ValueId) : Inst

  -- Coroutine suspend (state-machine lowering). Mirrors Rust
  -- Inst::CoroSuspend (crates/trust-ir/src/inst.rs). A TERMINATOR that models
  -- one `yield`: store `nextState` (i64) into `frame[stateSlot]`, then return
  -- `value` to the resumer. Semantics: TrustIr.Semantics.Coroutine
  -- (semCoroSuspend), defined as exactly that GEP+Store+Return composition.
  | CoroSuspend  (frame : ValueId) (stateSlot : Nat) (nextState : Int)
                 (value : ValueId) : Inst

  -- Exception handling (zero-cost table-driven unwinding). Mirrors Rust
  -- Inst::Invoke / Inst::LandingPad / Inst::Resume (crates/trust-ir/src/inst.rs).
  -- The executable model, like the reference interpreter, runs under a named
  -- `PanicStrategy` (amendment D, Part 2; `Semantics/Eval.lean`). Under
  -- `.abort` (the default, the panic=abort projection) an Invoke runs the
  -- call and always takes the normal edge, and a landing pad or a re-raise is
  -- refused. Under `.unwind` a failed check raises, the invoke-family
  -- terminators catch the unwinding into their landing pad, and `Resume`
  -- re-raises it. The bare `stepInst` is the `.abort` step.
  /-- A call with two control-flow successors (TERMINATOR): on normal return
      the callee's results bind this node's results and control transfers to
      `normalDest` with `normalArgs`; if the callee unwound, control would
      transfer to `unwindDest` (a block beginning with `LandingPad`). -/
  | Invoke       (callee : FuncId) (args : List ValueId) (normalDest : BlockId)
                 (normalArgs : List ValueId) (unwindDest : BlockId) : Inst
  /-- Entry of an exception handler / cleanup block (NOT a terminator).
      In Rust it produces TWO results, the exception-object pointer and the
      type selector `(Ptr, I32)`. Under `PanicStrategy.unwind` an unwinding
      entering the pad binds them (selector 1 for a catch-all clause 0, 0 for
      a cleanup pad; a typed clause is `unsupported.typed_catch`). Reached
      with no exception in hand — always, under `.abort` — it FAILS CLOSED
      (`unsupported.host_unwind`) exactly like interpret.rs: it binds no
      fabricated `(null, 0)` (WS2.5 / WS2.24). -/
  | LandingPad   (isCleanup : Bool) (catchTypeIndices : List Nat) : Inst
  /-- Continue unwinding (re-raise) after a cleanup pad (TERMINATOR with no
      successors in this function). Under `PanicStrategy.unwind` it re-raises
      the exception object its operand addresses (any other value is UB);
      under `.abort` it is refused (`unsupported.host_unwind`). -/
  | Resume       (exn : ValueId) : Inst
  /-- A sited check whose failure must enter an in-frame landing pad (MIR
      `UnwindAction::Cleanup` / `Terminate`; amendment P, wire v54). A
      TERMINATOR with `Invoke`'s successors: a passing check continues to
      `normalDest` with `normalArgs`; a failing one is the sited panic. Under
      `PanicStrategy.abort` (the panic=abort projection) the unwind edge is
      never taken; under `.unwind` the failure raises and enters the pad at
      `unwindDest` (amendment D, Part 2). Mirrors Rust `Inst::AssertInvoke`. -/
  | AssertInvoke (cond : ValueId) (kind : AssertKind) (site : PanicSite)
                 (normalDest : BlockId) (normalArgs : List ValueId)
                 (unwindDest : BlockId) : Inst
  /-- Run `ty`'s drop glue on the object at `ptr`, with an unwind edge
      (amendment D, wire v55). The unwinding twin of `Drop`, exactly as
      `Invoke` is `Call`'s: a TERMINATOR with `Invoke`'s successors and no
      results. Resolved through the module drop-glue table it IS
      `Invoke glue [ptr] normalDest normalArgs unwindDest`; unresolved, it is
      refused exactly as an unresolved `Drop` is. The unwind edge is taken
      only under `PanicStrategy.unwind`, when the glue unwinds. Mirrors Rust
      `Inst::DropInvoke`. -/
  | DropInvoke   (ty : Ty) (ptr : ValueId) (normalDest : BlockId)
                 (normalArgs : List ValueId) (unwindDest : BlockId) : Inst
  /-- `CallIndirect` with an unwind edge (amendment D, Part 2; wire v56, Inst
      tag 69): `CallIndirect`'s unwinding twin, exactly as `Invoke` is
      `Call`'s. A TERMINATOR with `Invoke`'s successors: the callee is
      resolved and checked as `CallIndirect`'s; on a normal return its
      results bind this node's results (`terminatorResultDests`) and control
      transfers to `normalDest` with `normalArgs`. The unwind edge is taken
      only under `PanicStrategy.unwind`, when the callee unwinds. Mirrors Rust
      `Inst::InvokeIndirect`. -/
  | InvokeIndirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId)
                 (callingConv : CallingConv) (normalDest : BlockId)
                 (normalArgs : List ValueId) (unwindDest : BlockId) : Inst

  -- Dialect op: a namespaced operation from a TrustIr dialect. Mirrors Rust
  -- Inst::DialectOp(Box<DialectInst>) from crates/trust_ir/src/inst.rs.
  -- Core TrustIr semantics do not interpret dialect ops; dialect-aware
  -- passes must lower them to core instructions before evaluation
  -- (TrustIr.Semantics.Dialect formalises the lowering-correctness
  -- obligation). stepInst treats DialectOp as an unsupported executable
  -- subset case at run time.
  | DialectOp    (op : DialectInst) : Inst
  deriving Repr

/-- Returns true if the instruction is a terminator (ends a basic block). -/
def Inst.isTerminator : Inst → Bool
  | .Br ..          => true
  | .CondBr ..      => true
  | .Switch ..      => true
  | .Return ..      => true
  | .Unreachable    => true
  -- CoroSuspend stores the resume state then returns to the resumer.
  -- Mirrors Rust is_terminator (inst.rs).
  | .CoroSuspend .. => true
  -- Invoke is a call with two successors; Resume re-raises to the host
  -- unwinder. Both mirror Rust is_terminator. LandingPad is NOT a
  -- terminator (it is the first instruction of the pad block).
  | .Invoke ..      => true
  | .Resume ..      => true
  -- A sited check with an unwind edge (amendment P). Mirrors Rust.
  | .AssertInvoke .. => true
  -- A drop with an unwind edge (amendment D). Mirrors Rust.
  | .DropInvoke ..   => true
  -- An indirect call with an unwind edge (amendment D, Part 2). Mirrors Rust.
  | .InvokeIndirect .. => true
  | _               => false

/-- Returns true if the instruction MUTATES the abstract machine state
    (`MachineState`): writes memory, allocates, caches a global address,
    modifies permissions/refcounts, or transfers control.

    NOTE — this is the *state-mutation* predicate of the Lean operational
    semantics, NOT the same notion as Rust `Inst::has_observable_effects` (the
    DCE-removability predicate in crates/trust-ir/src/inst.rs). They agree on
    the externally-observable ops (Store / all five Atomics — including
    `AtomicLoad`, whose synchronizes-with edge makes it non-removable — / Call /
    Assert / Dealloc / Borrow / ARC / DialectOp / volatile Load / terminators),
    but DELIBERATELY differ on
    `Alloca` / `HeapAlloc` / `GlobalAddr`: those genuinely mutate `MachineState`
    here (the step rules allocate / cache an address), so they are `true` for
    state-mutation, whereas the Rust DCE predicate treats an *unused*
    allocation/address as removable (`false`). Both are correct for their
    purpose; treating these as state-mutating keeps the DCE-correctness theorem
    (TransformCorrectness) sound without a memory-equivalence argument for
    allocation removal. -/
def Inst.hasSideEffects : Inst → Bool
  | .Store ..       => true
  -- An ATOMIC load is observable: it carries a synchronizes-with edge in the
  -- memory model regardless of ordering, so DCE must NOT remove it even when
  -- its result is unused. Mirrors Rust `has_observable_effects`
  -- (crates/trust-ir/src/inst.rs: `AtomicLoad { .. } => true`).
  | .AtomicLoad ..  => true
  | .AtomicStore .. => true
  | .AtomicRMW ..   => true
  -- Both strengths: a weak compare-exchange may STORE (when it succeeds), so
  -- it mutates state exactly as a strong one does. The `..` pattern covers the
  -- `weak` field; do not narrow it to one strength.
  | .CmpXchg ..     => true
  | .Fence ..       => true
  | .Call ..        => true
  | .CallIndirect .. => true
  | .CallCannotUnwind .. => true
  | .CallIndirectCannotUnwind .. => true
  -- SeqMap invokes an arbitrary element function per element (a call in
  -- disguise): conservatively state-mutating/observable, exactly like Call.
  -- Mirrors Rust `has_observable_effects` (`Inst::SeqMap { .. } => true`).
  | .SeqMap ..      => true
  | .Assert ..      => true
  -- Alloca allocates memory and sets permissions
  | .Alloca ..      => true
  -- HeapAlloc allocates memory and sets permissions (heap counterpart of Alloca)
  | .HeapAlloc ..   => true
  -- GlobalAddr reserves+caches a fresh address on first use (mutates memory/globals)
  | .GlobalAddr ..  => true
  -- Borrow instructions modify the permission map
  | .Borrow ..      => true
  | .BorrowMut ..   => true
  | .EndBorrow ..   => true
  -- ARC instructions modify reference counts
  | .Retain ..      => true
  | .Release ..     => true
  -- Dealloc frees an allocation — always side-effecting. Mirrors
  -- Rust has_side_effects.
  | .Dealloc ..     => true
  -- The bulk ops WRITE `bytes` bytes of the destination — as observable as a
  -- Store, and they bind no result a use count could keep alive. Mirrors
  -- Rust has_observable_effects (WS3.20).
  | .MemCopy ..     => true
  | .MemSet ..      => true
  -- A DROP runs a destructor: it frees, and it can run arbitrary user code. It
  -- is the definition of an observable effect and must never be removable.
  -- Mirrors Rust has_observable_effects (`Inst::Drop { .. } => true`).
  --
  -- THIS ARM IS LOAD-BEARING, not documentation: the fallthrough below is
  -- `i.isTerminator`, and Drop is deliberately NOT a terminator, so omitting
  -- this line would read Drop as PURE and let `dce_pure_inst` license deleting
  -- a destructor. The Lean build found it -- `TransformCorrectness` refused to
  -- compile with the alternative missing -- which is that exhaustive match
  -- doing exactly the job it exists for.
  | .Drop ..        => true
  -- CloseFrame is a DCE discipline marker (matches Rust has_observable_effects).
  -- OpenFrame, BindSlot, LoadSlot are pure SSA (default false).
  | .CloseFrame ..  => true
  -- DialectOp is opaque by design — conservatively side-effecting until
  -- a dialect-aware pass lowers it to core instructions. Mirrors Rust
  -- has_side_effects.
  | .DialectOp ..   => true
  -- A landing pad is the structural entry of an exception handler / cleanup
  -- block: the unwinder transfers control to it, so DCE must never remove it
  -- even when its produced values are unused (eliding it would drop the
  -- handler the LSDA points at). Mirrors Rust has_observable_effects.
  | .LandingPad ..  => true
  -- A VOLATILE load is an observable access (MMIO / signal visibility): it must
  -- not be removed even though it produces a value. Mirrors Rust
  -- has_observable_effects. A non-volatile load is pure (default false).
  | .Load _ _ volatile _ => volatile
  | i               => i.isTerminator

end TrustIr
