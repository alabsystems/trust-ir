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
- Memory: Load, Store, Alloca, GEP, Dealloc
- Atomics: AtomicLoad, AtomicStore, AtomicRMW, CmpXchg, Fence
- Control flow: Br, CondBr, Switch, Call, CallIndirect, Return
- Aggregates: ExtractField, InsertField, ExtractElement, InsertElement
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
  | Alloca       (ty : Ty) (count : Option ValueId) : Inst
  | HeapAlloc    (ty : Ty) (count : Option ValueId) (origin : AllocOrigin) : Inst
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
  | CmpXchg      (ty : Ty) (ptr : ValueId) (expected desired : ValueId)
                 (success failure : MemOrdering) : Inst
  | Fence        (ordering : MemOrdering) : Inst

  -- Control flow
  | Br           (target : BlockId) (args : List ValueId) : Inst
  | CondBr       (cond : ValueId) (thenTarget : BlockId) (thenArgs : List ValueId)
                 (elseTarget : BlockId) (elseArgs : List ValueId) : Inst
  | Switch       (value : ValueId) (default_ : BlockId) (defaultArgs : List ValueId)
                 (cases : List SwitchCase) : Inst
  | Call         (callee : FuncId) (args : List ValueId) : Inst
  | CallIndirect (callee : ValueId) (sig : FuncTyId) (args : List ValueId) : Inst
  | Return       (values : List ValueId) : Inst

  -- Aggregates
  | ExtractField   (ty : Ty) (aggregate : ValueId) (field : Nat) : Inst
  | InsertField    (ty : Ty) (aggregate : ValueId) (field : Nat) (value : ValueId) : Inst
  | ExtractElement (ty : Ty) (array : ValueId) (index : ValueId) : Inst
  | InsertElement  (ty : Ty) (array : ValueId) (index : ValueId) (value : ValueId) : Inst

  -- Constants
  | Const        (ty : Ty) (value : Constant) : Inst
  | NullPtr      : Inst
  | Undef        (ty : Ty) : Inst

  -- Proof instructions
  | Assume       (cond : ValueId) : Inst
  | Assert       (cond : ValueId) : Inst
  | Unreachable  : Inst

  -- Pseudo instructions
  | Copy         (ty : Ty) (operand : ValueId) : Inst
  /-- Branchless selection.

      Lean execution accepts scalar `Bool` as whole-value selection and a
      bounded same-lane `<N x Bool>` mask path for lane-wise vector selection.
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
  -- The executable model, like the reference interpreter, models a
  -- NON-THROWING callee (panic=abort): an Invoke runs the call and always
  -- takes the normal edge; the unwind edge / landing-pad entry / re-raise are
  -- carried with structural fidelity but never taken under evaluation.
  /-- A call with two control-flow successors (TERMINATOR): on normal return
      the callee's results bind this node's results and control transfers to
      `normalDest` with `normalArgs`; if the callee unwound, control would
      transfer to `unwindDest` (a block beginning with `LandingPad`). -/
  | Invoke       (callee : FuncId) (args : List ValueId) (normalDest : BlockId)
                 (normalArgs : List ValueId) (unwindDest : BlockId) : Inst
  /-- Entry of an exception handler / cleanup block (NOT a terminator).
      Produces the exception-object pointer and type selector, packed as an
      aggregate pair `(Ptr, I32)` per the Overflow multi-result convention. -/
  | LandingPad   (isCleanup : Bool) (catchTypeIndices : List Nat) : Inst
  /-- Continue unwinding (re-raise) after a cleanup pad (TERMINATOR with no
      successors in this function). -/
  | Resume       (exn : ValueId) : Inst

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
  | .CmpXchg ..     => true
  | .Fence ..       => true
  | .Call ..        => true
  | .CallIndirect .. => true
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
