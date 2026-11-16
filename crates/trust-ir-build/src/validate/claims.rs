// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS2.7 (F-021 / F-040): the cheap, sound part of two claim surfaces, checked.
//!
//! * **`FuncAttrs.readnone` / `readonly` on a DEFINED body** (F-021). Until
//!   this pass both were claim-style: a body that executed a `Store` could be
//!   stamped `readnone` and validated, so a consumer that trusted the claim
//!   (an LLVM `memory(none)` lowering, a CSE across the call) would be unsound.
//!   A bodyless declaration keeps its attributes as a claim — there is no body
//!   to check them against.
//! * **Borrow structure** (F-040). The only borrow rule used to be "the operand
//!   is a pointer". Two STRUCTURAL rules are now decided here: a `BorrowMut`
//!   may not be taken through a shared reference, and an `EndBorrow` must end
//!   a borrow. The flow-sensitive liveness half (exactly one `EndBorrow` per
//!   path, no two live `BorrowMut`, no use after `EndBorrow`) is NOT decided;
//!   it is ratified as a producer obligation in `TRUST.md` (item 12) and
//!   `LIMITATIONS.md`.
//!
//! Both rules start from one flow-insensitive ROOT TRACE: from an address
//! value, follow ONLY a `GEP`'s base, a `Copy`'s operand and a `Cast
//! PtrToPtr`'s operand. Every other definition on the path ends the trace and
//! is the root — in particular a `Select`, a block parameter, an `IntToPtr`, a
//! `Load` result, a call result and a `PtrFromParts` are roots, never
//! transparent. For the alloca EXEMPTION (an ALL-roots question) following
//! any of them would let `select %c, %alloca, %param` or a loop-carried block
//! parameter launder a parameter pointer into the exemption. A value with
//! several definitions (itself an SSA error) contributes every one of them, so
//! a duplicate can never vouch for its twin.
//!
//! The shared-borrow question is the opposite polarity (ANY root refuses), so
//! there the trace additionally follows BOTH arms of a `Select` and EVERY
//! incoming argument of a block parameter: stopping at them would be the
//! permissive direction, and `%s = select %c, %r, %r; borrow_mut %s` (or a
//! shared borrow carried into a block parameter) would upgrade a shared
//! borrow unrefused. Following more can only refuse more, never exempt more.

use super::ValidationError;
use std::collections::{BTreeMap, BTreeSet};
use trust_ir::inst::{CastOp, Inst, Ordering};
use trust_ir::ty::Ty;
use trust_ir::value::ValueId;
use trust_ir::{Function, Module};

/// One definition of an SSA value, as the flow-insensitive lookup sees it.
#[derive(Clone, Copy)]
pub(super) enum Def<'f> {
    /// Parameter `index` of block `block`: a root for the alloca exemption
    /// (a merge of arbitrary incoming values).
    Param { block: u32, index: usize },
    /// A result of this instruction.
    Node(&'f Inst),
}

/// Every definition of every value in `func`, in block order.
pub(super) struct DefTable<'f> {
    defs: BTreeMap<ValueId, Vec<Def<'f>>>,
}

impl<'f> DefTable<'f> {
    pub(super) fn new(func: &'f Function) -> Self {
        let mut defs: BTreeMap<ValueId, Vec<Def<'f>>> = BTreeMap::new();
        for block in &func.blocks {
            for (index, (value, _)) in block.params.iter().enumerate() {
                defs.entry(*value).or_default().push(Def::Param {
                    block: block.id.index(),
                    index,
                });
            }
            for node in &block.body {
                for result in &node.results {
                    defs.entry(*result).or_default().push(Def::Node(&node.inst));
                }
            }
        }
        Self { defs }
    }

    pub(super) fn defs(&self, value: ValueId) -> &[Def<'f>] {
        self.defs.get(&value).map_or(&[], Vec::as_slice)
    }

    /// The roots of `value` under the WS2.7 trace (`GEP` base, `Copy`
    /// operand, `Cast PtrToPtr` operand, nothing else). `None` in the result
    /// stands for a value with no definition at all, or a definition cycle
    /// (both malformed; reported elsewhere) — never a known root.
    fn roots(&self, value: ValueId) -> Vec<Option<Def<'f>>> {
        let mut roots = Vec::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![value];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                // A cycle through transparent definitions has no root; treat
                // it as unknown, which is never exempt.
                roots.push(None);
                continue;
            }
            let defs = self.defs(current);
            if defs.is_empty() {
                roots.push(None);
            }
            for def in defs {
                match def {
                    Def::Node(Inst::GEP { base, .. }) => stack.push(*base),
                    Def::Node(Inst::Copy { operand, .. })
                    | Def::Node(Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }) => stack.push(*operand),
                    other => roots.push(Some(*other)),
                }
            }
        }
        roots
    }

    /// Does `address` root EXCLUSIVELY at `Alloca`s of this function?
    fn roots_at_local_alloca(&self, address: ValueId) -> bool {
        let roots = self.roots(address);
        !roots.is_empty()
            && roots
                .iter()
                .all(|root| matches!(root, Some(Def::Node(Inst::Alloca { .. }))))
    }

    /// Can `address` be the result of a SHARED `Borrow` on any path? The
    /// root trace (`GEP` base, `Copy`, `Cast PtrToPtr`) widened, because this
    /// is the ANY-polarity question, by both arms of a `Select` and every
    /// incoming argument of a block parameter (`incoming`, keyed by
    /// `(block, param index)`). A cycle simply stops: it adds no new root.
    fn may_root_at_shared_borrow(
        &self,
        address: ValueId,
        incoming: &BTreeMap<(u32, usize), Vec<ValueId>>,
    ) -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![address];
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            for def in self.defs(current) {
                match def {
                    Def::Node(Inst::Borrow { .. }) => return true,
                    Def::Node(Inst::GEP { base, .. }) => stack.push(*base),
                    Def::Node(Inst::Copy { operand, .. })
                    | Def::Node(Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }) => stack.push(*operand),
                    Def::Node(Inst::Select {
                        then_val, else_val, ..
                    }) => {
                        stack.push(*then_val);
                        stack.push(*else_val);
                    }
                    Def::Param { block, index } => {
                        if let Some(args) = incoming.get(&(*block, *index)) {
                            stack.extend(args.iter().copied());
                        }
                    }
                    Def::Node(_) => {}
                }
            }
        }
        false
    }

    /// Is `value` DIRECTLY the result of a `Borrow` / `BorrowMut` (every
    /// definition of it, and at least one)?
    fn is_borrow_result(&self, value: ValueId) -> bool {
        let defs = self.defs(value);
        !defs.is_empty()
            && defs
                .iter()
                .all(|def| matches!(def, Def::Node(Inst::Borrow { .. } | Inst::BorrowMut { .. })))
    }
}

/// Which effect claim a body is checked against.
#[derive(Clone, Copy, PartialEq, Eq)]
enum EffectClaim {
    /// LLVM `memory(none)`: reads and writes no memory the caller can see.
    ReadNone,
    /// LLVM `memory(read)`: writes no memory the caller can see.
    ReadOnly,
}

impl EffectClaim {
    fn attr(self) -> &'static str {
        match self {
            Self::ReadNone => "readnone",
            Self::ReadOnly => "readonly",
        }
    }

    /// Does a callee's attribute set discharge this claim at a call edge?
    fn admits_callee(self, callee: &Function) -> bool {
        match self {
            Self::ReadNone => callee.attrs.readnone,
            Self::ReadOnly => callee.attrs.readonly || callee.attrs.readnone,
        }
    }
}

/// What one instruction does to memory, for the effect-claim rule.
enum Effect {
    /// No memory effect the caller can observe.
    None,
    /// A non-synchronizing READ through `address` (`Load`, `AtomicLoad`
    /// `Relaxed`): admitted by `readonly`; by `readnone` only when `address`
    /// roots at a local `Alloca`.
    Read { address: ValueId },
    /// A WRITE (or read-modify-write) through `address`, non-synchronizing:
    /// admitted by either claim only when `address` roots at a local `Alloca`.
    Write { address: ValueId },
    /// An effect no claim admits and no exemption covers: a synchronizing
    /// atomic, a fence, heap allocation / deallocation, reference counting,
    /// an indirect call, an opaque dialect op. `reason` names it.
    Refused { reason: &'static str },
    /// A direct call edge (`Call` / `Invoke`, and `SeqMap`'s element
    /// function): the callee's own attributes must discharge the claim.
    CallEdge { callee: trust_ir::value::FuncId },
}

fn is_relaxed(ordering: Ordering) -> bool {
    matches!(ordering, Ordering::Relaxed)
}

/// Classify `inst`. Exhaustive on purpose: a new instruction must be
/// classified here rather than slip through a wildcard as effect-free.
///
/// `drop_glue` is the module's drop-glue table (amendment D, §20): a RESOLVED
/// drop IS a call of its glue, so it is that call edge; an unresolved one (or
/// any drop without module context) states no destructor and is refused.
fn effect_of(inst: &Inst, drop_glue: Option<&trust_ir::DropGlueIndex>) -> Effect {
    match inst {
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Alloca { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::MakeAggregate { .. }
        | Inst::MakeClosure { .. }
        // v50: a fresh array value from one register value — no memory.
        | Inst::ArraySplat { .. }
        // The tensor region: a fresh tensor VALUE from two register values
        // — no memory, no call (a paired-extent mismatch is undefined
        // behaviour, not a trap).
        | Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        // A failed check is a TERMINAL panic outcome, whether or not it is
        // sited (amendment P): a site's entry never returns, so like an
        // unsited assert's trap it adds no memory effect the function's
        // continuation can observe. `AssertInvoke` is the same check with an
        // unwind edge the panic=abort projection never takes.
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        // Borrows are address identities (the interpreter passes the address
        // through); binding frames are typed slots of the executing frame;
        // a landing pad reads the unwinder's registers and `Resume` hands the
        // exception object back to the unwinder.
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => Effect::None,
        // Box validity is point-in-time and §28 forbids moving or deleting
        // its check. Until an explicit consumer contract exists, neither a
        // readnone nor a readonly claim may summarize it away.
        Inst::BoxDeref { .. } => Effect::Refused {
            reason: "point-in-time Box validity is not covered by an effect claim",
        },
        Inst::Load { ptr, .. } => Effect::Read { address: *ptr },
        Inst::AtomicLoad { ptr, ordering, .. } => {
            if is_relaxed(*ordering) {
                Effect::Read { address: *ptr }
            } else {
                Effect::Refused {
                    reason: "an atomic load stronger than relaxed synchronizes",
                }
            }
        }
        Inst::Store { ptr, .. } => Effect::Write { address: *ptr },
        Inst::AtomicStore { ptr, ordering, .. } | Inst::AtomicRMW { ptr, ordering, .. } => {
            if is_relaxed(*ordering) {
                Effect::Write { address: *ptr }
            } else {
                Effect::Refused {
                    reason: "an atomic write stronger than relaxed synchronizes",
                }
            }
        }
        Inst::CmpXchg {
            ptr,
            success,
            failure,
            ..
        } => {
            if is_relaxed(*success) && is_relaxed(*failure) {
                Effect::Write { address: *ptr }
            } else {
                Effect::Refused {
                    reason: "a cmpxchg stronger than relaxed synchronizes",
                }
            }
        }
        // `CoroSuspend` is DEFINED as GEP + Store + Return into the frame.
        Inst::CoroSuspend { frame, .. } => Effect::Write { address: *frame },
        Inst::Fence { .. } => Effect::Refused {
            reason: "a fence synchronizes",
        },
        Inst::HeapAlloc { .. } => Effect::Refused {
            reason: "heap allocation",
        },
        Inst::Dealloc { .. } => Effect::Refused {
            reason: "deallocation",
        },
        // Crystal lane (wave-DS): a destructor frees and can run arbitrary user code; no
        // effect claim admits it.
        Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => {
            match drop_glue.map(|index| index.resolve(ty)) {
                Some(trust_ir::DropResolution::Resolved(glue)) => Effect::CallEdge { callee: glue },
                _ => Effect::Refused {
                    reason: "an unresolved drop runs an unstated destructor (no drop_glue row)",
                },
            }
        }
        // WS3.20 bulk memory: a dynamic-count write (and read) over a byte
        // RANGE, not one addressed cell; the effect model here is per-cell.
        Inst::MemCopy { .. } | Inst::MemSet { .. } => Effect::Refused {
            reason: "a bulk byte-range write with a dynamic count is not a single-cell effect",
        },
        Inst::Retain { .. } | Inst::Release { .. } | Inst::IsUnique { .. } => Effect::Refused {
            reason: "reference counting reads and writes the object header",
        },
        Inst::CallIndirect { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::InvokeIndirect { .. } => Effect::Refused {
            reason: "an indirect callee's attributes are unknowable",
        },
        Inst::DialectOp(_) => Effect::Refused {
            reason: "an opaque dialect op's memory effects are unknown",
        },
        Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => {
            Effect::CallEdge { callee: *callee }
        }
        // The element function writes through its `&mut elem` parameter;
        // this rule does not attribute that write to a local, so the edge is
        // checked like any call.
        Inst::SeqMap { fwd, .. } => Effect::CallEdge { callee: *fwd },
    }
}

/// `FuncAttrs.readnone` / `readonly` on a DEFINED body (WS2.7 (a); F-021).
///
/// The body must be consistent with the claim (LLVM `memory(none)` /
/// `memory(read)` respectively):
///
/// * `readnone` admits no `BoxDeref` / `Load` / `AtomicLoad` / `Store` / `AtomicStore` /
///   `AtomicRMW` / `CmpXchg` / `Fence` / `HeapAlloc` / `Dealloc` / `Retain` /
///   `Release` / `IsUnique` (nor `CoroSuspend`, which is defined as a store
///   into the frame), and a `Call` / `Invoke` only to a callee that is itself
///   `readnone`.
/// * `readonly` additionally admits `Load` and a `Relaxed` `AtomicLoad`, but
///   not `BoxDeref`: its point-in-time validity check cannot be summarized or
///   moved by an attribute. An
///   `AtomicLoad` with `Acquire` or stronger synchronizes, which LLVM also
///   does not admit under `memory(read)`. A callee must be `readonly` or
///   `readnone`.
/// * Exemption, matching LLVM's treatment of a function's own stack: a
///   non-synchronizing load or store whose address roots at an `Alloca` of the
///   SAME function under the root trace (`GEP` base, `Copy`, `Cast PtrToPtr`
///   only — see the module docs for what is deliberately NOT followed).
/// * Refused under either claim, with no exemption: `CallIndirect` (the
///   callee's attributes are unknowable), a synchronizing atomic or fence,
///   heap allocation / deallocation, reference counting, and an opaque
///   `DialectOp`. `SeqMap`'s element function is checked as a call edge.
///
/// `module == None` is the standalone [`super::validate_function`] entry
/// point: it cannot resolve a callee's attributes, so every call edge of a
/// claiming body FAILS CLOSED there; module validation resolves them. When
/// both attributes are set, `readnone` (the stronger claim) is the one
/// checked and named.
pub(super) fn validate_func_attr_claims(
    func: &Function,
    module: Option<&Module>,
) -> Vec<ValidationError> {
    let claim = if func.attrs.readnone {
        EffectClaim::ReadNone
    } else if func.attrs.readonly {
        EffectClaim::ReadOnly
    } else {
        return Vec::new();
    };
    // A declaration's attributes remain a claim: there is no body.
    if func.blocks.is_empty() {
        return Vec::new();
    }
    let defs = DefTable::new(func);
    let drop_glue = module.map(Module::drop_glue_index);
    let mut errors = Vec::new();
    for block in &func.blocks {
        for node in &block.body {
            let mnemonic = super::instruction_kind(&node.inst);
            let violation: Option<String> = match effect_of(&node.inst, drop_glue.as_ref()) {
                Effect::None => None,
                Effect::Read { address } => match claim {
                    EffectClaim::ReadOnly => None,
                    EffectClaim::ReadNone if defs.roots_at_local_alloca(address) => None,
                    EffectClaim::ReadNone => Some(format!(
                        "{mnemonic} (reads memory not rooted at a local alloca)"
                    )),
                },
                Effect::Write { address } => {
                    if defs.roots_at_local_alloca(address) {
                        None
                    } else {
                        Some(format!(
                            "{mnemonic} (writes memory not rooted at a local alloca)"
                        ))
                    }
                }
                Effect::Refused { reason } => Some(format!("{mnemonic} ({reason})")),
                Effect::CallEdge { callee } => match module {
                    None => Some(format!(
                        "{mnemonic} to function #{} (a callee's attributes cannot be \
                         resolved without module context)",
                        callee.index()
                    )),
                    Some(module) => match module.function_by_id(callee) {
                        None => Some(format!(
                            "{mnemonic} to function #{} (the callee does not resolve)",
                            callee.index()
                        )),
                        Some(target) if claim.admits_callee(target) => None,
                        Some(target) => Some(format!(
                            "{mnemonic} @{} (the callee does not carry {})",
                            target.name,
                            match claim {
                                EffectClaim::ReadNone => "readnone",
                                EffectClaim::ReadOnly => "readonly or readnone",
                            }
                        )),
                    },
                },
            };
            if let Some(inst) = violation {
                errors.push(ValidationError::FuncAttrClaimViolated {
                    function: func.name.clone(),
                    attr: claim.attr(),
                    block: block.id.index(),
                    inst,
                });
            }
        }
    }
    errors
}

/// Every value a CFG edge passes to parameter `index` of block `block`
/// (every normal edge; an unwind edge carries none). An edge with the wrong
/// arity is reported elsewhere; here an extra argument is simply ignored and
/// a missing one contributes nothing.
fn block_param_incoming(func: &Function) -> BTreeMap<(u32, usize), Vec<ValueId>> {
    let mut incoming: BTreeMap<(u32, usize), Vec<ValueId>> = BTreeMap::new();
    let mut edge = |target: u32, args: &[ValueId]| {
        for (index, arg) in args.iter().enumerate() {
            incoming.entry((target, index)).or_default().push(*arg);
        }
    };
    // Every normal edge, from the exhaustive accessor (amendment D §1.3):
    // this walk once listed `Br` / `CondBr` / `Switch` / `Invoke` behind a
    // `_ => {}` arm, so a value passed on an `AssertInvoke` normal edge had
    // no incoming root, and a borrow traced through it was missed.
    for block in &func.blocks {
        for node in &block.body {
            for e in super::edges_default_first(&node.inst) {
                if e.kind == trust_ir::EdgeKind::Normal {
                    edge(e.target.index(), e.args);
                }
            }
        }
    }
    incoming
}

/// Borrow STRUCTURE (WS2.7 (b); F-040). Two rules, both flow-insensitive:
///
/// * `BorrowMutThroughSharedRef`: a `BorrowMut`'s operand has static type
///   `Ref(_)` or `PtrConst(_)`, or may root at the result of a SHARED
///   `Borrow` — the effect rule's trace (`Copy` / `GEP` / `Cast PtrToPtr`)
///   widened, because this is the any-root question, by both arms of a
///   `Select` and every incoming argument of a block parameter. The type-only
///   half alone would miss the common shape `%r = borrow %x; borrow_mut %r`,
///   because a thin borrow's result is typed `Ptr`
///   (`trust_ir::bridge::borrow_result_ty`).
/// * `EndBorrowOfNonBorrow`: an `EndBorrow`'s operand is not DIRECTLY the
///   result of a `Borrow` / `BorrowMut` (every definition of it, and at least
///   one).
///
/// Liveness (exactly one `EndBorrow` per path, no two live `BorrowMut` of one
/// place, no use after `EndBorrow`) needs a flow-sensitive borrow checker and
/// is NOT decided here: it is a producer obligation (`TRUST.md` item 12) —
/// discharged upstream by rustc for the tRust producer, unchecked for Clean
/// and hand-built producers. An upgrade laundered through MEMORY (a store
/// and reload), a call, or an integer round trip is not traced and falls
/// under that same producer obligation.
/// A Rust reference carries no permission instruction
/// (`docs/SPEC_RATIFICATIONS.md`, the section of that name): in a function
/// stamped [`trust_ir::Producer::TRust`], every node whose instruction drives
/// the permission machine ([`Inst::uses_borrow_permissions`], the proved
/// `InstShape` table) is [`ValidationError::RustReferenceAsPermissionBorrow`].
///
/// Only the `TRust` stamp selects the rule. The MIR bridge stamps
/// `Producer::TrustIr`, so its output is for the bundle check's `RustMir`
/// key instead, which is applied once the bridge's respelling is on Trust's
/// main (the SPEC section, rule 5); every other producer, and an unstamped
/// function, keeps the permission machine as the format's model for a
/// discipline that is its own.
pub(super) fn validate_rust_reference_spelling(func: &Function) -> Vec<ValidationError> {
    if func.producer != Some(trust_ir::Producer::TRust) {
        return Vec::new();
    }
    let mut errors = Vec::new();
    for block in &func.blocks {
        for (inst_index, node) in block.body.iter().enumerate() {
            if node.inst.uses_borrow_permissions() {
                errors.push(ValidationError::RustReferenceAsPermissionBorrow {
                    function: func.name.clone(),
                    block: block.id.index(),
                    inst_index,
                });
            }
        }
    }
    errors
}

pub(super) fn validate_borrow_structure(
    func: &Function,
    val_ty: &BTreeMap<u32, Ty>,
) -> Vec<ValidationError> {
    let mut defs: Option<DefTable<'_>> = None;
    let mut incoming: Option<BTreeMap<(u32, usize), Vec<ValueId>>> = None;
    let mut errors = Vec::new();
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::BorrowMut { ptr } => {
                    let shared_type =
                        matches!(val_ty.get(&ptr.index()), Some(Ty::Ref(_) | Ty::PtrConst(_)));
                    let table = defs.get_or_insert_with(|| DefTable::new(func));
                    let incoming = incoming.get_or_insert_with(|| block_param_incoming(func));
                    if shared_type || table.may_root_at_shared_borrow(*ptr, incoming) {
                        errors.push(ValidationError::BorrowMutThroughSharedRef {
                            block: block.id.index(),
                        });
                    }
                }
                Inst::EndBorrow { borrow_ptr } => {
                    let table = defs.get_or_insert_with(|| DefTable::new(func));
                    if !table.is_borrow_result(*borrow_ptr) {
                        errors.push(ValidationError::EndBorrowOfNonBorrow {
                            block: block.id.index(),
                        });
                    }
                }
                _ => {}
            }
        }
    }
    errors
}
