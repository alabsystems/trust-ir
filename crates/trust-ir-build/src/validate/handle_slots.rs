// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.7 (F-047, memory half): SEALED handle slots.
//!
//! A v43 opaque runtime handle may be spilled to a function-local stack slot
//! and reloaded — `let slot = v; let r = &slot; *r` for a `Nat` local — and
//! to nothing else in memory. A Rust producer spells `&slot` as the slot
//! address itself (SPEC "A Rust reference carries no permission
//! instruction"), which the rule admits as it stands; the `Borrow` /
//! `BorrowMut` join below is for a producer whose discipline the permission
//! machine is. The
//! soundness invariant is unchanged: *every handle a pinned entry point
//! receives came from a pinned entry point*. A slot only ever holds a value
//! that an exact-typed `Store` wrote into it from an SSA value that already
//! was a handle, and it is only ever read back at that same type, so a load
//! is `load ∘ store = id` at one pointer word (Lean:
//! `load_store_roundtrip_handle`, `Proofs/MemoryProps.lean`). Nothing here
//! introduces a handle.
//!
//! The rule, exactly. An `Alloca { ty: T, count: None, .. }` result `s`,
//! where `T` is a handle or a struct / tuple whose handle-reaching lanes are
//! themselves handles, structs or tuples (the WS3.6 register carriers), is
//! **sealed** iff every use of `s` — and, transitively, of every
//! `Borrow` / `BorrowMut` result derived from it — is one of:
//!
//! * `Store { ty: T, ptr: s', value: v }` with `s'` a slot pointer in the
//!   POINTER position and `v` of exactly `T`;
//! * `Load { ty: T, ptr: s' }`;
//! * `Borrow` / `BorrowMut` (whose result joins the slot) and `EndBorrow`.
//!
//! Any other use — `GEP`, a `Cast` (the `PtrToInt` leak), `Copy` / `Select`
//! of the pointer, a branch / call / invoke / return argument, a `Store` of
//! the pointer AS A VALUE, an atomic, `Dealloc`, `Drop`, a differently typed
//! `Load` / `Store` — unseals the slot, and its `Alloca` is refused
//! `InvalidHandleUse` naming the use. Beyond the escape rule:
//!
//! * **Definite initialization.** Every `Load` of a sealed slot must be
//!   dominated, at instruction granularity, by an exact-typed `Store` into
//!   the same slot that the `Alloca` itself strictly dominates. An
//!   uninitialized word read at a handle type would be a forged handle, so a
//!   store on only one arm of a diamond does not initialize the join —
//!   conservative by design; a producer stores the incoming value right after
//!   the `Alloca`.
//! * **Instance soundness.** Every use of a slot pointer must be dominated by
//!   that pointer's own definition. The deep SSA pass checks this too, but it
//!   is FILTERED under `validate_changed` while this rule runs on every
//!   function, so it is re-checked here rather than assumed: with it, the
//!   pointer a `Load` or `Store` names is always the one the most recent
//!   execution of the `Alloca` produced, so a store in an earlier loop
//!   iteration never initializes a later iteration's fresh slot.
//! * **Plain, naturally aligned accesses only.** A `volatile` access, an
//!   access `align` other than the slot type's natural alignment, an
//!   under-aligned `Alloca`, a dynamic `count`, a slot type without a
//!   computable layout, and a pointer value defined more than once are each
//!   refused.
//!
//! `HeapAlloc` of a handle stays refused (the handle arm's whitelist), as do
//! handle-typed globals (ratified: a Lean top-level `Nat` constant is a
//! function returning a fresh handle) and a handle behind a `Ref` / `RefMut`
//! PARAMETER, which is WS3.7 phase 2 (DG-46, gated on WS5 F-094): a `Load` or
//! `Store` at a handle type through any pointer that is not a sealed slot is
//! refused. Double release through a reloaded copy remains the `TRUST.md`
//! item 9(c) non-guarantee — this rule decides origins, never liveness.
//!
//! The rule is SYNTACTIC over the slot pointer's def-use graph: a write into
//! the slot's bytes through a pointer NOT derived from it (an `IntToPtr` of a
//! guessed address, an out-of-bounds `GEP` from another allocation) is a wild
//! write it cannot see. `docs/SPEC_RATIFICATIONS.md` §7 states that boundary;
//! the run-time half (a handle as a provenance-tagged word, so a forged reload
//! faults) is WS2 F-035's.

#![allow(
    clippy::type_complexity,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use std::collections::BTreeMap;

use trust_ir::analysis::DominatorTree;
use trust_ir::inst::Inst;
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, ValueId};
use trust_ir::{Function, Module, NominalTypeReachability, StructId};

/// The one-line statement of the rule every slot refusal carries.
pub(super) const SEALED: &str = "a handle slot is sealed: it may only be loaded and stored at its \
                                 exact type and never escapes";

/// An instruction position: `(block, index in the block body)`.
type Point = (BlockId, usize);

/// One `Alloca` whose type reaches a handle.
struct Slot {
    /// The allocated type `T`: the only type the slot is loaded and stored at.
    ty: Ty,
    /// Where the `Alloca` sits.
    site: Point,
    /// `T`'s natural alignment in bytes, once the shape check has passed.
    natural_align: Option<u64>,
    /// The FIRST reason the slot is not sealed, or `None` when it is.
    unsealed: Option<String>,
    /// Every exact-typed `Store` into the slot, in body order.
    stores: Vec<Point>,
}

/// The sealed-slot state of ONE function.
///
/// Built only for a function of a handle-bearing module that allocates a
/// slot whose type reaches a handle; when it is absent every `Load` / `Store`
/// at a handle type is REFUSED, never admitted.
pub(super) struct SealedHandleSlots {
    dominators: DominatorTree,
    /// Keyed by the `Alloca`'s result value.
    slots: BTreeMap<u32, Slot>,
    /// Every pointer value that addresses a slot — the `Alloca` result and,
    /// transitively, each `Borrow` / `BorrowMut` of one — mapped to its
    /// owning `Alloca` result and its own definition point.
    members: BTreeMap<u32, (u32, Point)>,
}

impl SealedHandleSlots {
    /// Whether `func` allocates a stack slot whose type reaches a handle. The
    /// analysis (and its dominator tree) is built only when it does.
    pub(super) fn function_allocates_a_handle(
        func: &Function,
        nominal_types: &NominalTypeReachability<'_>,
    ) -> bool {
        func.blocks.iter().any(|block| {
            block.body.iter().any(|node| {
                matches!(&node.inst, Inst::Alloca { ty, .. } if nominal_types.contains_handle(ty))
            })
        })
    }

    pub(super) fn new(
        layouts: &trust_ir::LayoutTable<'_>,
        func: &Function,
        nominal_types: &NominalTypeReachability<'_>,
    ) -> Self {
        let dominators = DominatorTree::new(func);

        // How many times each value is defined. A slot pointer defined more
        // than once has no single definition to reason about; the deep SSA
        // pass may be filtered off for this function, so this is checked
        // here and fails closed.
        let mut definitions: BTreeMap<u32, usize> = BTreeMap::new();
        for block in &func.blocks {
            for (value, _) in &block.params {
                *definitions.entry(value.index()).or_default() += 1;
            }
            for node in &block.body {
                for value in &node.results {
                    *definitions.entry(value.index()).or_default() += 1;
                }
            }
        }

        let mut slots: BTreeMap<u32, Slot> = BTreeMap::new();
        let mut members: BTreeMap<u32, (u32, Point)> = BTreeMap::new();
        for block in &func.blocks {
            for (index, node) in block.body.iter().enumerate() {
                let Inst::Alloca { ty, count, align } = &node.inst else {
                    continue;
                };
                if !nominal_types.contains_handle(ty) {
                    continue;
                }
                // An `Alloca` with no single result defines no slot; the rule
                // then finds no slot for it and refuses it.
                let [result] = node.results.as_slice() else {
                    continue;
                };
                let site = (block.id, index);
                let (natural_align, unsealed) =
                    match slot_shape(layouts, nominal_types, ty, count.is_some(), *align) {
                        Ok(natural) => (Some(natural), None),
                        Err(reason) => (None, Some(reason)),
                    };
                slots.insert(
                    result.index(),
                    Slot {
                        ty: ty.clone(),
                        site,
                        natural_align,
                        unsealed,
                        stores: Vec::new(),
                    },
                );
                members.insert(result.index(), (result.index(), site));
            }
        }

        // Every Borrow / BorrowMut of a slot pointer is a slot pointer, to a
        // fixed point (block storage order need not be dominance order).
        loop {
            let mut grew = false;
            for block in &func.blocks {
                for (index, node) in block.body.iter().enumerate() {
                    let (Inst::Borrow { ptr } | Inst::BorrowMut { ptr }) = &node.inst else {
                        continue;
                    };
                    let Some(&(owner, _)) = members.get(&ptr.index()) else {
                        continue;
                    };
                    for result in &node.results {
                        if let std::collections::btree_map::Entry::Vacant(entry) =
                            members.entry(result.index())
                        {
                            entry.insert((owner, (block.id, index)));
                            grew = true;
                        }
                    }
                }
            }
            if !grew {
                break;
            }
        }

        let multiply_defined: Vec<(u32, u32)> = members
            .iter()
            .filter(|(value, _)| definitions.get(value).copied().unwrap_or(0) != 1)
            .map(|(&value, &(owner, _))| (value, owner))
            .collect();
        let mut analysis = Self {
            dominators,
            slots,
            members,
        };
        for (value, owner) in multiply_defined {
            analysis.unseal(
                owner,
                format!("its slot pointer %{value} is defined more than once"),
            );
        }
        analysis.scan_uses(func);
        analysis
    }

    /// Record `reason` as the slot's first unsealing use.
    fn unseal(&mut self, owner: u32, reason: String) {
        if let Some(slot) = self.slots.get_mut(&owner)
            && slot.unsealed.is_none()
        {
            slot.unsealed = Some(reason);
        }
    }

    /// Classify every use of every slot pointer in `func`.
    fn scan_uses(&mut self, func: &Function) {
        for block in &func.blocks {
            for (index, node) in block.body.iter().enumerate() {
                let at = (block.id, index);
                let mut unsealing: Vec<(u32, String)> = Vec::new();

                // Instance soundness: each slot-pointer operand is dominated
                // by its own definition.
                node.inst.visit_value_operands(|operand| {
                    if let Some(&(owner, definition)) = self.members.get(&operand.index())
                        && !precedes(&self.dominators, definition, at)
                    {
                        unsealing.push((
                            owner,
                            format!(
                                "its slot pointer %{} is used in bb{} where its definition does \
                                 not dominate the use",
                                operand.index(),
                                block.id.index()
                            ),
                        ));
                    }
                });

                match &node.inst {
                    Inst::Store { ty, ptr, value, .. } => {
                        if let Some(&(owner, _)) = self.members.get(&value.index()) {
                            unsealing.push((
                                owner,
                                format!(
                                    "its slot pointer %{} is stored AS A VALUE by `Store` in bb{}",
                                    value.index(),
                                    block.id.index()
                                ),
                            ));
                        }
                        if let Some(&(owner, _)) = self.members.get(&ptr.index())
                            && let Some(slot) = self.slots.get_mut(&owner)
                        {
                            if *ty == slot.ty {
                                slot.stores.push(at);
                            } else {
                                unsealing.push((
                                    owner,
                                    format!(
                                        "`Store` in bb{} writes it at `{ty}`, not at the slot's \
                                         own type `{}`",
                                        block.id.index(),
                                        slot.ty
                                    ),
                                ));
                            }
                        }
                    }
                    Inst::Load { ty, ptr, .. } => {
                        if let Some(&(owner, _)) = self.members.get(&ptr.index())
                            && let Some(slot) = self.slots.get(&owner)
                            && *ty != slot.ty
                        {
                            unsealing.push((
                                owner,
                                format!(
                                    "`Load` in bb{} reads it at `{ty}`, not at the slot's own \
                                     type `{}`",
                                    block.id.index(),
                                    slot.ty
                                ),
                            ));
                        }
                    }
                    // A borrow of a slot pointer joined the slot above; ending
                    // one is not a use of the slot's contents.
                    Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. } => {}
                    other => other.visit_value_operands(|operand| {
                        if let Some(&(owner, _)) = self.members.get(&operand.index()) {
                            unsealing.push((
                                owner,
                                format!(
                                    "its slot pointer %{} escapes into `{}` in bb{}",
                                    operand.index(),
                                    super::inst_variant_name(other),
                                    block.id.index()
                                ),
                            ));
                        }
                    }),
                }

                for (owner, reason) in unsealing {
                    self.unseal(owner, reason);
                }
            }
        }
    }

    /// The slot a pointer value addresses: `(owning Alloca result, slot)`.
    fn slot_of(&self, pointer: ValueId) -> Option<(u32, &Slot)> {
        let &(owner, _) = self.members.get(&pointer.index())?;
        self.slots.get(&owner).map(|slot| (owner, slot))
    }

    /// Whether some exact-typed store into `slot` — itself strictly after the
    /// slot's `Alloca` — dominates the instruction at `at`.
    fn initialized_at(&self, slot: &Slot, at: Point) -> bool {
        slot.stores.iter().any(|&store| {
            precedes(&self.dominators, slot.site, store) && precedes(&self.dominators, store, at)
        })
    }
}

/// Whether the instruction at `earlier` executes before the one at `later` on
/// every entry-to-`later` path: same block and strictly earlier, or a block
/// that strictly dominates `later`'s. Fails closed on an unreachable `later`
/// and on a CFG the dominator analysis could not use.
fn precedes(dominators: &DominatorTree, earlier: Point, later: Point) -> bool {
    if !dominators.is_reachable(later.0) {
        return false;
    }
    if earlier.0 == later.0 {
        earlier.1 < later.1
    } else {
        dominators.strictly_dominates(earlier.0, later.0)
    }
}

/// The shape a sealed slot must have, returning `T`'s natural alignment in
/// bytes.
fn slot_shape(
    layouts: &trust_ir::LayoutTable<'_>,
    nominal_types: &NominalTypeReachability<'_>,
    ty: &Ty,
    has_count: bool,
    align: Option<u64>,
) -> Result<u64, String> {
    if has_count {
        return Err(format!(
            "an `Alloca` with a dynamic count is an array of `{ty}`, and a handle slot holds \
             exactly one value"
        ));
    }
    if !sealable_slot_type(layouts.module(), nominal_types, ty, &mut Vec::new()) {
        return Err(format!(
            "`{ty}` is not a sealable slot type: a slot holds a handle, or a struct or tuple whose \
             handle-reaching lanes are themselves handles, structs or tuples (an enum, record, \
             array, closure, vector, set, sequence, refinement or reference carrying a handle \
             stays refused)"
        ));
    }
    let shape = layouts
        .ty_layout(ty)
        .map_err(|error| format!("`{ty}` has no computable layout ({error})"))?;
    let natural = match (shape.size_bytes(), shape.align_bits) {
        (Some(_), Some(bits)) if bits >= 8 && bits.is_multiple_of(8) => bits / 8,
        _ => {
            return Err(format!(
                "`{ty}` has no byte-exact size and alignment ({shape}), so its slot image is not \
                 a checkable memory cell"
            ));
        }
    };
    if let Some(align) = align
        && (align < natural || !align.is_power_of_two())
    {
        return Err(format!(
            "the `Alloca` align {align} is not a power of two at least the natural alignment \
             {natural} of `{ty}`"
        ));
    }
    Ok(natural)
}

/// A handle, or a struct / tuple whose every handle-reaching lane is itself
/// sealable. Anything else that reaches a handle — an enum, record, array,
/// closure, vector, set, sequence, refinement or reference — is not, and a
/// by-value struct cycle is refused rather than walked.
fn sealable_slot_type(
    module: &Module,
    nominal_types: &NominalTypeReachability<'_>,
    ty: &Ty,
    visiting: &mut Vec<StructId>,
) -> bool {
    match ty {
        Ty::Handle(_) => true,
        Ty::Struct(id) => {
            if visiting.contains(id) {
                return false;
            }
            let Some(def) = module.struct_def(*id) else {
                return false;
            };
            visiting.push(*id);
            let sealable = def.fields.iter().all(|field| {
                !nominal_types.contains_handle(&field.ty)
                    || sealable_slot_type(module, nominal_types, &field.ty, visiting)
            });
            visiting.pop();
            sealable
        }
        Ty::Tuple(lanes) => lanes.iter().all(|lane| {
            !nominal_types.contains_handle(lane)
                || sealable_slot_type(module, nominal_types, lane, visiting)
        }),
        _ => false,
    }
}

/// The refusal for a handle-typed `Load` / `Store` through a pointer that
/// addresses no sealed slot at all.
fn not_a_slot(op: &str, ty: &Ty) -> String {
    format!(
        "`{op}` at `{ty}` goes through a pointer that is not a sealed handle slot; a handle is \
         loaded and stored only through a function-local `alloca` of exactly its type whose \
         pointer never escapes (a handle behind a `Ref` / `RefMut` parameter is WS3.7 phase 2, \
         and a handle-typed global is refused)"
    )
}

/// The access-shape checks shared by `Load` and `Store`.
fn check_access(op: &str, slot: &Slot, volatile: bool, align: Option<u64>) -> Result<(), String> {
    if volatile {
        return Err(format!(
            "`{op}` of a handle slot of `{}` may not be volatile",
            slot.ty
        ));
    }
    match (align, slot.natural_align) {
        (None, Some(_)) => Ok(()),
        (Some(align), Some(natural)) if align == natural => Ok(()),
        (align, natural) => Err(format!(
            "`{op}` of a handle slot of `{}` states align {align:?}, not the type's natural \
             alignment {natural:?}",
            slot.ty
        )),
    }
}

/// WS3.7: the handle-arm verdict for `Alloca`, `Load` and `Store`.
///
/// Returns the ONE rule that failed, so the refusal names it. `slots` is the
/// function's analysis when it was built; when it is absent every access is
/// refused.
pub(super) fn handle_slot_rule(
    inst: &Inst,
    results: &[ValueId],
    val_ty: &BTreeMap<u32, Ty>,
    block: BlockId,
    index: usize,
    slots: Option<&SealedHandleSlots>,
) -> Result<(), String> {
    let at = (block, index);
    match inst {
        Inst::Alloca { ty, .. } => {
            let slot = match (slots, results) {
                (Some(slots), [result]) => slots.slots.get(&result.index()),
                _ => None,
            };
            let Some(slot) = slot else {
                return Err(format!(
                    "`Alloca` of `{ty}`: {SEALED}; this allocation defines no single slot pointer"
                ));
            };
            match &slot.unsealed {
                Some(reason) => Err(format!("`Alloca` of `{ty}`: {SEALED}; {reason}")),
                None => Ok(()),
            }
        }
        Inst::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            let slots = slots.ok_or_else(|| not_a_slot("Load", ty))?;
            let (owner, slot) = slots.slot_of(*ptr).ok_or_else(|| not_a_slot("Load", ty))?;
            if let Some(reason) = &slot.unsealed {
                return Err(format!(
                    "`Load` at `{ty}` reads the slot %{owner}, which is not sealed: {reason}"
                ));
            }
            if *ty != slot.ty {
                return Err(format!(
                    "`Load` at `{ty}` reads the slot %{owner} of `{}`; {SEALED}",
                    slot.ty
                ));
            }
            check_access("Load", slot, *volatile, *align)?;
            if slots.initialized_at(slot, at) {
                Ok(())
            } else {
                Err(format!(
                    "load of a handle slot not dominated by a store: `Load` in bb{} reads the \
                     slot %{owner} of `{ty}` where no store into it dominates the read, and an \
                     uninitialized word would be a forged handle",
                    block.index()
                ))
            }
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            let slots = slots.ok_or_else(|| not_a_slot("Store", ty))?;
            let (owner, slot) = slots.slot_of(*ptr).ok_or_else(|| not_a_slot("Store", ty))?;
            if let Some(reason) = &slot.unsealed {
                return Err(format!(
                    "`Store` at `{ty}` writes the slot %{owner}, which is not sealed: {reason}"
                ));
            }
            if *ty != slot.ty {
                return Err(format!(
                    "`Store` at `{ty}` writes the slot %{owner} of `{}`; {SEALED}",
                    slot.ty
                ));
            }
            if val_ty.get(&value.index()) != Some(ty) {
                return Err(format!(
                    "`Store` into the handle slot %{owner} of `{ty}` needs a value of exactly \
                     that type"
                ));
            }
            check_access("Store", slot, *volatile, *align)
        }
        _ => Err(format!(
            "`{}` is not a slot access",
            super::inst_variant_name(inst)
        )),
    }
}

#[cfg(test)]
pub(super) fn sealable_slot_type_test_oracle(
    module: &Module,
    nominal: &NominalTypeReachability<'_>,
    ty: &Ty,
) -> bool {
    sealable_slot_type(module, nominal, ty, &mut Vec::new())
}

#[cfg(test)]
pub(super) fn slot_shape_test_oracle(
    layouts: &trust_ir::LayoutTable<'_>,
    nominal: &NominalTypeReachability<'_>,
    ty: &Ty,
    has_count: bool,
    align: Option<u64>,
) -> Result<u64, String> {
    slot_shape(layouts, nominal, ty, has_count, align)
}

#[cfg(test)]
pub(super) fn sealed_slots_test_snapshot(
    layouts: &trust_ir::LayoutTable<'_>,
    function: &Function,
    nominal: &NominalTypeReachability<'_>,
) -> (
    Vec<(
        u32,
        Ty,
        (BlockId, usize),
        Option<u64>,
        Option<String>,
        Vec<(BlockId, usize)>,
    )>,
    Vec<(u32, (u32, (BlockId, usize)))>,
) {
    let analysis = SealedHandleSlots::new(layouts, function, nominal);
    let slots = analysis
        .slots
        .into_iter()
        .map(|(key, slot)| {
            (
                key,
                slot.ty,
                slot.site,
                slot.natural_align,
                slot.unsealed,
                slot.stores,
            )
        })
        .collect();
    (slots, analysis.members.into_iter().collect())
}
#[cfg(test)]
pub(super) fn sealed_slot_access_test_oracle(
    layouts: &trust_ir::LayoutTable<'_>,
    function: &Function,
    nominal: &NominalTypeReachability<'_>,
    inst: &Inst,
    results: &[ValueId],
    values: &BTreeMap<u32, Ty>,
    block: BlockId,
    index: usize,
    present: bool,
) -> Result<(), String> {
    let analysis = if present {
        Some(SealedHandleSlots::new(layouts, function, nominal))
    } else {
        None
    };
    handle_slot_rule(inst, results, values, block, index, analysis.as_ref())
}
#[cfg(test)]
pub(super) fn allocates_handle_test_oracle(
    function: &Function,
    nominal: &NominalTypeReachability<'_>,
) -> bool {
    SealedHandleSlots::function_allocates_a_handle(function, nominal)
}
