// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The layout-sensitive cast rule's three reachability walks, and the rule H
//! carrier walk, as they were before the reachability memo (`trust_ir`'s
//! `reach` module, behind `LayoutTable::type_reaches_handle` /
//! `type_holds_closure_by_value` / `type_stores_bool_lane`): kept verbatim
//! (`self` spelled `module`) as the oracle of `by_value_reach_differential`.
//!
//! * `type_holds_closure_by_value` and `type_stores_bool_lane` recursed on the
//!   native stack behind `Vec` guards and scanned the whole definition list at
//!   every nominal node (`shape.rs` before the memo);
//! * `type_reaches_handle` walked a heap frontier but scanned the whole
//!   definition list at every struct, enum and record referent, and
//!   `callable_carriers` likewise (`type_reachability.rs` before the memo);
//! * `layout_sensitive_cast_evidence` asked those walks, then the layouts
//!   (here through `Module::ty_layout_shape`, whose table is held to its own
//!   recursion by `layout_table_differential`).
//!
//! One arm postdates the memo: `Ty::Tensor` (the tensor region, PKG-U13a)
//! holds its element inline, so each walk descends into it exactly as into a
//! `Vector`'s lane, which is what the memo's inline scan does.

use std::collections::HashSet;

use trust_ir::ty::{FatPtrKind, Ty};
use trust_ir::value::{EnumId, RecordId, StructId, TyId};
use trust_ir::{CallableCarriers, CastLayoutEvidence, CastOp, LayoutError, Module};

// ---------------------------------------------------------------------------
// Closure held by value (shape.rs, `Module::type_holds_closure_by_value`)
// ---------------------------------------------------------------------------

pub fn type_holds_closure_by_value(module: &Module, ty: &Ty) -> bool {
    let mut seen_structs: Vec<StructId> = Vec::new();
    let mut seen_enums: Vec<EnumId> = Vec::new();
    let mut seen_records: Vec<RecordId> = Vec::new();
    let mut seen_tys: Vec<TyId> = Vec::new();
    holds_closure_by_value_inner(
        module,
        ty,
        &mut seen_structs,
        &mut seen_enums,
        &mut seen_records,
        &mut seen_tys,
    )
}

fn holds_closure_by_value_inner(
    module: &Module,
    ty: &Ty,
    seen_structs: &mut Vec<StructId>,
    seen_enums: &mut Vec<EnumId>,
    seen_records: &mut Vec<RecordId>,
    seen_tys: &mut Vec<TyId>,
) -> bool {
    match ty {
        Ty::Closure(_) => true,
        Ty::Tuple(elems) => elems.iter().any(|elem| {
            holds_closure_by_value_inner(
                module,
                elem,
                seen_structs,
                seen_enums,
                seen_records,
                seen_tys,
            )
        }),
        Ty::Vector(elem, _) | Ty::Tensor(elem, _) => holds_closure_by_value_inner(
            module,
            elem,
            seen_structs,
            seen_enums,
            seen_records,
            seen_tys,
        ),
        Ty::Array(id, _) | Ty::Refine(id, _) => {
            if seen_tys.contains(id) {
                return false;
            }
            seen_tys.push(*id);
            module.types.get(id.as_usize()).is_some_and(|inner| {
                holds_closure_by_value_inner(
                    module,
                    inner,
                    seen_structs,
                    seen_enums,
                    seen_records,
                    seen_tys,
                )
            })
        }
        Ty::Struct(id) => {
            if seen_structs.contains(id) {
                return false;
            }
            seen_structs.push(*id);
            module
                .structs
                .iter()
                .filter(|def| def.id == *id)
                .flat_map(|def| def.fields.iter())
                .any(|field| {
                    holds_closure_by_value_inner(
                        module,
                        &field.ty,
                        seen_structs,
                        seen_enums,
                        seen_records,
                        seen_tys,
                    )
                })
        }
        Ty::Enum(id) => {
            if seen_enums.contains(id) {
                return false;
            }
            seen_enums.push(*id);
            module
                .enums
                .iter()
                .filter(|def| def.id == *id)
                .flat_map(|def| def.variants.iter())
                .flat_map(|variant| variant.fields.iter())
                .any(|field| {
                    holds_closure_by_value_inner(
                        module,
                        field,
                        seen_structs,
                        seen_enums,
                        seen_records,
                        seen_tys,
                    )
                })
        }
        Ty::Record(id) => {
            if seen_records.contains(id) {
                return false;
            }
            seen_records.push(*id);
            module
                .records
                .iter()
                .filter(|def| def.id == *id)
                .flat_map(|def| def.fields.iter())
                .any(|field| {
                    holds_closure_by_value_inner(
                        module,
                        &field.ty,
                        seen_structs,
                        seen_enums,
                        seen_records,
                        seen_tys,
                    )
                })
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Bool lane stored by value (shape.rs, `Module::type_stores_bool_lane`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ByValueReferent {
    Ty(TyId),
    Struct(StructId),
    Enum(EnumId),
}

fn push_unseen(seen: &mut Vec<ByValueReferent>, referent: ByValueReferent) -> bool {
    if seen.contains(&referent) {
        return false;
    }
    seen.push(referent);
    true
}

pub fn type_stores_bool_lane(module: &Module, ty: &Ty) -> bool {
    type_stores_bool_lane_inner(module, ty, &mut Vec::new())
}

fn type_stores_bool_lane_inner(module: &Module, ty: &Ty, seen: &mut Vec<ByValueReferent>) -> bool {
    match ty {
        Ty::Bool => true,
        Ty::Vector(elem, _) | Ty::Tensor(elem, _) => {
            type_stores_bool_lane_inner(module, elem, seen)
        }
        Ty::Tuple(elems) => elems
            .iter()
            .any(|elem| type_stores_bool_lane_inner(module, elem, seen)),
        Ty::Array(id, _) | Ty::Refine(id, _) => {
            if !push_unseen(seen, ByValueReferent::Ty(*id)) {
                return false;
            }
            module
                .types
                .get(id.as_usize())
                .is_some_and(|referent| type_stores_bool_lane_inner(module, referent, seen))
        }
        Ty::Struct(id) => {
            if !push_unseen(seen, ByValueReferent::Struct(*id)) {
                return false;
            }
            module
                .structs
                .iter()
                .filter(|def| def.id == *id)
                .flat_map(|def| def.fields.iter())
                .any(|field| type_stores_bool_lane_inner(module, &field.ty, seen))
        }
        Ty::Enum(id) => {
            if !push_unseen(seen, ByValueReferent::Enum(*id)) {
                return false;
            }
            module
                .enums
                .iter()
                .filter(|def| def.id == *id)
                .flat_map(|def| def.variants.iter())
                .flat_map(|variant| variant.fields.iter())
                .any(|field| type_stores_bool_lane_inner(module, field, seen))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Handle reached through table references, and the carriers of a value
// (type_reachability.rs, `Module::type_reaches_handle` / `callable_carriers`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TableReferent {
    Ty(usize),
    FuncTy(usize),
    Struct(u32),
    Enum(u32),
    Record(u32),
    ClosureTy(usize),
}

fn table_referent(ty: &Ty) -> Option<TableReferent> {
    Some(match ty {
        Ty::Array(id, _)
        | Ty::Set(id, _)
        | Ty::Sequence(id)
        | Ty::Refine(id, _)
        | Ty::FatPtr(FatPtrKind::Slice(id)) => TableReferent::Ty(id.as_usize()),
        Ty::Func(id) => TableReferent::FuncTy(id.as_usize()),
        Ty::Struct(id) => TableReferent::Struct(id.index()),
        Ty::Enum(id) => TableReferent::Enum(id.index()),
        Ty::Record(id) => TableReferent::Record(id.index()),
        Ty::Closure(id) => TableReferent::ClosureTy(id.as_usize()),
        _ => return None,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Signatures {
    Expand,
    Skip,
}

fn scan_occurrences(
    ty: &Ty,
    seen: &mut HashSet<TableReferent>,
    frontier: &mut Vec<TableReferent>,
) -> bool {
    let mut found = false;
    ty.visit_types(|child| {
        found |= matches!(child, Ty::Handle(_));
        if let Some(referent) = table_referent(child)
            && seen.insert(referent)
        {
            frontier.push(referent);
        }
    });
    found
}

pub fn type_reaches_handle(module: &Module, root: &Ty) -> bool {
    let mut seen: HashSet<TableReferent> = HashSet::new();
    let mut frontier: Vec<TableReferent> = Vec::new();
    if scan_occurrences(root, &mut seen, &mut frontier) {
        return true;
    }
    let mut members: Vec<&Ty> = Vec::new();
    while let Some(referent) = frontier.pop() {
        members.clear();
        // A missing entry contributes no edge (a validation error).
        let _ = referent_members(
            module,
            referent,
            Signatures::Expand,
            &mut seen,
            &mut members,
        );
        for member in &members {
            if scan_occurrences(member, &mut seen, &mut frontier) {
                return true;
            }
        }
    }
    false
}

pub fn callable_carriers(module: &Module, ty: &Ty) -> CallableCarriers {
    let mut carriers = CallableCarriers::default();
    let mut seen: HashSet<TableReferent> = HashSet::new();
    let mut frontier: Vec<TableReferent> = Vec::new();
    let mut members: Vec<&Ty> = vec![ty];
    loop {
        for member in members.drain(..) {
            member.visit_types(|child| {
                record_carrier(&mut carriers, child);
                if let Some(referent) = table_referent(child)
                    && seen.insert(referent)
                {
                    frontier.push(referent);
                }
            });
        }
        let Some(referent) = frontier.pop() else {
            return carriers;
        };
        // A function pointer's signature is not a carried value.
        carriers.opaque |=
            !referent_members(module, referent, Signatures::Skip, &mut seen, &mut members);
    }
}

fn record_carrier(carriers: &mut CallableCarriers, ty: &Ty) {
    match ty {
        Ty::Func(signature) => {
            carriers.fn_types.insert(*signature);
        }
        Ty::Closure(closure) => {
            carriers.closures.insert(*closure);
        }
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id }) => {
            carriers.principals.insert(*trait_id);
        }
        Ty::FatPtr(FatPtrKind::ContainerVtable) => carriers.erased_dyn = true,
        Ty::Ptr | Ty::Dialect(_) | Ty::Error => carriers.opaque = true,
        _ => {}
    }
}

fn referent_members<'module>(
    module: &'module Module,
    referent: TableReferent,
    signatures: Signatures,
    seen: &mut HashSet<TableReferent>,
    members: &mut Vec<&'module Ty>,
) -> bool {
    let expand = signatures == Signatures::Expand;
    let found = |count: usize| count > 0;
    match referent {
        TableReferent::Ty(index) => module.types.get(index).map(|ty| members.push(ty)).is_some(),
        TableReferent::FuncTy(index) => {
            let signature = module.func_types.get(index);
            if expand && let Some(signature) = signature {
                members.extend(signature.params.iter().chain(&signature.returns));
            }
            signature.is_some()
        }
        TableReferent::Struct(id) => found(
            module
                .structs
                .iter()
                .filter(|def| def.id.index() == id)
                .inspect(|def| members.extend(def.fields.iter().map(|field| &field.ty)))
                .count(),
        ),
        TableReferent::Enum(id) => found(
            module
                .enums
                .iter()
                .filter(|def| def.id.index() == id)
                .inspect(|def| {
                    members.extend(
                        def.variants
                            .iter()
                            .flat_map(|variant| variant.fields.iter()),
                    )
                })
                .count(),
        ),
        TableReferent::Record(id) => found(
            module
                .records
                .iter()
                .filter(|def| def.id.index() == id)
                .inspect(|def| members.extend(def.fields.iter().map(|field| &field.ty)))
                .count(),
        ),
        TableReferent::ClosureTy(index) => {
            let Some(closure) = module.closure_types.get(index) else {
                return false;
            };
            members.extend(&closure.captures);
            if expand
                && let Some(signature) = module.func_types.get(closure.func.as_usize())
                && seen.insert(TableReferent::FuncTy(closure.func.as_usize()))
            {
                members.extend(signature.params.iter().chain(&signature.returns));
            }
            true
        }
    }
}

// ---------------------------------------------------------------------------
// The cast rule (shape.rs, `LayoutTable::layout_sensitive_cast_evidence`)
// ---------------------------------------------------------------------------

pub fn legacy_layout_sensitive_cast_evidence(
    module: &Module,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
) -> Result<CastLayoutEvidence, LayoutError> {
    if !op.is_layout_sensitive() {
        return Ok(CastLayoutEvidence::NotLayoutSensitive);
    }
    if type_reaches_handle(module, src) || type_reaches_handle(module, dst) {
        return Err(LayoutError::OpaqueHandleCast {
            src: src.shape(),
            dst: dst.shape(),
        });
    }
    if type_holds_closure_by_value(module, src) || type_holds_closure_by_value(module, dst) {
        return Err(LayoutError::ClosureCast {
            src: src.shape(),
            dst: dst.shape(),
        });
    }

    match op {
        CastOp::PtrToPtr => {
            let pointer_bits = module.pointer_bits();
            let src_layout = src
                .pointer_layout_shape(pointer_bits)
                .ok_or_else(|| LayoutError::NotPointer(src.shape()))?;
            let dst_layout = dst
                .pointer_layout_shape(pointer_bits)
                .ok_or_else(|| LayoutError::NotPointer(dst.shape()))?;
            if src_layout.lane_count() != dst_layout.lane_count() {
                return Err(LayoutError::PointerLaneMismatch {
                    src_lanes: src_layout.lane_count(),
                    dst_lanes: dst_layout.lane_count(),
                });
            }
            if src_layout.metadata != dst_layout.metadata {
                return Err(LayoutError::PointerMetadataMismatch {
                    src: src_layout.metadata,
                    dst: dst_layout.metadata,
                });
            }
            Ok(CastLayoutEvidence::PointerCast {
                src: src_layout,
                dst: dst_layout,
            })
        }
        CastOp::Bitcast | CastOp::Transmute => {
            if src != dst
                && (type_stores_bool_lane(module, src) || type_stores_bool_lane(module, dst))
            {
                return Err(LayoutError::BoolLaneReinterpret {
                    src: src.shape(),
                    dst: dst.shape(),
                });
            }
            let src_layout = module.ty_layout_shape(src)?;
            let dst_layout = module.ty_layout_shape(dst)?;
            if src_layout.size_bits != dst_layout.size_bits {
                return Err(LayoutError::CastSizeMismatch {
                    src_bits: src_layout.size_bits,
                    dst_bits: dst_layout.size_bits,
                });
            }
            Ok(CastLayoutEvidence::SameSize {
                size_bits: src_layout.size_bits,
                src_align_bits: src_layout.align_bits,
                dst_align_bits: dst_layout.align_bits,
            })
        }
        CastOp::ReifyFnPointer => {
            if !matches!(src, Ty::Func(_)) {
                return Err(LayoutError::NotFunctionPointerSource(src.shape()));
            }
            let pointer_bits = module.pointer_bits();
            let dst_layout = dst
                .pointer_layout_shape(pointer_bits)
                .ok_or_else(|| LayoutError::NotPointer(dst.shape()))?;
            if dst_layout.is_fat() {
                return Err(LayoutError::PointerLaneMismatch {
                    src_lanes: 1,
                    dst_lanes: dst_layout.lane_count(),
                });
            }
            Ok(CastLayoutEvidence::ReifyFnPointer { pointer_bits })
        }
        _ => Ok(CastLayoutEvidence::NotLayoutSensitive),
    }
}

/// The current Storage-first cast policy layered over the frozen legacy rule.
/// Handle refusal still precedes Storage; all remaining legacy answers stay
/// byte-for-byte derived by the historical function above. This independent
/// reference never delegates Storage presence to the implementation under test.
pub fn layout_sensitive_cast_evidence(
    module: &Module,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
) -> Result<CastLayoutEvidence, LayoutError> {
    if op.is_layout_sensitive()
        && !type_reaches_handle(module, src)
        && !type_reaches_handle(module, dst)
        && (storage_value_present(module, src) || storage_value_present(module, dst))
    {
        return Err(LayoutError::UnsupportedTyShape(
            trust_ir::shape::TyShape::Storage,
        ));
    }
    legacy_layout_sensitive_cast_evidence(module, op, src, dst)
}

/// Independent raw-definition Storage-presence walk for the current policy.
/// It follows every declared by-value child, including duplicate definitions,
/// empty arrays and inactive enum fields. Missing rows and seedless cycles add
/// no Storage. Pointer/code boundaries stop; closure captures do not.
///
/// This is presence, not StorageClosed validity, layout, initialization or ABI
/// admission. It deliberately uses no Module/LayoutTable reach query or memo.
pub fn storage_value_present(module: &Module, root: &Ty) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(ty) = pending.pop() {
        match ty {
            Ty::Storage(_) => return true,
            Ty::Tuple(fields) => pending.extend(fields),
            Ty::Vector(element, _) | Ty::Tensor(element, _) => pending.push(element),
            Ty::Array(id, _) | Ty::Refine(id, _) | Ty::Sequence(id) | Ty::Set(id, _) => {
                if seen.insert(TableReferent::Ty(id.as_usize()))
                    && let Some(child) = module.types.get(id.as_usize())
                {
                    pending.push(child);
                }
            }
            Ty::Struct(id) => {
                if seen.insert(TableReferent::Struct(id.index())) {
                    for row in module.structs.iter().filter(|row| row.id == *id) {
                        pending.extend(row.fields.iter().map(|field| &field.ty));
                    }
                }
            }
            Ty::Enum(id) => {
                if seen.insert(TableReferent::Enum(id.index())) {
                    for row in module.enums.iter().filter(|row| row.id == *id) {
                        pending.extend(row.variants.iter().flat_map(|variant| &variant.fields));
                    }
                }
            }
            Ty::Record(id) => {
                if seen.insert(TableReferent::Record(id.index())) {
                    for row in module.records.iter().filter(|row| row.id == *id) {
                        pending.extend(row.fields.iter().map(|field| &field.ty));
                    }
                }
            }
            Ty::Closure(id) => {
                if seen.insert(TableReferent::ClosureTy(id.as_usize()))
                    && let Some(row) = module.closure_types.get(id.as_usize())
                {
                    pending.extend(&row.captures);
                }
            }
            // Scalars, opaque types, pointers/references/Rc/fat pointers and
            // function pointers carry no by-value Storage child.
            _ => {}
        }
    }
    false
}
