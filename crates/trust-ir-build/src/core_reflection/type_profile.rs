// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bound inline type trees before validation, hashing, cloning or layout work.

use super::{Result, reject};
use trust_ir::{Module, Ty};

pub(super) fn supported(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Usize
            | Ty::Ptr
            | Ty::FatPtr(_)
            | Ty::Unit
            | Ty::Func(_)
            | Ty::Array(_, _)
            | Ty::Struct(_)
            | Ty::Tuple(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
    )
}

pub(super) fn check(module: &Module, limit: usize) -> Result<()> {
    check_bounded(module, limit, false)
}

pub(super) fn check_with_runtime_signature_descriptors(
    module: &Module,
    limit: usize,
) -> Result<()> {
    check_bounded(module, limit, true)
}

fn check_bounded(module: &Module, limit: usize, descriptor_floats: bool) -> Result<()> {
    const MAX_DEPTH: usize = 64;
    // The shared walker is iterative and visits inline trees in preorder,
    // without following table IDs. Pending child counts recover their depth
    // without recursion or a second copy of the trees. A completed stack
    // denotes a new root (another signature, table row or instruction type).
    let mut ancestors: Vec<(usize, usize)> = Vec::new();
    let mut count = 0usize;
    let mut refusal = None;
    module.visit_types(|ty| {
        if refusal.is_some() {
            return;
        }
        while ancestors
            .last()
            .is_some_and(|(_, remaining)| *remaining == 0)
        {
            ancestors.pop();
        }
        let depth = if let Some((parent_depth, remaining)) = ancestors.last_mut() {
            *remaining -= 1;
            *parent_depth + 1
        } else {
            1
        };
        if count == limit || depth > MAX_DEPTH {
            refusal = Some("byte-profile inline type size or depth limit");
            return;
        }
        count += 1;
        // This is the bounded whole-tree preflight, not value permission.
        // The reflector independently rechecks every executable type in its
        // strict role before consulting a role-keyed cache.
        if !(supported(ty) || descriptor_floats && matches!(ty, Ty::F16 | Ty::F32 | Ty::F64)) {
            refusal = Some("unsupported byte-profile type");
            return;
        }
        let children = match ty {
            Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) => 1,
            Ty::Tuple(fields) => fields.len(),
            _ => 0,
        };
        if children != 0 {
            ancestors.push((depth, children));
        }
    });
    refusal.map_or(Ok(()), |reason| Err(reject(reason)))
}
