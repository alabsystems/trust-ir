// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
mod typed;
mod untyped;

pub(super) fn all() -> Vec<Inst> {
    let mut all = typed::all();
    all.extend(untyped::all());
    all.extend([
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::U32,
            dst_ty: Ty::F32,
            operand: v(1),
        },
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(1),
            indices: vec![v(1)],
            inbounds: true,
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(1),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            ptr: v(1),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            data: v(1),
            metadata: v(1),
        },
        frame(2),
        dialect(2),
    ]);
    all
}
