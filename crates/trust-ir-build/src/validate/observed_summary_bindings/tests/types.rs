// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn types() -> Vec<Ty> {
    use trust_ir::ty::{DialectTy, FatPtrKind, HandleTy, SetRepr};
    use trust_ir::value::{ClosureTyId, EnumId, PredId, RecordId, StructId, TyId};
    vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Vector(Box::new(Ty::U32), 8),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Never,
        Ty::Struct(StructId::new(3)),
        Ty::Array(TyId::new(7), 64),
        Ty::Tuple(vec![Ty::U32]),
        Ty::Enum(EnumId::new(8)),
        Ty::Func(FuncTyId::new(9)),
        Ty::Ref(Box::new(Ty::U8)),
        Ty::RefMut(Box::new(Ty::U16)),
        Ty::PtrConst(Box::new(Ty::U32)),
        Ty::PtrMut(Box::new(Ty::U64)),
        Ty::Rc(Box::new(Ty::I32)),
        Ty::Set(TyId::new(1), SetRepr::Boxed),
        Ty::Sequence(TyId::new(2)),
        Ty::Record(RecordId::new(3)),
        Ty::Closure(ClosureTyId::new(4)),
        Ty::Refine(TyId::new(5), PredId::new(6)),
        Ty::Dialect(Box::new(DialectTy::new("vector", "lanes", 1))),
        Ty::Handle(Box::new(HandleTy::new("Nat", "trust_bignum::Nat"))),
    ]
}
