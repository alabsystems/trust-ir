// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn opcode(&mut self, op: CastOp) -> R<&'static str> {
        self.admit(17, size_of::<&str>())?;
        Ok(match op {
            CastOp::Trunc => "trunc",
            CastOp::ZExt => "zext",
            CastOp::SExt => "sext",
            CastOp::FPTrunc => "fptrunc",
            CastOp::FPExt => "fpext",
            CastOp::FPToUI => "fptoui",
            CastOp::FPToSI => "fptosi",
            CastOp::UIToFP => "uitofp",
            CastOp::SIToFP => "sitofp",
            CastOp::PtrToInt => "ptrtoint",
            CastOp::IntToPtr => "inttoptr",
            CastOp::PtrToPtr => "ptrtoptr",
            CastOp::Bitcast => "bitcast",
            CastOp::Transmute => "transmute",
            CastOp::ReifyFnPointer => "reify_fn_pointer",
            CastOp::FPToSISat => "fptosi.sat",
            CastOp::FPToUISat => "fptoui.sat",
        })
    }
    pub(super) fn shape(&mut self, shape: TyShape, output: &mut String) -> R {
        self.admit(29, size_of::<&str>())?;
        match shape {
            TyShape::Int { signed, bits } => {
                self.text(if signed { "i" } else { "u" }, output)?;
                self.decimal(bits, output)
            }
            TyShape::Float { bits } => {
                self.text("f", output)?;
                self.decimal(bits, output)
            }
            other => self.text(
                match other {
                    TyShape::Storage => "storage",
                    TyShape::PointerInt { signed } => {
                        if signed {
                            "isize"
                        } else {
                            "usize"
                        }
                    }
                    TyShape::Error => "error",
                    TyShape::Bool => "bool",
                    TyShape::ThinPointer => "thin_pointer",
                    TyShape::FatPointer => "fat_pointer",
                    TyShape::Unit => "unit",
                    TyShape::Never => "never",
                    TyShape::Struct => "struct",
                    TyShape::Array => "array",
                    TyShape::Vector => "vector",
                    TyShape::Tuple => "tuple",
                    TyShape::Enum => "enum",
                    TyShape::Function => "function",
                    TyShape::Ref => "ref",
                    TyShape::RefMut => "ref_mut",
                    TyShape::PtrConst => "ptr_const",
                    TyShape::PtrMut => "ptr_mut",
                    TyShape::Rc => "rc",
                    TyShape::Set => "set",
                    TyShape::Sequence => "sequence",
                    TyShape::Record => "record",
                    TyShape::Closure => "closure",
                    TyShape::Refine => "refine",
                    TyShape::Dialect => "dialect",
                    TyShape::Handle => "handle",
                    TyShape::Tensor => "tensor",
                    TyShape::Int { .. } | TyShape::Float { .. } => {
                        return Err(ObservedValueError::InvalidRange);
                    }
                },
                output,
            ),
        }
    }
}
