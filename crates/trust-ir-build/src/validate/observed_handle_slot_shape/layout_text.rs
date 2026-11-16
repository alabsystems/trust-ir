// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn shape<O: ExecutionObserver>(
    value: &TyLayoutShape,
    work: &mut Work<'_, '_, O>,
) -> R<String> {
    work.admit(1, size_of::<String>())?;
    let mut output = String::new();
    let result = write(value, work, &mut output).and_then(|()| {
        work.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: work.site,
                work: 1,
                copy_bytes: size_of::<String>(),
            })
            .map_err(Into::into)
    });
    match result {
        Ok(()) => Ok(output),
        Err(error) => {
            work.flat(output);
            Err(work.terminal(error))
        }
    }
}
fn write<O: ExecutionObserver>(
    value: &TyLayoutShape,
    work: &mut Work<'_, '_, O>,
    out: &mut String,
) -> R {
    work.admit(1, size_of::<TyLayoutKind>())?;
    match &value.kind {
        TyLayoutKind::Storage => work.text("storage", out)?,
        TyLayoutKind::Scalar(value) => {
            work.text("scalar<", out)?;
            ty_shape(*value, work, out)?;
            work.text(">", out)?;
        }
        TyLayoutKind::ThinPointer => work.text("thin_pointer", out)?,
        TyLayoutKind::FatPointer(value) => {
            work.text("fat_pointer<", out)?;
            metadata(*value, work, out)?;
            work.text(">", out)?;
        }
        TyLayoutKind::Struct { id, fields } => {
            work.text("struct.", out)?;
            work.unsigned(u128::from(id.index()), out)?;
            work.text("[", out)?;
            work.unsigned(fields.len() as u128, out)?;
            work.text(" fields]", out)?;
        }
        TyLayoutKind::Tuple { fields } => {
            work.text("tuple<", out)?;
            work.unsigned(fields.len() as u128, out)?;
            work.text(" fields>", out)?;
        }
        TyLayoutKind::Closure { id, captures } => {
            work.text("closure<", out)?;
            work.unsigned(u128::from(id.index()), out)?;
            work.text(", ", out)?;
            work.unsigned(captures.len() as u128, out)?;
            work.text(" captures>", out)?;
        }
        TyLayoutKind::Enum { id, variants } => {
            work.text("enum.", out)?;
            work.unsigned(u128::from(id.index()), out)?;
            work.text("[", out)?;
            work.unsigned(*variants as u128, out)?;
            work.text(" variants]", out)?;
        }
        TyLayoutKind::Array {
            elem,
            len,
            stride_bits,
        } => {
            work.text("array<ty.", out)?;
            work.unsigned(u128::from(elem.index()), out)?;
            work.text(", len=", out)?;
            work.unsigned(u128::from(*len), out)?;
            work.text(", stride=", out)?;
            work.unsigned(u128::from(*stride_bits), out)?;
            work.text("b>", out)?;
        }
        TyLayoutKind::Vector {
            elem_shape,
            lanes,
            lane_bits,
        } => {
            work.text("vector<", out)?;
            work.unsigned(u128::from(*lanes), out)?;
            work.text(" x ", out)?;
            ty_shape(*elem_shape, work, out)?;
            work.text(", lane=", out)?;
            work.unsigned(u128::from(*lane_bits), out)?;
            work.text("b>", out)?;
        }
        TyLayoutKind::Unit => work.text("unit", out)?,
        TyLayoutKind::Never => work.text("never", out)?,
        TyLayoutKind::FnItem => work.text("function_item", out)?,
    }
    work.admit(1, size_of::<u64>() + size_of::<Option<u64>>())?;
    work.text(" size=", out)?;
    work.unsigned(u128::from(value.size_bits), out)?;
    work.text("b align=", out)?;
    if let Some(align) = value.align_bits {
        work.unsigned(u128::from(align), out)?;
        work.text("b", out)?;
    } else {
        work.text("?", out)?;
    }
    Ok(())
}
fn metadata<O: ExecutionObserver>(
    value: PointerMetadataShape,
    work: &mut Work<'_, '_, O>,
    out: &mut String,
) -> R {
    work.admit(1, size_of::<PointerMetadataShape>())?;
    match value {
        PointerMetadataShape::SliceLen { elem } => {
            work.text("slice_len<ty.", out)?;
            work.unsigned(u128::from(elem.index()), out)?;
            work.text(">", out)
        }
        PointerMetadataShape::StrLen => work.text("str_len", out),
        PointerMetadataShape::VTable { trait_id } => {
            work.text("vtable<dyn.", out)?;
            work.unsigned(u128::from(trait_id), out)?;
            work.text(">", out)
        }
        PointerMetadataShape::ContainerLen => work.text("container_len", out),
        PointerMetadataShape::ContainerVtable => work.text("container_vtable", out),
    }
}
fn ty_shape<O: ExecutionObserver>(
    value: TyShape,
    work: &mut Work<'_, '_, O>,
    out: &mut String,
) -> R {
    work.admit(1, size_of::<TyShape>())?;
    let text = match value {
        TyShape::Storage => "storage",
        TyShape::Int { signed, bits } => {
            work.text(if signed { "i" } else { "u" }, out)?;
            return work.unsigned(u128::from(bits), out);
        }
        TyShape::Float { bits } => {
            work.text("f", out)?;
            return work.unsigned(u128::from(bits), out);
        }
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
        TyShape::FnItem => "fnitem",
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
    };
    work.text(text, out)
}
