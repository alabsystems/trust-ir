// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
pub(super) fn convention(value: CallingConv) -> &'static str {
    match value {
        CallingConv::C => "ccc",
        CallingConv::Fast => "fastcc",
        CallingConv::Cold => "coldcc",
        CallingConv::Rust => "rustcc",
        CallingConv::Swift => "swiftcc",
        CallingConv::CUnwind => "c_unwindcc",
        CallingConv::SysV64 => "sysv64cc",
        CallingConv::Win64 => "win64cc",
        CallingConv::Aapcs => "aapcscc",
        CallingConv::EfiApi => "efiapicc",
        CallingConv::VectorCall => "vectorcallcc",
        CallingConv::RustCold => "rust_coldcc",
    }
}
pub(super) fn visibility(value: trust_ir::Visibility) -> &'static str {
    match value {
        trust_ir::Visibility::Default => "default",
        trust_ir::Visibility::Hidden => "hidden",
        trust_ir::Visibility::Protected => "protected",
    }
}
/// Exact original format_func_ty output. A full returned child display is
/// retained in the State-owned render field before output copy or any fee.
pub(super) fn signature<O: ExecutionObserver>(
    signature: &FuncTy,
    output: &mut String,
    pending: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    types(&signature.params, output, pending, work)?;
    work.text(" -> ", output)?;
    types(&signature.returns, output, pending, work)
}
fn types<O: ExecutionObserver>(
    types: &[Ty],
    output: &mut String,
    pending: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.text("(", output)?;
    let mut at = 0usize;
    while let Some(ty) = work.at(types, at)? {
        work.admit(1, size_of::<bool>())?;
        if at != 0 {
            work.text(", ", output)?;
        }
        work.admit(1, size_of::<String>())?;
        if pending.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        *pending = ty.display_observed(work.session, work.site)?;
        work.text(pending, output)?;
        work.flat(take(pending));
        work.admit(1, 0)?;
        work.next(&mut at)?;
    }
    work.text(")", output)
}
impl State<'_> {
    pub(super) fn mismatch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, size_of::<usize>())?;
        if self.mismatches != 0 {
            work.text(", ", &mut self.actual)?;
        }
        work.text(&self.piece, &mut self.actual)?;
        work.flat(take(&mut self.piece));
        work.admit(1, size_of::<usize>())?;
        self.mismatches = self
            .mismatches
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
}
