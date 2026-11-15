// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn vararg<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<CallingConv>())?;
        if !matches!(function.calling_conv, CallingConv::Rust) {
            return Ok(());
        }
        work.admit(1, size_of::<u32>())?;
        let index = function.ty.index();
        let Some(signature) = work.at(&module.func_types, index as usize)? else {
            return Ok(());
        };
        work.admit(1, size_of::<bool>())?;
        if !signature.is_vararg {
            return Ok(());
        }
        work.admit(1, 0)?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        work.quoted(&function.name, &mut self.detail)?;
        work.text(
            " declares the Rust calling convention with variadic functy.",
            &mut self.detail,
        )?;
        work.admit(1, size_of::<u128>())?;
        work.number(u128::from(index), &mut self.detail)?;
        work.text(" (", &mut self.detail)?;
        work.admit(2, size_of::<usize>() + size_of::<u128>())?;
        work.number(signature.params.len() as u128, &mut self.detail)?;
        work.text(" fixed parameter(s))", &mut self.detail)?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<ValidationError>() + size_of::<u32>())?;
        self.errors.push(ValidationError::RustAbiVararg {
            function: function.id.index(),
            detail: take(&mut self.detail),
        });
        Ok(())
    }
}
