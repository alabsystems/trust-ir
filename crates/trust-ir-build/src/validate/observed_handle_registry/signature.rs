// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[cfg(test)]
mod tests;
struct State {
    signature: FuncTy,
    pending: Option<Ty>,
    name: String,
    runtime: String,
}
#[derive(Clone, Copy)]
enum Side {
    Params,
    Returns,
}
impl HandleRuntimePin {
    /// Exact original slot order: own handle identities or complete scalar Ty
    /// clones, ABI=None/vararg=false. Registry admission remains separate: even
    /// an invalid supplied Scalar is copied exactly, never silently legalized.
    /// Every actual slot/child clone/string/box/vector allocation and publication
    /// uses the supplied original owner. Partial results remain State-owned;
    /// no shorter signature is returned after cancellation/resource refusal.
    pub(crate) fn func_ty_observed<O: ExecutionObserver>(
        &self,
        entry: &HandleEntryPoint,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<ObservedPinnedFuncTy> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State {
            signature: FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                abi: None,
                is_vararg: false,
            },
            pending: None,
            name: String::new(),
            runtime: String::new(),
        };
        let result = (|| {
            work.admit(2, 2 * size_of::<&[PinnedTy]>() + 2 * size_of::<Side>())?;
            state.slots(self, entry.params, Side::Params, &mut work)?;
            state.slots(self, entry.returns, Side::Returns, &mut work)
        })();
        state.retire_scratch(&mut work);
        match result.and_then(|()| work.publication(size_of::<ObservedPinnedFuncTy>())) {
            Ok(()) => Ok(ObservedPinnedFuncTy {
                signature: state.signature,
            }),
            Err(error) => {
                work.retire_types(&mut state.signature.params);
                work.retire_types(&mut state.signature.returns);
                Err(work.terminal(error))
            }
        }
    }
}
impl State {
    fn slots<O: ExecutionObserver>(
        &mut self,
        pin: &HandleRuntimePin,
        slots: &[PinnedTy],
        side: Side,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0usize;
        while let Some(slot) = work.at(slots, at)? {
            work.admit(2, size_of::<Option<Ty>>() + size_of::<Side>())?;
            if self.pending.is_some() {
                return Err(ObservedValueError::InvalidRange);
            }
            match slot {
                PinnedTy::Scalar(ty) => {
                    self.pending = Some(ty.clone_observed(work.session, work.site)?)
                }
                PinnedTy::Handle => {
                    work.text(pin.name, &mut self.name)?;
                    work.text(pin.runtime, &mut self.runtime)?;
                    work.admit(
                        1,
                        size_of::<HandleTy>() + size_of::<Ty>() + size_of::<Option<Ty>>(),
                    )?;
                    self.pending = Some(Ty::Handle(Box::new(HandleTy {
                        name: take(&mut self.name),
                        runtime: take(&mut self.runtime),
                    })));
                }
            }
            let output = match side {
                Side::Params => &mut self.signature.params,
                Side::Returns => &mut self.signature.returns,
            };
            work.reserve(output)?;
            work.admit(1, size_of::<Ty>() + size_of::<Option<Ty>>())?;
            let value = self
                .pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?;
            output.push(value);
            work.next(&mut at)?;
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        work.step(size_of::<Option<Ty>>());
        if let Some(ty) = self.pending.take() {
            let _ = ty.retire_observed(work.session, work.site);
        }
        work.flat(take(&mut self.name));
        work.flat(take(&mut self.runtime));
    }
}
