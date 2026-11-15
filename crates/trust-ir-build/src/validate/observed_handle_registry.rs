// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Real supplied-registry symbol lookup and pinned signature materialization.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use core::mem::{size_of, take};
use trust_ir::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
mod lookup;
mod signature;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
/// Owned expected signature data, not runtime/type/module/proof authority.
/// Only this module constructs the wrapper; no mutable, decoding, callback or
/// receipt constructor exists. Its signature has ABI=None/vararg=false, exactly
/// as HandleRuntimePin::func_ty. This closed invariant permits explicit actual
/// nested-type retirement without pretending to retire arbitrary ABI payloads.
pub(crate) struct ObservedPinnedFuncTy {
    signature: FuncTy,
}
impl ObservedPinnedFuncTy {
    /// Borrow the actual same core FuncTy identity for observed comparisons.
    pub(crate) fn signature(&self) -> &FuncTy {
        &self.signature
    }
    /// Consume all nested parameter/return types and buffers, even on a prior
    /// or new refusal, under the supplied original owner. Physical allocator/
    /// deallocator latency and original input disposal remain OPEN.
    pub(crate) fn retire_observed<O: ExecutionObserver>(
        mut self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.retire_types(&mut self.signature.params);
        work.retire_types(&mut self.signature.returns);
        work.step(size_of::<FuncTy>());
        drop(self);
        work.poll();
        work.complete_retirement()
    }
}
