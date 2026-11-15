// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn places<O: ExecutionObserver>(
        &mut self,
        _module: &Module,
        function: &Function,
        signature: Option<&FuncTy>,
        obligation: &ProofObligation,
        name: &str,
        binding: &ClauseBinding,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(12, size_of::<ClausePlace>())?;
        match binding.place {
            ClausePlace::Param { index }
            | ClausePlace::MutParamExit { index }
            | ClausePlace::ParamPointeeEntry { index } => {
                work.admit(17, size_of::<bool>())?;
                if matches!(binding.place, ClausePlace::MutParamExit { .. })
                    && !matches!(
                        obligation.kind,
                        ObligationKind::Postcondition | ObligationKind::GiveBackRefinement
                    )
                {
                    self.bind_prefix(name, binding.place, work)?;
                    work.text(
                        ", the give-back / primed exit value, on a ",
                        &mut self.detail,
                    )?;
                    work.kind(&obligation.kind, &mut self.detail)?;
                    work.text(" obligation; it is a post-state place, legal only on a Postcondition or a GiveBackRefinement",&mut self.detail)?;
                    self.emit(obligation, work)?;
                }
                self.arity(
                    function,
                    signature,
                    obligation,
                    name,
                    binding.place,
                    index,
                    false,
                    work,
                )?;
            }
            ClausePlace::ResultSlot { index } => self.arity(
                function,
                signature,
                obligation,
                name,
                binding.place,
                index,
                true,
                work,
            )?,
            ClausePlace::Unwind => {
                work.admit(1, size_of::<bool>())?;
                if matches!(obligation.kind, ObligationKind::Precondition) {
                    work.text("binds ", &mut self.detail)?;
                    work.quoted(name, &mut self.detail)?;
                    work.text(" to the in-flight unwind state on a Precondition; a precondition is evaluated before the call, where no unwind is in flight",&mut self.detail)?;
                    self.emit(obligation, work)?;
                }
            }
            ClausePlace::Value(value) => {
                work.admit(1, size_of::<bool>())?;
                if function.blocks.is_empty() {
                    self.bind_prefix(name, binding.place, work)?;
                    work.text(" of function #", &mut self.detail)?;
                    work.number(u128::from(function.id.index()), &mut self.detail)?;
                    work.text(
                        ", a body-less declaration with no body to resolve it in",
                        &mut self.detail,
                    )?;
                    self.emit(obligation, work)?;
                } else if !scan::defined(function, value, work)? {
                    self.bind_prefix(name, binding.place, work)?;
                    work.text(", which function #", &mut self.detail)?;
                    work.number(u128::from(function.id.index()), &mut self.detail)?;
                    work.text("'s body never defines", &mut self.detail)?;
                    self.emit(obligation, work)?;
                }
            }
            ClausePlace::WorldPost => {
                work.admit(16, size_of::<bool>())?;
                if !matches!(
                    obligation.kind,
                    ObligationKind::Postcondition | ObligationKind::GiveBackRefinement
                ) {
                    self.bind_prefix(name, binding.place, work)?;
                    work.text(", the world at exit, on a ", &mut self.detail)?;
                    work.kind(&obligation.kind, &mut self.detail)?;
                    work.text(" obligation; it is a post-state place, legal only on a Postcondition or a GiveBackRefinement",&mut self.detail)?;
                    self.emit(obligation, work)?;
                }
            }
            ClausePlace::WorldPre
            | ClausePlace::World
            | ClausePlace::SpecVar { .. }
            | ClausePlace::SpecVarNext { .. } => {}
        }
        Ok(())
    }
    fn arity<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        signature: Option<&FuncTy>,
        obligation: &ProofObligation,
        name: &str,
        place: ClausePlace,
        index: u32,
        result: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 2 * size_of::<usize>())?;
        let at = usize::try_from(index).map_err(|_| ObservedValueError::CapacityOverflow)?;
        if let Some(ft) = signature {
            let length = if result {
                ft.returns.len()
            } else {
                ft.params.len()
            };
            if at < length {
                return Ok(());
            }
            self.bind_prefix(name, place, work)?;
            work.text(" but function #", &mut self.detail)?;
            work.number(u128::from(function.id.index()), &mut self.detail)?;
            work.text("'s signature declares ", &mut self.detail)?;
            work.number(length as u128, &mut self.detail)?;
            work.text(
                if result {
                    " return value(s)"
                } else {
                    " parameter(s)"
                },
                &mut self.detail,
            )?;
        } else {
            self.bind_prefix(name, place, work)?;
            work.text(", which cannot be resolved: functy.", &mut self.detail)?;
            work.number(u128::from(function.ty.index()), &mut self.detail)?;
            work.text(" is not declared in this module", &mut self.detail)?;
        }
        self.emit(obligation, work)
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn kind(&mut self, kind: &ObligationKind, out: &mut String) -> R {
        self.admit(16, size_of::<&str>())?;
        let text = match kind {
            ObligationKind::Precondition => "precondition",
            ObligationKind::Postcondition => "postcondition",
            ObligationKind::LoopInvariant => "loop_invariant",
            ObligationKind::TypeInvariant => "type_invariant",
            ObligationKind::RefinementType => "refinement_type",
            ObligationKind::TranslationValidation => "translation_validation",
            ObligationKind::MemorySafety => "memory_safety",
            ObligationKind::PanicFreedom => "panic_freedom",
            ObligationKind::TemporalSafety => "temporal_safety",
            ObligationKind::Liveness => "liveness",
            ObligationKind::ArithmeticSafety => "arithmetic_safety",
            ObligationKind::BoundsCheck => "bounds_check",
            ObligationKind::GiveBackRefinement => "give_back_refinement",
            ObligationKind::Termination => "termination",
            ObligationKind::Ownership => "ownership",
            ObligationKind::Custom { namespace, name } => {
                self.text("custom:", out)?;
                self.text(namespace, out)?;
                self.text("/", out)?;
                return self.text(name, out);
            }
            // An external future kind has no audited diagnostic spelling.
            _ => return Err(ObservedValueError::UnsupportedValue),
        };
        self.text(text, out)
    }
}
