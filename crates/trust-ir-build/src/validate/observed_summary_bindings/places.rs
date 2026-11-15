// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn places<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        summary: &FunctionSummary,
        signature: Option<&FuncTy>,
        role: ContractClauseRole,
        index: usize,
        name: &str,
        binding: &ClauseBinding,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(11, size_of::<Option<u32>>())?;
        let parameter = match binding.place {
            ClausePlace::Param { index } | ClausePlace::ParamPointeeEntry { index } => Some(index),
            ClausePlace::MutParamExit { index: parameter } => {
                if role != ContractClauseRole::Ensures {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(
                        " uses MutParamExit, the give-back / primed-output place, on a ",
                        &mut self.detail,
                    )?;
                    work.text(role.name(), &mut self.detail)?;
                    work.text(
                        " clause; `ClausePlace` makes it legal only on an ensures clause",
                        &mut self.detail,
                    )?;
                    self.issue(function, work)?;
                }
                Some(parameter)
            }
            ClausePlace::ResultSlot { .. }
            | ClausePlace::World
            | ClausePlace::WorldPre
            | ClausePlace::WorldPost
            | ClausePlace::Unwind
            | ClausePlace::Value(_)
            | ClausePlace::SpecVar { .. }
            | ClausePlace::SpecVarNext { .. } => None,
        };
        if let Some(parameter) = parameter {
            work.admit(1, 2 * size_of::<usize>())?;
            match signature {
                Some(ft) if (parameter as usize) < ft.params.len() => {}
                Some(ft) => {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(" names parameter ", &mut self.detail)?;
                    work.number(parameter as u128, &mut self.detail)?;
                    work.text(" but the signature declares ", &mut self.detail)?;
                    work.number(ft.params.len() as u128, &mut self.detail)?;
                    work.text(" parameter(s)", &mut self.detail)?;
                    self.issue(function, work)?;
                }
                None => self.unknown_signature(function, role, index, name, "parameter", work)?,
            }
        }
        work.admit(11, size_of::<ClausePlace>())?;
        match binding.place {
            ClausePlace::Param { .. }
            | ClausePlace::ParamPointeeEntry { .. }
            | ClausePlace::MutParamExit { .. }
            | ClausePlace::WorldPre => {}
            ClausePlace::ResultSlot { index: slot } => {
                work.admit(1, 2 * size_of::<usize>())?;
                match signature {
                    Some(ft) if (slot as usize) < ft.returns.len() => {}
                    Some(ft) => {
                        binding_prefix(role, index, name, &mut self.detail, work)?;
                        work.text(" names result slot ", &mut self.detail)?;
                        work.number(slot as u128, &mut self.detail)?;
                        work.text(" but the signature declares ", &mut self.detail)?;
                        work.number(ft.returns.len() as u128, &mut self.detail)?;
                        work.text(" return value(s)", &mut self.detail)?;
                        self.issue(function, work)?;
                    }
                    None => self.unknown_signature(function, role, index, name, "return", work)?,
                }
            }
            ClausePlace::World => {
                work.admit(1, size_of::<bool>())?;
                if summary.proved {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(" names the legacy un-epoched World on a proved summary; it cannot say whether it is the world before or after the call, so the clause is unbindable — bind WorldPre (entry) or WorldPost (exit) instead",&mut self.detail)?;
                    self.issue(function, work)?;
                }
            }
            ClausePlace::WorldPost => {
                work.admit(1, size_of::<ContractClauseRole>())?;
                if role != ContractClauseRole::Ensures {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(
                        " names WorldPost, the world at exit, on a ",
                        &mut self.detail,
                    )?;
                    work.text(role.name(), &mut self.detail)?;
                    work.text(
                        " clause; `ClausePlace` makes it legal only on an ensures clause",
                        &mut self.detail,
                    )?;
                    self.issue(function, work)?;
                }
            }
            ClausePlace::Unwind => {
                work.admit(1, size_of::<ContractClauseRole>())?;
                if role == ContractClauseRole::Requires {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(" names the in-flight unwind state on a requires clause; `ClausePlace` makes Unwind illegal there — a precondition is evaluated before the call, where no unwind is in flight",&mut self.detail)?;
                    self.issue(function, work)?;
                }
            }
            ClausePlace::Value(value) => {
                work.admit(1, size_of::<bool>())?;
                if function.blocks.is_empty() {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(" names SSA value v", &mut self.detail)?;
                    work.number(value.index() as u128, &mut self.detail)?;
                    work.text(
                        " on a body-less declaration, which has no body to resolve it in",
                        &mut self.detail,
                    )?;
                    self.issue(function, work)?;
                } else if !walk::defined(function, value, work)? {
                    binding_prefix(role, index, name, &mut self.detail, work)?;
                    work.text(" names SSA value v", &mut self.detail)?;
                    work.number(value.index() as u128, &mut self.detail)?;
                    work.text(
                        ", which this function's body never defines",
                        &mut self.detail,
                    )?;
                    self.issue(function, work)?;
                }
            }
            ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. } => {
                binding_prefix(role, index, name, &mut self.detail, work)?;
                work.text(" names ", &mut self.detail)?;
                place_text(binding.place, &mut self.detail, work)?;
                work.text(", a spec-machine state variable; that index space belongs to a SpecModule's `vars` and a function summary has none, so the binding can never be resolved here",&mut self.detail)?;
                self.issue(function, work)?;
            }
        }
        Ok(())
    }
    fn unknown_signature<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        role: ContractClauseRole,
        index: usize,
        name: &str,
        which: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        binding_prefix(role, index, name, &mut self.detail, work)?;
        work.text(" cannot be resolved: functy.", &mut self.detail)?;
        work.number(function.ty.index() as u128, &mut self.detail)?;
        work.text(" is not declared in this module, so the ", &mut self.detail)?;
        work.text(which, &mut self.detail)?;
        work.text(
            " arity it would be checked against is unknown",
            &mut self.detail,
        )?;
        self.issue(function, work)
    }
}
