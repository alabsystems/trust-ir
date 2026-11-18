// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, Module, PanicStrategy};
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug)]
pub(super) enum ModulePreflight {
    Ready,
    // The complete ABI verdict depends on current options and the supplied body.
    NeedsTypedAbiPreflight,
    InvalidStorage,
}

impl ModulePreflight {
    pub(super) fn inspect(module: &Module) -> Self {
        if module
            .func_types
            .iter()
            .any(|signature| signature.abi.is_some())
        {
            Self::NeedsTypedAbiPreflight
        } else if module.first_storage_violation().is_some() {
            Self::InvalidStorage
        } else {
            Self::Ready
        }
    }
}

/// Successful module-only ABI checks, tied to this exact immutable borrow.
/// Panic strategy is the only execution option read by these checks. Errors
/// are not retained, so each refusal keeps the current entry's diagnostics.
#[derive(Clone, Debug, Default)]
pub(super) struct ModuleAbiPreflights {
    abort: OnceLock<bool>,
    unwind: OnceLock<bool>,
}

impl ModuleAbiPreflights {
    pub(super) fn for_strategy(&self, strategy: PanicStrategy) -> &OnceLock<bool> {
        match strategy {
            PanicStrategy::Abort => &self.abort,
            PanicStrategy::Unwind => &self.unwind,
        }
    }
}

/// Lend interpreters sharing one lazy module-wide execution-policy preflight.
///
/// The immutable module borrow prevents safe mutation for this owner's entire
/// lifetime. Results are private to this exact borrow, never keyed by an address,
/// module name, function ID or global cache. Creating this owner performs no
/// validation or observed-work debit; ordinary execution initializes its policy
/// before executing any body or host callback. This is not full IR validation.
/// Explicit functions outside the module still receive their own body checks.
pub struct InterpreterModule<'module> {
    module: &'module Module,
    preflight: OnceLock<ModulePreflight>,
    storage_preflight: OnceLock<bool>,
    typed_abi_preflights: ModuleAbiPreflights,
}

impl std::fmt::Debug for InterpreterModule<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InterpreterModule")
            .field("module", &self.module.name)
            .field("preflight", &self.preflight.get())
            .field("storage_preflight", &self.storage_preflight.get())
            .finish()
    }
}

impl<'module> InterpreterModule<'module> {
    /// Retain one immutable module; validation stays lazy until execution.
    pub fn new(module: &'module Module) -> Self {
        Self {
            module,
            preflight: OnceLock::new(),
            storage_preflight: OnceLock::new(),
            typed_abi_preflights: ModuleAbiPreflights::default(),
        }
    }

    /// Borrow an interpreter sharing this owner's complete module policy.
    /// Its ordinary options, host model, per-run fuel and memory remain local.
    pub fn interpreter(&self) -> Interpreter<'_> {
        let mut interpreter = Interpreter::with_module(self.module);
        interpreter.module_preflight = Some(&self.preflight);
        interpreter.module_storage_preflight = Some(&self.storage_preflight);
        interpreter.module_typed_abi_preflights = Some(&self.typed_abi_preflights);
        interpreter
    }
}
