// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Nominal zero-byte function-item references. Resolving a header does not
//! execute its body or authenticate a producer's source-to-function binding.

use crate::{FuncId, FuncTy, FuncTyId, Function, Module, ModuleFunctionCatalog};
use std::collections::BTreeMap;

pub(crate) fn record_function_id<V>(
    entries: &mut BTreeMap<u32, V>,
    id: FuncId,
    unique: V,
    ambiguous: V,
) {
    match entries.entry(id.index()) {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(unique);
        }
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            entry.insert(ambiguous);
        }
    }
}

/// Owned positions keep a lazily cached layout table covariant in its source
/// borrow. The enclosing table holds the immutable actual Module; no caller
/// can supply an index or substitute a different source for that table.
#[derive(Debug)]
pub(crate) struct FunctionItemIndex {
    source_address: usize,
    positions: BTreeMap<u32, Option<usize>>,
}

impl FunctionItemIndex {
    pub(crate) fn new(module: &Module) -> Self {
        let mut positions = BTreeMap::new();
        for (position, function) in module.functions.iter().enumerate() {
            record_function_id(&mut positions, function.id, Some(position), None);
        }
        Self {
            source_address: module as *const Module as usize,
            positions,
        }
    }

    pub(crate) fn function_item<'m>(
        &self,
        module: &'m Module,
        id: FuncId,
    ) -> Result<(&'m Function, &'m FuncTy), FunctionItemError> {
        if self.source_address != module as *const Module as usize {
            return Err(FunctionItemError::MissingOrAmbiguousFunction(id));
        }
        let function = self
            .positions
            .get(&id.index())
            .copied()
            .flatten()
            .and_then(|position| module.functions.get(position))
            .filter(|function| function.id == id)
            .ok_or(FunctionItemError::MissingOrAmbiguousFunction(id))?;
        let signature =
            module
                .func_type(function.ty)
                .ok_or(FunctionItemError::MissingSignature {
                    function: id,
                    signature: function.ty,
                })?;
        Ok((function, signature))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionItemError {
    MissingOrAmbiguousFunction(FuncId),
    MissingSignature {
        function: FuncId,
        signature: FuncTyId,
    },
}

impl core::fmt::Display for FunctionItemError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::MissingOrAmbiguousFunction(id) => {
                write!(f, "missing or ambiguous function item func.{}", id.index())
            }
            Self::MissingSignature {
                function,
                signature,
            } => write!(
                f,
                "function item func.{} has missing signature functy.{}",
                function.index(),
                signature.index()
            ),
        }
    }
}

impl std::error::Error for FunctionItemError {}

impl Module {
    /// Resolve the exact, unique nominal function and its actual signature.
    /// Sparse IDs and bodyless declarations are valid; duplicate IDs never
    /// select an arbitrary first row. No declaration is synthesized.
    pub fn function_item(&self, id: FuncId) -> Result<(&Function, &FuncTy), FunctionItemError> {
        ModuleFunctionCatalog::new(self).function_item(id)
    }
}

impl<'module> ModuleFunctionCatalog<'module> {
    /// Reuse a prepared duplicate-aware catalog for composite operations.
    pub fn function_item(
        &self,
        id: FuncId,
    ) -> Result<(&'module Function, &'module FuncTy), FunctionItemError> {
        let function = self
            .unique(id)
            .ok_or(FunctionItemError::MissingOrAmbiguousFunction(id))?;
        let signature =
            self.module
                .func_type(function.ty)
                .ok_or(FunctionItemError::MissingSignature {
                    function: id,
                    signature: function.ty,
                })?;
        Ok((function, signature))
    }
}
