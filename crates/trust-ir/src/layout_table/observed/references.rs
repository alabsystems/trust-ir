// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::layout_table::references::{self, Key};

impl<O: ExecutionObserver> references::Work for Work<'_, '_, O> {
    type Error = Error;
    fn poll(&mut self) -> R {
        Work::poll(self)
    }
    fn push<'a>(&mut self, pending: &mut Vec<&'a Ty>, ty: &'a Ty) -> R {
        Work::push(self, pending, ty)
    }
    fn mark(&mut self, seen: &mut BTreeSet<Key>, key: Key) -> R<bool> {
        self.lookup(seen.len())?;
        if seen.contains(&key) {
            return Ok(false);
        }
        self.tree::<Key, ()>(seen.len())?;
        seen.insert(key);
        Ok(true)
    }
    fn function_item(&mut self, module: &Module, id: crate::FuncId) -> R<bool> {
        self.function_item_valid(module, id)
    }
    fn retire(&mut self, pending: Vec<&Ty>, seen: BTreeSet<Key>) {
        self.retire_copy_vec(pending);
        self.retire_set(seen);
    }
}
