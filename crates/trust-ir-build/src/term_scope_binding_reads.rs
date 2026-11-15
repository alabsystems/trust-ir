// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! One lazy read leaf per LIVE named binding, never scope or cache authority.

use super::*;

struct NamedRead {
    depth: u32,
    leaf: Option<NonZeroUsize>,
}

#[derive(Default)]
pub(super) struct NamedReads {
    bindings: HashMap<FVarId, NamedRead>,
    // Only tracked binder entry/exit and between-root external admission
    // preserve a lexical-prefix proof.
    untracked_mutation: bool,
}

impl NamedReads {
    pub(super) fn get(&self, id: &FVarId) -> Option<&u32> {
        self.bindings.get(id).map(|binding| &binding.depth)
    }
    pub(super) fn contains_key(&self, id: &FVarId) -> bool {
        self.bindings.contains_key(id)
    }
    pub(super) fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
    pub(super) fn insert(&mut self, id: FVarId, depth: u32) -> Option<u32> {
        self.untracked_mutation = true;
        self.bindings
            .insert(id, NamedRead { depth, leaf: None })
            .map(|old| old.depth)
    }
    pub(super) fn remove(&mut self, id: &FVarId) -> Option<u32> {
        self.untracked_mutation = true;
        self.bindings.remove(id).map(|old| old.depth)
    }
    pub(super) fn insert_scoped(&mut self, id: FVarId, depth: u32) -> Option<u32> {
        let untracked = self.untracked_mutation;
        let result = self.insert(id, depth);
        self.untracked_mutation = untracked;
        result
    }
    pub(super) fn remove_scoped(&mut self, id: &FVarId) -> Option<u32> {
        let untracked = self.untracked_mutation;
        let result = self.remove(id);
        self.untracked_mutation = untracked;
        result
    }
    pub(super) fn stack_consistent(&self) -> bool {
        !self.untracked_mutation
    }
    #[cfg(test)]
    pub(super) fn clear(&mut self) {
        self.untracked_mutation = true;
        self.bindings.clear();
    }
}

#[cfg(test)]
impl Extend<(FVarId, u32)> for NamedReads {
    fn extend<T: IntoIterator<Item = (FVarId, u32)>>(&mut self, bindings: T) {
        for (id, depth) in bindings {
            let _ = self.insert(id, depth);
        }
    }
}

impl Closer<'_> {
    /// Called only after the actual binding/depth check, never instead of it.
    pub(super) fn named_read_dependency(&mut self, id: FVarId, depth: u32) -> usize {
        let binding = self
            .active
            .bindings
            .get(&id)
            .expect("read lacks its live named binding");
        assert_eq!(binding.depth, depth, "read lacks its live named binding");
        let expected = Dependency::Named(id, depth);
        let cached = binding.leaf.map(|handle| handle.get() - 1);
        if let Some(index) = cached
            && self
                .dependencies
                .get(index)
                .is_some_and(|node| node.dependency == expected)
        {
            self.refresh_named_prefix(index);
            return index;
        }
        // A failed private rebase can truncate/recycle an arena suffix. A stale
        // handle is only a hint: exact bounds AND read value are checked above.
        let index = self.intern_dependency_node(expected);
        self.active.bindings.get_mut(&id).unwrap().leaf = MemoEntry::compact(Some(index));
        index
    }
}
