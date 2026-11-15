// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Exact primitive dependency-DAG construction, never scope authority.
//! Ordered edges retain the original left-first guard prefix. Arena nodes own
//! their backward child IDs; rollback removes unpublished canonical entries.

use super::*;

impl Closer<'_> {
    pub(super) fn intern_dependency_node(&mut self, dependency: Dependency) -> usize {
        if let Some(index) = self.dependency_nodes.get(&dependency).copied()
            && self
                .dependencies
                .get(index)
                .is_some_and(|node| node.dependency == dependency)
        {
            self.observe_dependency_node_intern(true);
            self.refresh_named_prefix(index);
            return index;
        }
        self.observe_dependency_node_intern(false);
        let index = self.dependency_node(dependency);
        self.dependency_nodes.insert(dependency, index);
        index
    }

    pub(super) fn truncate_dependencies(&mut self, checkpoint: usize) {
        // One constant-time removal per previously appended node, not a graph
        // search. Every construction was bounded by its charged source/probe.
        for (offset, node) in self.dependencies[checkpoint..].iter().enumerate() {
            if self.dependency_nodes.get(&node.dependency) == Some(&(checkpoint + offset)) {
                self.dependency_nodes.remove(&node.dependency);
            }
        }
        self.dependencies.truncate(checkpoint);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_values_ordered_joins_and_rollback_keep_one_live_canonical_node() {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let a = closer.intern_dependency_node(Dependency::Named(FVarId::new(1), 0));
        let b = closer.intern_dependency_node(Dependency::Named(FVarId::new(2), 0));
        assert_ne!(a, b);
        let checkpoint = closer.dependencies.len();
        let ab = closer.union_dependencies(a, b);
        assert_eq!(closer.union_dependencies(a, b), ab);
        let ba = closer.union_dependencies(b, a);
        assert_ne!(ab, ba, "ordered first-read prefix remains distinct");
        assert_eq!(closer.dependencies.len(), checkpoint + 2);
        let changed_depth = closer.intern_dependency_node(Dependency::Named(FVarId::new(1), 1));
        assert_ne!(changed_depth, a);
        let ordinary = closer.intern_dependency_node(Dependency::Ordinary(0, 0));
        assert_ne!(ordinary, a);
        closer.truncate_dependencies(checkpoint);
        assert_eq!(closer.dependency_nodes.len(), checkpoint);
        let recycled = closer.dependency_node(Dependency::Ordinary(3, 3));
        assert_eq!(recycled, ab);
        let actual = closer.union_dependencies(a, b);
        assert_ne!(actual, recycled);
        assert!(
            matches!(closer.dependencies[actual].dependency, Dependency::Join(left, right) if left == a && right == b)
        );
        // A raw private-fixture rollback can leave a stale hint; exact live
        // bounds AND value checks still prevent a recycled-index admission.
        closer.dependencies.truncate(actual);
        let recycled = closer.dependency_node(Dependency::Ordinary(4, 4));
        assert_eq!(actual, recycled);
        let actual = closer.union_dependencies(a, b);
        assert_ne!(actual, recycled);
        assert_eq!(closer.stats, TermScopeStats::default());
        assert!(closer.diagnostic_report().cache.dependency_node_intern_hits > 0);
        for (index, node) in closer.dependencies.iter().enumerate() {
            if let Dependency::Join(left, right) = node.dependency {
                assert!(left < index && right < index);
            }
        }
    }
}
