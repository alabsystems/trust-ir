// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Share newly constructed ordinary core nodes by exact shallow identity.
//! Every child pointer stays live through the retained value. No structural
//! equality walk, deferred-input identity, source rewrite or extra traversal.

use super::*;
use clean_kernel::expr::BinderData;
use std::collections::hash_map::Entry;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum OutputKey {
    BVar(u32),
    App(usize, usize),
    Lam(BinderData, usize, usize),
    Pi(BinderData, usize, usize),
}

impl OutputKey {
    fn of(expression: &Expr) -> Option<Self> {
        let ptr = |child: &Arc<Expr>| Arc::as_ptr(child) as usize;
        match expression.kind() {
            ExprKind::BVar(index) => Some(Self::BVar(*index)),
            ExprKind::App(function, argument) => Some(Self::App(ptr(function), ptr(argument))),
            ExprKind::Lam(binder, ty, body) => Some(Self::Lam(*binder, ptr(ty), ptr(body))),
            ExprKind::Pi(binder, ty, body) => Some(Self::Pi(*binder, ptr(ty), ptr(body))),
            // These other output constructors retain their existing exact
            // representation. Their node-local metadata is not reinterpreted
            // or compared recursively just to enlarge this construction cache.
            _ => None,
        }
    }
}

#[derive(Default)]
pub(super) struct OutputNodes(HashMap<OutputKey, Arc<Expr>>);

impl Closer<'_> {
    /// Called only after the existing visitor completes a newly built output.
    /// This interns neither an unvisited input nor a registered binder body.
    pub(super) fn intern_output_node(&mut self, node: Arc<Expr>) -> Arc<Expr> {
        let Some(key) = OutputKey::of(&node) else {
            return node;
        };
        let (result, reused) = match self.output_nodes.0.entry(key) {
            Entry::Occupied(entry) => (entry.get().clone(), true),
            Entry::Vacant(entry) => (entry.insert(node).clone(), false),
        };
        self.observe_output_node_intern(reused);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::Multiplicity;
    use clean_kernel::{BinderInfo, Expr};

    #[test]
    fn only_exact_complete_shells_share_and_owners_retain_child_addresses() {
        let scope = TermScope::new();
        let mut closer = Closer::new(&scope, TermScopeLimits::default(), true);
        let left = closer.intern_output_node(Arc::new(Expr::bvar(0)));
        let right = closer.intern_output_node(Arc::new(Expr::bvar(1)));
        assert!(!Arc::ptr_eq(&left, &right));
        let same_left = closer.intern_output_node(Arc::new(Expr::bvar(0)));
        assert!(Arc::ptr_eq(&left, &same_left));
        let make = || Arc::new(Expr::app_arc(left.clone(), right.clone()));
        let first = closer.intern_output_node(make());
        let weak = Arc::downgrade(&first);
        drop(first);
        let repeated = closer.intern_output_node(make());
        assert!(Arc::ptr_eq(&weak.upgrade().unwrap(), &repeated));
        let fresh_child = Arc::new(Expr::bvar(0));
        let equal_but_unowned =
            closer.intern_output_node(Arc::new(Expr::app_arc(fresh_child, right.clone())));
        assert_eq!(*equal_but_unowned, *repeated);
        assert!(!Arc::ptr_eq(&equal_but_unowned, &repeated));
        let reversed =
            closer.intern_output_node(Arc::new(Expr::app_arc(right.clone(), left.clone())));
        assert!(!Arc::ptr_eq(&reversed, &repeated));
        let lam = closer.intern_output_node(Arc::new(Expr::lam_arc(
            BinderInfo::Default,
            left.clone(),
            right.clone(),
        )));
        let pi = closer.intern_output_node(Arc::new(Expr::pi_arc(
            BinderInfo::Default,
            left.clone(),
            right.clone(),
        )));
        assert!(!Arc::ptr_eq(&lam, &pi));
        let implicit = closer.intern_output_node(Arc::new(Expr::lam_arc(
            BinderInfo::Implicit,
            left.clone(),
            right.clone(),
        )));
        assert!(!Arc::ptr_eq(&lam, &implicit));
        let linear = closer.intern_output_node(Arc::new(Expr::lam_arc(
            BinderData::new(BinderInfo::Default, Multiplicity::One),
            left,
            right,
        )));
        assert!(!Arc::ptr_eq(&lam, &linear));
        let literal = Arc::new(Expr::const_str("untouched"));
        assert!(Arc::ptr_eq(
            &literal,
            &closer.intern_output_node(literal.clone())
        ));
        assert_eq!(
            closer.stats,
            TermScopeStats::default(),
            "construction adds no visits or refunds"
        );
    }
}
