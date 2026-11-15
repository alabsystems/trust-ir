// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Observations only: cached hashes neither prove equality nor authorize reuse.

use super::{BinderKind, TermScope};
use clean_kernel::{Expr, ExprKind};
use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

/// First-seen input addresses of one expression kind in the observed prefix.
/// Named/ordinary lambda, Pi and let rows use this scope's binder registry,
/// not expression hashes. Kind names are diagnostic labels, not a wire format.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TermScopeInputKindCounts {
    pub kind: &'static str,
    pub distinct_input_nodes: usize,
    /// Distinct cached 32-bit hashes, NOT distinct structural expressions.
    /// Collisions and deferred binder identities prevent equality/reuse claims.
    pub distinct_cached_hashes: usize,
}

#[derive(Default)]
pub(super) struct InputCensus {
    nodes: HashSet<usize>,
    // At most one address and one hash entry per charged, first-seen input.
    // No Expr or scope is retained, and no second graph traversal is performed.
    kinds: BTreeMap<&'static str, (usize, HashSet<u32>)>,
}

impl InputCensus {
    pub(super) fn observe(&mut self, scope: &TermScope, expression: &Expr) {
        if !self.nodes.insert(expression as *const Expr as usize) {
            return;
        }
        let entry = self.kinds.entry(kind(scope, expression)).or_default();
        entry.0 += 1;
        entry.1.insert(expression.hash_cached());
    }

    pub(super) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(super) fn counts(&self) -> Vec<TermScopeInputKindCounts> {
        self.kinds
            .iter()
            .map(|(&kind, (nodes, hashes))| TermScopeInputKindCounts {
                kind,
                distinct_input_nodes: *nodes,
                distinct_cached_hashes: hashes.len(),
            })
            .collect()
    }
}

fn kind(scope: &TermScope, expression: &Expr) -> &'static str {
    let named = |kind, body: &Arc<Expr>| {
        scope
            .bindings
            .contains_key(&(kind, Arc::as_ptr(body) as usize))
    };
    // Exhaustive: a new ExprKind must receive an explicit diagnostic label.
    // No child or application-head walk is hidden in classification.
    match expression.kind() {
        ExprKind::BVar(_) => "BVar",
        ExprKind::FVar(_) => "FVar",
        ExprKind::Sort(_) => "Sort",
        ExprKind::Const(..) => "Const",
        ExprKind::App(..) => "App",
        ExprKind::Lam(_, _, body) => {
            if named(BinderKind::Lambda, body) {
                "Lam.named"
            } else {
                "Lam.ordinary"
            }
        }
        ExprKind::Pi(_, _, body) => {
            if named(BinderKind::Pi, body) {
                "Pi.named"
            } else {
                "Pi.ordinary"
            }
        }
        ExprKind::Let(_, _, _, body, _) => {
            if named(BinderKind::Let, body) {
                "Let.named"
            } else {
                "Let.ordinary"
            }
        }
        ExprKind::Lit(_) => "Lit",
        ExprKind::Proj(..) => "Proj",
        ExprKind::MData(..) => "MData",
        ExprKind::SProp => "SProp",
        ExprKind::Squash(_) => "Squash",
        ExprKind::CubicalInterval => "CubicalInterval",
        ExprKind::CubicalI0 => "CubicalI0",
        ExprKind::CubicalI1 => "CubicalI1",
        ExprKind::CubicalPath { .. } => "CubicalPath",
        ExprKind::CubicalPathLam { .. } => "CubicalPathLam",
        ExprKind::CubicalPathApp { .. } => "CubicalPathApp",
        ExprKind::CubicalHComp { .. } => "CubicalHComp",
        ExprKind::CubicalTransp { .. } => "CubicalTransp",
        ExprKind::CubicalCoe { .. } => "CubicalCoe",
        ExprKind::ZFCSet(_) => "ZFCSet",
        ExprKind::ZFCMem { .. } => "ZFCMem",
        ExprKind::ZFCComprehension { .. } => "ZFCComprehension",
    }
}
