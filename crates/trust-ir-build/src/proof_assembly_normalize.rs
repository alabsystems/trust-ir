// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact, success-only normalization sharing within one proof producer.
//!
//! Deferred binder meanings belong to (scope, binder kind, body Arc), not just
//! structural Expr equality. Keys retain the complete input and compare every
//! immediate child identity before ordinary kind/scalar equality. The cached
//! hash is only an index; collisions never authorize reuse. No borrowed root
//! address survives a call, and owned Expr/capture snapshots pin all children.
//! The owner token is weak: no entry retains the entire deferred scope registry.
//!
//! A successful LocalScope close contains no FVars. Subsequent scope growth can
//! only add fresh retained binder bodies and registered IDs: it cannot change
//! a pinned old body or introduce an uncaptured FVar into that prior success.
//! Capture types/terms and scope closing limits are immutable. Failures are
//! never stored, so no failed traversal is bypassed by this argument.

use crate::scoped_local::{LocalScopeOwner, ScopedLocal};
use clean_kernel::{
    Expr, ExprKind,
    expr::{FVarId, ZFCSetExpr},
};
use std::{
    collections::{HashMap, HashSet, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
    sync::Arc,
};

#[cfg(test)]
#[path = "proof_assembly_normalize_tests.rs"]
mod tests;

struct Entry {
    owner: LocalScopeOwner,
    captures: Vec<Capture>,
    input: Expr,
    output: Expr,
}

/// Retain exactly the immutable capture input, not its Rc-owned allocator.
struct Capture {
    id: FVarId,
    ty: Expr,
    term: Expr,
}

#[derive(Default)]
pub(super) struct NormalizeMemo {
    buckets: HashMap<u64, Vec<Entry>>,
    /// Aggregate entry/capture handles plus reachable Expr DAG nodes. Shared
    /// nodes across entries are conservatively charged again. This is NOT an
    /// exact byte cap for variable-size scalar payloads or replay resources.
    retained: usize,
}

impl NormalizeMemo {
    pub(super) fn get<'a>(
        &self,
        key: u64,
        owner: &LocalScopeOwner,
        captures: impl ExactSizeIterator<Item = &'a ScopedLocal> + Clone,
        input: &Expr,
    ) -> Option<Expr> {
        self.buckets.get(&key)?.iter().find_map(|entry| {
            (entry.owner.matches(owner)
                && entry.captures.len() == captures.len()
                && entry.captures.iter().zip(captures.clone()).all(|(a, b)| {
                    a.id == b.id() && same_graph(&a.ty, b.ty()) && same_graph(&a.term, b.term())
                })
                && same_graph(&entry.input, input))
            .then(|| entry.output.clone())
        })
    }

    pub(super) fn insert<'a>(
        &mut self,
        key: u64,
        owner: LocalScopeOwner,
        captures: impl ExactSizeIterator<Item = &'a ScopedLocal> + Clone,
        input: &Expr,
        output: &Expr,
        budget: usize,
    ) {
        let Some(weight) = retained_weight(captures.clone(), input, output, budget) else {
            return;
        };
        if self.retained > budget - weight {
            // Eviction changes only reuse, never producer admission or limits.
            // No new public policy knob or unbounded per-root cache is added.
            self.buckets.clear();
            self.retained = 0;
        }
        self.buckets.entry(key).or_default().push(Entry {
            owner,
            captures: captures
                .map(|local| Capture {
                    id: local.id(),
                    ty: local.ty().clone(),
                    term: local.term().clone(),
                })
                .collect(),
            input: input.clone(),
            output: output.clone(),
        });
        self.retained += weight;
    }
}

/// Count exactly the graphs an entry would retain, iteratively and with an
/// early stop. The existing capture budget bounds both census work/storage and
/// aggregate cache retention. Exceeding it only declines memoization; the
/// successful normalized result is still returned to the ordinary caller.
fn retained_weight<'a>(
    captures: impl ExactSizeIterator<Item = &'a ScopedLocal>,
    input: &Expr,
    output: &Expr,
    budget: usize,
) -> Option<usize> {
    // An entry owns two root Expr copies; each capture owns two more. Count
    // these copies even when supplied root references alias one another. Only
    // the reachable Arc allocations below those copies are deduplicated.
    let mut weight = captures.len().checked_mul(3)?.checked_add(3)?;
    if weight > budget {
        return None;
    }
    let mut seen = HashSet::new();
    fn account(
        root: &Expr,
        seen: &mut HashSet<usize>,
        weight: &mut usize,
        budget: usize,
    ) -> Option<()> {
        let mut stack: Vec<_> = children(root).into_iter().flatten().collect();
        while let Some(expr) = stack.pop() {
            let address = Arc::as_ptr(expr) as usize;
            if seen.contains(&address) {
                continue;
            }
            if *weight == budget {
                return None;
            }
            seen.insert(address);
            *weight += 1;
            stack.extend(children(expr).into_iter().flatten());
        }
        Some(())
    }
    account(input, &mut seen, &mut weight, budget)?;
    account(output, &mut seen, &mut weight, budget)?;
    for capture in captures {
        account(capture.ty(), &mut seen, &mut weight, budget)?;
        account(capture.term(), &mut seen, &mut weight, budget)?;
    }
    Some(weight)
}

pub(super) fn key_hash<'a>(
    owner: &LocalScopeOwner,
    captures: impl ExactSizeIterator<Item = &'a ScopedLocal>,
    input: &Expr,
) -> u64 {
    let mut hash = DefaultHasher::new();
    owner.address().hash(&mut hash);
    captures.len().hash(&mut hash);
    for local in captures {
        local.id().hash(&mut hash);
        hash_graph(local.ty(), &mut hash);
        hash_graph(local.term(), &mut hash);
    }
    hash_graph(input, &mut hash);
    hash.finish()
}

pub(crate) fn hash_graph(expr: &Expr, hash: &mut impl Hasher) {
    expr.hash_cached().hash(hash);
    std::mem::discriminant(expr.kind()).hash(hash);
    child_ids(expr).hash(hash);
}

pub(crate) fn same_graph(a: &Expr, b: &Expr) -> bool {
    // Expr equality alone can conflate structurally equal ordinary/named
    // binders. Equal immediate Arc identities pin the entire immutable child
    // graph first; equality then checks all scalar fields (including metadata,
    // names, levels, binder annotations, and ZFC constructor tags).
    child_ids(a) == child_ids(b) && a == b
}

fn child_ids(expr: &Expr) -> [usize; 4] {
    children(expr).map(|child| child.map_or(0, |arc| Arc::as_ptr(arc) as usize))
}

/// Every current Expr/ZFC constructor is explicit. A future child-bearing
/// variant must update this match; a wildcard must not silently omit its Arc.
/// Four is the maximum current immediate arity, not an expression-size cap.
fn children(expr: &Expr) -> [Option<&Arc<Expr>>; 4] {
    match expr.kind() {
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(..)
        | ExprKind::Lit(_)
        | ExprKind::SProp
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1 => [None; 4],
        ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
            [Some(a), Some(b), None, None]
        }
        ExprKind::Let(_, a, b, c, _) => [Some(a), Some(b), Some(c), None],
        ExprKind::Proj(_, _, a) | ExprKind::MData(_, a) | ExprKind::Squash(a) => {
            [Some(a), None, None, None]
        }
        ExprKind::CubicalPath { ty, left, right } => [Some(ty), Some(left), Some(right), None],
        ExprKind::CubicalPathLam { body } => [Some(body), None, None, None],
        ExprKind::CubicalPathApp { path, arg } => [Some(path), Some(arg), None, None],
        ExprKind::CubicalHComp { ty, phi, u, base } => [Some(ty), Some(phi), Some(u), Some(base)],
        ExprKind::CubicalTransp { ty, phi, base } => [Some(ty), Some(phi), Some(base), None],
        ExprKind::CubicalCoe { ty, r, s, base } => [Some(ty), Some(r), Some(s), Some(base)],
        ExprKind::ZFCSet(set) => match set {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => [None; 4],
            ZFCSetExpr::Singleton(a)
            | ZFCSetExpr::Union(a)
            | ZFCSetExpr::PowerSet(a)
            | ZFCSetExpr::Choice(a) => [Some(a), None, None, None],
            ZFCSetExpr::Pair(a, b) => [Some(a), Some(b), None, None],
            ZFCSetExpr::Separation { set, pred } => [Some(set), Some(pred), None, None],
            ZFCSetExpr::Replacement { set, func } => [Some(set), Some(func), None, None],
        },
        ExprKind::ZFCMem { element, set } => [Some(element), Some(set), None, None],
        ExprKind::ZFCComprehension { domain, pred } => [Some(domain), Some(pred), None, None],
    }
}
