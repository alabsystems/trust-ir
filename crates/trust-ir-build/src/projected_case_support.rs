// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0
//! Bounded graph summaries for this replay's immutable normalization context.
//! Bits use the cached structural hash, not allocation identities, and
//! conservatively index closed commutable cases in the exact raw walk used
//! by replacement. A collision only loses a pruning opportunity. These are
//! producer hints; original endpoints and the complete kernel proof still check.
use super::*;
use crate::scoped_local::{LocalScope, LocalScopeOwner};
use std::collections::hash_map::DefaultHasher;

#[derive(Clone, Copy)]
pub(super) struct Summary {
    pub cases: u128,
    /// Search deliberately does not enter Lam/Pi or Let binder bodies.
    pub search_height: usize,
    /// Replacement does enter those bodies. Never reuse search's shorter bound.
    pub replacement_height: usize,
}
#[derive(Default)]
pub(in crate::projected_equality_replay) struct CaseSupportCache {
    nodes: HashMap<Key, Summary>,
    owner: Option<LocalScopeOwner>,
}
impl CaseSupportCache {
    pub(super) fn bits(e: &Expr) -> u128 {
        let mut hash = DefaultHasher::new();
        e.hash(&mut hash);
        let hash = hash.finish();
        (1u128 << (hash & 127)) | (1u128 << ((hash >> 7) & 127))
    }
    pub(super) fn summary(
        &mut self,
        checker: &TypeChecker<'_>,
        scope: &LocalScope,
        e: &Expr,
        work: &mut usize,
        limit: usize,
        remaining_depth: usize,
        max_entries: usize,
        visits: &mut usize,
    ) -> Result<Option<Summary>, &'static str> {
        let owner = scope.memo_owner();
        if self.owner.as_ref().is_some_and(|old| !old.matches(&owner)) {
            return Err("foreign case support cache owner");
        }
        self.owner = Some(owner);
        self.index(
            checker,
            scope,
            e,
            work,
            limit,
            0,
            remaining_depth,
            max_entries,
            visits,
            true,
        )
    }
    fn index(
        &mut self,
        checker: &TypeChecker<'_>,
        scope: &LocalScope,
        e: &Expr,
        work: &mut usize,
        limit: usize,
        depth: usize,
        max_depth: usize,
        max_entries: usize,
        visits: &mut usize,
        root: bool,
    ) -> Result<Option<Summary>, &'static str> {
        if max_entries == 0 {
            return Ok(None);
        }
        if *work >= limit {
            return Err("projected case support aggregate work limit");
        }
        *work += 1;
        *visits += 1;
        // A named binder is not an ordinary closed kernel binder yet.
        // Do not normalize it, or a parent containing it, before its owner
        // materializes it. Previously validated ordinary nodes stay ordinary.
        if scope.named_binder_id(e).is_some() {
            return Ok(None);
        }
        let key = Key(e.clone());
        if let Some(summary) = self.nodes.get(&key).copied() {
            // A root is consumed using its caller's own traversal height.
            // Internal full summaries may not extend an index walk's depth.
            return Ok((root
                || depth
                    .checked_add(summary.replacement_height)
                    .is_some_and(|end| end <= max_depth))
            .then_some(summary));
        }
        if depth > max_depth || self.nodes.len() >= max_entries {
            return Ok(None);
        }
        let mut summary = Summary {
            cases: 0,
            search_height: 0,
            replacement_height: 0,
        };
        // Inspect ordinary binder bodies for replacement's support, even though
        // search leaves them unread. Open nodes cannot match a closed target;
        // their closed descendants can, and must participate in the summary.
        let children: Vec<_> = match e.kind() {
            ExprKind::App(f, a) => vec![(f.as_ref(), true), (a.as_ref(), true)],
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                vec![(ty.as_ref(), false), (body.as_ref(), false)]
            }
            ExprKind::Let(_, ty, value, body, _) => vec![
                (ty.as_ref(), true),
                (value.as_ref(), true),
                (body.as_ref(), false),
            ],
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => vec![(inner.as_ref(), true)],
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(..)
            | ExprKind::Lit(_) => vec![],
            // Unknown expression families retain the original walk. Never infer
            // absence from a node whose child traversal is not described here.
            _ => return Ok(None),
        };
        for (child, searched) in children {
            let Some(child) = self.index(
                checker,
                scope,
                child,
                work,
                limit,
                depth + 1,
                max_depth,
                max_entries,
                visits,
                false,
            )?
            else {
                return Ok(None);
            };
            summary.cases |= child.cases;
            summary.replacement_height =
                summary.replacement_height.max(child.replacement_height + 1);
            if searched {
                summary.search_height = summary.search_height.max(child.search_height + 1);
            }
        }
        if !e.has_loose_bvars() {
            let normalized = checker.whnf(e);
            if checker.heartbeat_spent() {
                return Err("projected case support kernel budget");
            }
            if let Some(found) = case(&normalized, checker) {
                summary.cases |= Self::bits(&found.term);
            }
            if checker.heartbeat_spent() {
                return Err("projected case support kernel budget");
            }
        }
        if self.nodes.len() < max_entries {
            self.nodes.insert(key, summary);
        }
        Ok(Some(summary))
    }
}
