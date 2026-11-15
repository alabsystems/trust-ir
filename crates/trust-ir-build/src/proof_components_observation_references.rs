// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! One replay's privately constructed observations. First queries completely
//! scan every input subterm, including arbitrary data embedded by a constructor.
//! No input root, typing premise or scope-closing receipt enters this memo.
use super::*;
use std::cell::RefCell;

pub(crate) struct ObservationReferences {
    component: Arc<()>,
    scope: LocalScopeOwner,
    replay: Arc<()>,
    cache: RefCell<generated_references::Memo>,
}

#[cfg(test)]
#[path = "proof_components_observation_references_tests.rs"]
mod tests;

impl ObservationReferences {
    pub(crate) fn diagnostics(&self) -> String {
        self.cache.borrow().statistics()
    }
}

pub(crate) struct ConstructedObservation {
    replay: Arc<()>,
    root: Expr,
}

impl ProofComponents {
    pub(crate) fn observation_references(
        &mut self,
        scope: &LocalScope,
    ) -> Result<ObservationReferences, String> {
        self.make_observation_references(scope, generated_references::Memo::new, 0)
    }

    /// Fresh CPS observation graphs can choose a complete per-query walk
    /// without probing every child against the retained root inventory.
    /// Whole-root reuse, admission and exact reference checks stay the same.
    #[cfg(test)]
    pub(crate) fn observation_references_root_only(
        &mut self,
        scope: &LocalScope,
    ) -> Result<ObservationReferences, String> {
        self.make_observation_references(scope, generated_references::Memo::root_only, 0)
    }

    /// Retain every possible nested root hit. A singleton immediate child
    /// proves only that an exact retained graph key cannot match this node.
    pub(crate) fn observation_references_shared_children(
        &mut self,
        scope: &LocalScope,
    ) -> Result<ObservationReferences, String> {
        let storage = generated_references::Memo::hash_filter_words(self.limits.operations)
            .checked_add(1)
            .ok_or("observation hash filter storage overflow")?;
        self.make_observation_references(
            scope,
            generated_references::Memo::shared_children_bitmap,
            storage,
        )
    }

    fn make_observation_references(
        &mut self,
        scope: &LocalScope,
        make: fn(usize) -> generated_references::Memo,
        storage: usize,
    ) -> Result<ObservationReferences, String> {
        self.spend_context_work(3)?;
        if !self
            .owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
        {
            return Err("observation references have another component scope owner".into());
        }
        self.spend_context_work(storage)?; // cells/header before allocation or token publication
        let component = self
            .external_context_owner
            .get_or_insert_with(|| Arc::new(()))
            .clone();
        Ok(ObservationReferences {
            component,
            scope: scope.memo_owner(),
            replay: Arc::new(()),
            cache: RefCell::new(make(self.limits.operations)),
        })
    }

    fn owns_observation_references(
        &self,
        scope: &LocalScope,
        memo: &ObservationReferences,
    ) -> bool {
        self.owner
            .as_ref()
            .is_some_and(|owner| owner.matches(&scope.memo_owner()))
            && memo.scope.matches(&scope.memo_owner())
            && self
                .external_context_owner
                .as_ref()
                .is_some_and(|owner| Arc::ptr_eq(owner, &memo.component))
    }

    /// Called only for the actual output of the private ImageNode constructors.
    /// Pinning the immutable root does not establish its references: its first
    /// query still walks the complete graph and every previously unseen child.
    pub(crate) fn constructed_observation(
        &mut self,
        scope: &LocalScope,
        memo: &ObservationReferences,
        root: &Expr,
    ) -> Result<ConstructedObservation, String> {
        self.spend_context_work(7)?; // identity, token/root pins, registered graph/hash inventory
        if !self.owns_observation_references(scope, memo) || memo.cache.borrow().has_failed() {
            return Err("observation references have another owner or a failed scan".into());
        }
        memo.cache.borrow_mut().register(root)?;
        Ok(ConstructedObservation {
            replay: memo.replay.clone(),
            root: root.clone(),
        })
    }

    pub(crate) fn charged_constructed_observation_independent_of(
        &mut self,
        scope: &LocalScope,
        memo: &mut ObservationReferences,
        observation: &ConstructedObservation,
        actual: &Expr,
        forbidden: &[ScopedLocal],
    ) -> Result<(), String> {
        self.spend_context_work(
            forbidden
                .len()
                .checked_mul(4)
                .and_then(|n| n.checked_add(2))
                .ok_or("constructed observation query inventory overflow")?,
        )?;
        if !self.owns_observation_references(scope, memo)
            || !Arc::ptr_eq(&memo.replay, &observation.replay)
            || !same_graph(&observation.root, actual)
            || forbidden.iter().any(|local| !scope.owns(local))
        {
            return Err("constructed observation query has another replay, graph or owner".into());
        }
        if memo.cache.borrow().has_failed() {
            return Err("constructed observation retains a failed scan".into());
        }
        if actual.has_loose_bvars() {
            memo.cache.borrow_mut().poison();
            return Err("first-order data has loose bound variables".into());
        }
        let (scanned, work) = memo
            .cache
            .borrow()
            .scan(actual, self.context_work_remaining()?);
        self.spend_context_work(work)?;
        let result = scanned.and_then(|summary| {
            if forbidden.iter().any(|local| summary.contains(local.id())) {
                Err("first-order data depends on final CPS callbacks".into())
            } else {
                self.spend_context_work(3)?;
                memo.cache.borrow_mut().publish(actual, summary)
            }
        });
        if result.is_err() {
            memo.cache.borrow_mut().poison();
        }
        result
    }
}
