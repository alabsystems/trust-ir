// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete, untrusted ordinary-term export; never select or replay support.

use super::ScopedProofComponentBundle;
use crate::term_scope::{TermScope, TermScopeLimits, TermScopeStats};
use clean_kernel::Expr;
use std::collections::HashSet;

/// Structural export work, with construction and closure sharing one allowance.
#[derive(Clone, Copy, Debug)]
pub struct ScopedProofExportWork {
    pub declarations: usize,
    /// One identity check and two telescope constructors per declaration.
    pub construction_visits: usize,
    pub closing: TermScopeStats,
}

/// Ordinary closed syntax containing every original declaration type and value.
/// Neither the root nor its proposed goal has been typechecked or certified.
pub struct ClosedScopedProofTerms {
    pub root: Expr,
    pub goal: Expr,
    pub work: ScopedProofExportWork,
}

impl ScopedProofComponentBundle {
    /// Export the complete mixed telescope as ordinary lambdas, Pis and lets.
    ///
    /// All definitions, including unused ones, occur in both returned terms.
    /// Identities must be unique, nonreserved and used only in their preceding
    /// prefixes; unknown locals and loose ordinary bound variables are refused.
    /// Internal declarations remain definitions, rather than new hypotheses.
    /// One caller-owned visit allowance covers validation, construction and the
    /// complete two-root closing walk. Producer counters grant no allowance.
    ///
    /// This constructs syntax only. Consumers must independently reconstruct
    /// the required claim and check every retained type and value in the kernel.
    pub fn into_closed_terms(
        self,
        limits: TermScopeLimits,
    ) -> Result<ClosedScopedProofTerms, String> {
        if self.outer_count > self.declarations.len() {
            return Err("missing original scoped telescope".into());
        }
        let construction_visits = self
            .declarations
            .len()
            .checked_mul(3)
            .filter(|&work| work <= limits.max_visits)
            .ok_or("complete scoped export construction visit limit")?;
        if self.declarations.len() > limits.max_depth as usize {
            return Err("complete scoped export telescope depth limit".into());
        }
        let mut ids = HashSet::new();
        for (index, declaration) in self.declarations.iter().enumerate() {
            if declaration.id.as_u64() >= (1u64 << 63) || !ids.insert(declaration.id) {
                return Err("duplicate or reserved scoped identity".into());
            }
            if index >= self.outer_count && declaration.value.is_none() {
                return Err("complete scoped export has an internal assumption".into());
            }
        }
        let mut scope = TermScope::new();
        let mut root = self.root;
        let mut goal = self.goal;
        for declaration in self.declarations.iter().rev() {
            if let Some(value) = &declaration.value {
                root = scope.let_named(
                    declaration.id,
                    declaration.name.clone(),
                    declaration.type_.clone(),
                    value.clone(),
                    root,
                    declaration.non_dep,
                );
                goal = scope.let_named(
                    declaration.id,
                    declaration.name.clone(),
                    declaration.type_.clone(),
                    value.clone(),
                    goal,
                    declaration.non_dep,
                );
            } else {
                root = scope.lam(
                    declaration.id,
                    declaration.binder,
                    declaration.type_.clone(),
                    root,
                );
                goal = scope.pi(
                    declaration.id,
                    declaration.binder,
                    declaration.type_.clone(),
                    goal,
                );
            }
        }
        let (closed, closing) = scope.close_external_forest_fully(
            &[root, goal],
            &[],
            &[0, 0],
            TermScopeLimits {
                max_visits: limits.max_visits - construction_visits,
                ..limits
            },
        );
        let mut closed = closed.map_err(|error| error.to_string())?.into_iter();
        let root = closed.next().ok_or("missing complete exported root")?;
        let goal = closed.next().ok_or("missing complete exported goal")?;
        if root.has_loose_bvars_quick() || goal.has_loose_bvars_quick() {
            return Err("complete scoped export has loose bound variables".into());
        }
        Ok(ClosedScopedProofTerms {
            root,
            goal,
            work: ScopedProofExportWork {
                declarations: self.declarations.len(),
                construction_visits,
                closing,
            },
        })
    }
}

#[cfg(test)]
#[path = "proof_components_complete_export_tests.rs"]
mod tests;
