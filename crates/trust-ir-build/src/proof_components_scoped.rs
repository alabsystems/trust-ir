// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::term_scope::{TermScopeInternStats, TermScopeStats};
use clean_kernel::{Environment, Expr, Name, expr::FVarId};
use std::collections::HashSet;

#[derive(Clone, Copy, Debug)]
pub struct ScopedBuildWork {
    pub preparation: TermScopeInternStats,
    pub closing: TermScopeStats,
}

pub struct ReplayedProofComponents<'a> {
    environment: &'a Environment,
    pub kernel_work: u64,
    pub scope_visits: usize,
    pub scoped_work: clean_kernel::ScopedAuditWork,
}
impl ReplayedProofComponents<'_> {
    pub fn environment(&self) -> &Environment {
        self.environment
    }
}
struct WorkBudget;
impl Drop for WorkBudget {
    fn drop(&mut self) {
        clean_kernel::tc::clear_declaration_budget();
    }
}
/// Portable untrusted telescope entry. Later entries may refer only to earlier
/// identities; replay validates this before checking any defining value.
#[derive(Clone)]
pub struct ScopedProofDeclaration {
    pub id: FVarId,
    pub name: Name,
    pub binder: clean_kernel::expr::BinderData,
    pub non_dep: bool,
    pub type_: Expr,
    pub value: Option<Expr>,
}
#[derive(Clone)]
pub struct ScopedProofComponentBundle {
    pub declarations: Vec<ScopedProofDeclaration>,
    pub outer_count: usize,
    pub root: Expr,
    pub goal: Expr,
    /// Producer measurements; absent after decoding and never proof authority.
    pub work: Option<ScopedBuildWork>,
}
impl ScopedProofComponentBundle {
    pub fn replay<'a>(
        &self,
        environment: &'a Environment,
        external_claim: &Expr,
        kernel_limit: u64,
    ) -> Result<ReplayedProofComponents<'a>, String> {
        if kernel_limit == 0
            || clean_kernel::tc::declaration_budget_limit() != 0
            || clean_kernel::env::mm_axiom_only()
        {
            return Err("scoped replay requires an exclusive strict finite budget".into());
        }
        let mut context = clean_kernel::LocalContext::new();
        let mut ids = HashSet::new();
        for declaration in &self.declarations {
            if declaration.id.as_u64() >= (1u64 << 63) || !ids.insert(declaration.id) {
                return Err("duplicate or reserved scoped identity".into());
            }
            if let Some(value) = &declaration.value {
                context.push_let_with_id(
                    declaration.id,
                    declaration.name.clone(),
                    declaration.type_.clone(),
                    value.clone(),
                );
            } else {
                context.push_with_id(
                    declaration.id,
                    declaration.name.clone(),
                    declaration.type_.clone(),
                    declaration.binder,
                );
            }
        }
        clean_kernel::tc::set_declaration_budget(kernel_limit);
        let _budget = WorkBudget;
        let (audit, scoped_work) = environment.audit_scoped_certification(
            &context,
            self.outer_count,
            external_claim,
            &self.goal,
            &self.root,
            1_000_000,
        );
        let work = clean_kernel::tc::declaration_budget_used();
        let exhausted = clean_kernel::tc::declaration_budget_exhausted();
        if !audit.is_certified() || exhausted {
            // Consumers bound diagnostics. Keep the rejection kind before the
            // potentially large per-declaration work ledger so truncation can
            // never hide a type failure or turn budget exhaustion into one.
            let budget = if exhausted { "BudgetExhausted; " } else { "" };
            return Err(format!(
                "complete scoped replay: {budget}first issue={:?}; kernel work={work}; work={scoped_work:?}; {audit:?}",
                audit.issues.first()
            ));
        }
        for dependency in &audit.dependencies {
            if !environment
                .axiom_deps(dependency)
                .is_some_and(|deps| deps.is_empty())
                || !environment
                    .foundational_axiom_deps(dependency)
                    .is_some_and(|deps| deps.is_empty())
                || !environment
                    .trust_marker_deps(dependency)
                    .is_some_and(|deps| deps.is_empty())
            {
                return Err(format!(
                    "scoped dependency is not axiom/trust-marker free: {dependency}"
                ));
            }
        }
        Ok(ReplayedProofComponents {
            environment,
            kernel_work: work,
            scope_visits: scoped_work.reference_visits,
            scoped_work,
        })
    }
}
