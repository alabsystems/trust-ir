// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One DAG transport for every part of a scoped proof. The named applications
//! below are inert record tags, never declarations or kernel proof premises.

use super::{ScopedProofComponentBundle, ScopedProofDeclaration};
use clean_kernel::{Expr, ExprKind, Name};

const ROOT_TAG: &str = "TrustIR.ScopedProof.v1";
const DECLARATIONS_TAG: &str = "TrustIR.ScopedProof.declarations.v1";
const MAX_DECLARATIONS: usize = 262_144;

fn tagged(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![]), arguments)
}
fn has_tag(expression: &Expr, tag: &str) -> bool {
    matches!(expression.get_app_fn().kind(), ExprKind::Const(name, levels) if *name == Name::from_string(tag) && levels.is_empty())
}

impl ScopedProofComponentBundle {
    /// Encode the complete untrusted artifact and its frozen external claim in
    /// ONE bounded DAG, retaining sharing between declarations and the root.
    pub fn encode_with_claim(&self, claim: &Expr) -> Result<Vec<u8>, String> {
        if self.outer_count > self.declarations.len() || self.declarations.len() > MAX_DECLARATIONS
        {
            return Err("invalid scoped proof declaration count".into());
        }
        let records = self.declarations.iter().map(|declaration| {
            let id = Expr::fvar(declaration.id);
            match &declaration.value {
                Some(value) => Expr::let_named(
                    declaration.name.clone(),
                    declaration.type_.clone(),
                    value.clone(),
                    id,
                    declaration.non_dep,
                ),
                None => Expr::lam(declaration.binder, declaration.type_.clone(), id),
            }
        });
        let envelope = tagged(
            ROOT_TAG,
            [
                Expr::nat_lit(self.outer_count as u64),
                tagged(DECLARATIONS_TAG, records),
                claim.clone(),
                self.goal.clone(),
                self.root.clone(),
            ],
        );
        trust_ir::proof::encode_clean_expr_dag_v2(&envelope)
    }

    /// Decode data only. No declaration or judgment is trusted until replay.
    /// Build-time work observations are deliberately not transport authority.
    pub fn decode_with_claim(bytes: &[u8]) -> Result<(Self, Expr), String> {
        let envelope = trust_ir::proof::decode_clean_expr_dag_v2(bytes)?;
        if !has_tag(&envelope, ROOT_TAG) || envelope.get_app_num_args() != 5 {
            return Err("invalid scoped proof envelope".into());
        }
        let fields = envelope.get_app_args();
        let outer_count = match fields[0].kind() {
            ExprKind::Lit(clean_kernel::expr::Literal::Nat(value)) => {
                value.to_u64().and_then(|value| usize::try_from(value).ok())
            }
            _ => None,
        }
        .ok_or("invalid scoped proof outer telescope count")?;
        let records = fields[1];
        if !has_tag(records, DECLARATIONS_TAG) || records.get_app_num_args() > MAX_DECLARATIONS {
            return Err("invalid scoped proof declarations".into());
        }
        let mut declarations = Vec::with_capacity(records.get_app_num_args());
        for record in records.get_app_args() {
            let (name, binder, non_dep, type_, value, id) = match record.kind() {
                ExprKind::Lam(binder, ty, id) => {
                    (Name::anon(), *binder, false, ty.as_ref().clone(), None, id)
                }
                ExprKind::Let(name, ty, value, id, non_dep) => (
                    name.clone(),
                    clean_kernel::expr::BinderInfo::Default.into(),
                    *non_dep,
                    ty.as_ref().clone(),
                    Some(value.as_ref().clone()),
                    id,
                ),
                _ => return Err("invalid scoped proof declaration record".into()),
            };
            let ExprKind::FVar(id) = id.kind() else {
                return Err("invalid scoped proof declaration identity".into());
            };
            declarations.push(ScopedProofDeclaration {
                id: *id,
                name,
                binder,
                non_dep,
                type_,
                value,
            });
        }
        if outer_count > declarations.len() {
            return Err("missing original scoped telescope".into());
        }
        Ok((
            Self {
                declarations,
                outer_count,
                root: (*fields[4]).clone(),
                goal: (*fields[3]).clone(),
                work: None,
            },
            (*fields[2]).clone(),
        ))
    }
}
