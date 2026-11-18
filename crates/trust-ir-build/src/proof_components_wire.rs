// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One DAG transport for every part of a scoped proof. The named applications
//! below are inert record tags, never declarations or kernel proof premises.

use super::{ScopedProofComponentBundle, ScopedProofDeclaration};
use clean_kernel::{Expr, ExprKind, Name};

const ROOT_TAG: &str = "TrustIR.ScopedProof.v1";
const DECLARATIONS_TAG: &str = "TrustIR.ScopedProof.declarations.v1";
const MAX_DECLARATIONS: usize = 262_144;
const BALANCED_ROOT_TAG: &str = "TrustIR.ScopedProof.v2";
const BALANCED_DECLARATIONS_TAG: &str = "TrustIR.ScopedProof.declarations.v2";
const LEAF_TAG: &str = "trust_ir.proof.scoped.declarations.leaf.v1";
const BRANCH_TAG: &str = "trust_ir.proof.scoped.declarations.branch.v1";
const DEFINITION_TAG: &str = "trust_ir.proof.scoped.definition.v1";
const PARAMETER_TAG: &str = "trust_ir.proof.scoped.parameter.v1";
const LEAF_RECORDS: usize = 32;

fn tagged(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![]), arguments)
}
fn has_tag(expression: &Expr, tag: &str) -> bool {
    matches!(expression.get_app_fn().kind(), ExprKind::Const(name, levels) if *name == Name::from_string(tag) && levels.is_empty())
}

// These are inert records, not kernel declarations. The inner lambda stores
// every binder attribute and the exact identity. The let stores the original
// name/type/value/non-dependency flag. A parameter has no value: its reserved
// value slot must repeat that same identity. The distinct tag records presence.
fn record(declaration: &ScopedProofDeclaration) -> Expr {
    let id = Expr::fvar(declaration.id);
    tagged(
        if declaration.value.is_some() {
            DEFINITION_TAG
        } else {
            PARAMETER_TAG
        },
        [Expr::let_named(
            declaration.name.clone(),
            declaration.type_.clone(),
            declaration.value.clone().unwrap_or_else(|| id.clone()),
            Expr::lam(declaration.binder, id.clone(), id),
            declaration.non_dep,
        )],
    )
}

fn balanced_records(declarations: &[ScopedProofDeclaration]) -> Expr {
    // MAX_DECLARATIONS bounds this balanced recursion to fourteen levels.
    if declarations.len() <= LEAF_RECORDS {
        tagged(LEAF_TAG, declarations.iter().map(record))
    } else {
        let middle = declarations.len() / 2;
        tagged(
            BRANCH_TAG,
            [
                balanced_records(&declarations[..middle]),
                balanced_records(&declarations[middle..]),
            ],
        )
    }
}

fn natural_count(expression: &Expr) -> Option<usize> {
    match expression.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(value)) => {
            value.to_u64().and_then(|n| usize::try_from(n).ok())
        }
        _ => None,
    }
}

fn balanced_record_refs(root: &Expr) -> Result<Vec<&Expr>, String> {
    if !has_tag(root, BALANCED_DECLARATIONS_TAG) || root.get_app_num_args() != 2 {
        return Err("invalid balanced scoped proof declarations".into());
    }
    let fields = root.get_app_args();
    let count = natural_count(fields[0])
        .filter(|&n| n <= MAX_DECLARATIONS)
        .ok_or("invalid balanced scoped proof declaration count")?;
    let mut records = Vec::with_capacity(count);
    let mut pending = vec![(fields[1], count)];
    while let Some((node, count)) = pending.pop() {
        if count <= LEAF_RECORDS {
            if !has_tag(node, LEAF_TAG) || node.get_app_num_args() != count {
                return Err("invalid balanced scoped proof leaf".into());
            }
            records.extend(node.get_app_args());
        } else {
            if !has_tag(node, BRANCH_TAG) || node.get_app_num_args() != 2 {
                return Err("invalid balanced scoped proof branch".into());
            }
            let children = node.get_app_args();
            let middle = count / 2;
            pending.push((children[1], count - middle));
            pending.push((children[0], middle));
        }
    }
    Ok(records)
}

fn balanced_declaration(record: &Expr) -> Result<ScopedProofDeclaration, String> {
    let definition = has_tag(record, DEFINITION_TAG);
    if (!definition && !has_tag(record, PARAMETER_TAG)) || record.get_app_num_args() != 1 {
        return Err("invalid balanced scoped proof declaration record".into());
    }
    let fields = record.get_app_args();
    let ExprKind::Let(name, ty, value, body, non_dep) = fields[0].kind() else {
        return Err("invalid balanced scoped proof declaration fields".into());
    };
    let ExprKind::Lam(binder, identity_type, identity) = body.kind() else {
        return Err("invalid balanced scoped proof declaration attributes".into());
    };
    let (ExprKind::FVar(type_id), ExprKind::FVar(id)) = (identity_type.kind(), identity.kind())
    else {
        return Err("invalid balanced scoped proof declaration identity".into());
    };
    if type_id != id || (!definition && !matches!(value.kind(), ExprKind::FVar(v) if v == id)) {
        return Err("inconsistent balanced scoped proof declaration identity".into());
    }
    Ok(ScopedProofDeclaration {
        id: *id,
        name: name.clone(),
        binder: *binder,
        non_dep: *non_dep,
        type_: ty.as_ref().clone(),
        value: definition.then(|| value.as_ref().clone()),
    })
}

impl ScopedProofComponentBundle {
    /// Encode the complete untrusted artifact and its frozen external claim in
    /// ONE bounded DAG, retaining sharing between declarations and the root.
    /// The explicitly tagged v2 envelope balances the ordered declaration
    /// sequence; declaration count no longer becomes expression graph depth.
    pub fn encode_with_claim(&self, claim: &Expr) -> Result<Vec<u8>, String> {
        if self.outer_count > self.declarations.len() || self.declarations.len() > MAX_DECLARATIONS
        {
            return Err("invalid scoped proof declaration count".into());
        }
        let envelope = tagged(
            BALANCED_ROOT_TAG,
            [
                Expr::nat_lit(self.outer_count as u64),
                tagged(
                    BALANCED_DECLARATIONS_TAG,
                    [
                        Expr::nat_lit(self.declarations.len() as u64),
                        balanced_records(&self.declarations),
                    ],
                ),
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
        let balanced = has_tag(&envelope, BALANCED_ROOT_TAG);
        if (!balanced && !has_tag(&envelope, ROOT_TAG)) || envelope.get_app_num_args() != 5 {
            return Err("invalid scoped proof envelope".into());
        }
        let fields = envelope.get_app_args();
        let outer_count =
            natural_count(fields[0]).ok_or("invalid scoped proof outer telescope count")?;
        let records = if balanced {
            balanced_record_refs(fields[1])?
        } else {
            if !has_tag(fields[1], DECLARATIONS_TAG)
                || fields[1].get_app_num_args() > MAX_DECLARATIONS
            {
                return Err("invalid scoped proof declarations".into());
            }
            fields[1].get_app_args().to_vec()
        };
        let mut declarations = Vec::with_capacity(records.len());
        for record in records {
            if balanced {
                declarations.push(balanced_declaration(record)?);
                continue;
            }
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

#[cfg(test)]
#[path = "proof_components_wire_tests.rs"]
mod tests;
