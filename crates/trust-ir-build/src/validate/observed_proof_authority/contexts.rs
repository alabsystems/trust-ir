// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn contexts<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<trust_ir::ObservedDropGlueIndex<'_>>())?;
        let glue = a.module.drop_glue_index_observed(w.session, w.site)?;
        let result = self.context_functions(a, &glue, w);
        w.step(size_of::<trust_ir::ObservedDropGlueIndex<'_>>().saturating_add(1));
        drop(glue);
        w.poll();
        result.and_then(|()| w.admit(1, 0))
    }
    fn context_functions<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        glue: &trust_ir::ObservedDropGlueIndex<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = w.at(&a.module.functions, f)? {
            let mut b = 0;
            while let Some(block) = w.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = w.at(&block.body, n)? {
                    w.admit(1, size_of::<Option<&trust_ir::proof::ProofContext>>())?;
                    if let Some(context) = &node.proof_context {
                        self.context_node(a, glue, block.id.index(), node, context, w)?;
                    }
                    w.next(&mut n)?;
                }
                w.next(&mut b)?;
            }
            w.next(&mut f)?;
        }
        Ok(())
    }
    fn context_node<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        glue: &trust_ir::ObservedDropGlueIndex<'_>,
        block: u32,
        node: &trust_ir::InstrNode,
        pc: &trust_ir::proof::ProofContext,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(64, size_of::<Option<FuncId>>())?;
        let glue = match &node.inst {
            Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => match glue
                .resolve(ty, w.session, w.site)?
            {
                trust_ir::DropResolution::Resolved(f) => Some(f),
                trust_ir::DropResolution::Unresolved | trust_ir::DropResolution::Ambiguous => None,
            },
            _ => None,
        };
        if !matches!(
            node.inst,
            Inst::Call { .. }
                | Inst::CallCannotUnwind { .. }
                | Inst::CallIndirect { .. }
                | Inst::CallIndirectCannotUnwind { .. }
                | Inst::Invoke { .. }
                | Inst::InvokeIndirect { .. }
        ) && glue.is_none()
        {
            fixed_error!(
                self,
                w,
                ValidationError::ProofContextOnNonCallNode { block }
            )?;
        }
        for ids in [&pc.assumes, &pc.establishes] {
            let mut at = 0;
            while let Some(id) = w.at(ids, at)? {
                if lookup::last(a.module, *id, w)?.is_none() {
                    fixed_error!(
                        self,
                        w,
                        ValidationError::ProofContextUnknownObligation {
                            block,
                            obligation: id.index(),
                        }
                    )?;
                }
                w.next(&mut at)?;
            }
        }
        let mut at = 0;
        while let Some(id) = w.at(&pc.assumes, at)? {
            if lookup::last(a.module, *id, w)?.is_some()
                && !self.grounds(a, *id, Currency::Kernel, w)?
            {
                fixed_error!(
                    self,
                    w,
                    ValidationError::ProofContextAssumeNotAuthoritative {
                        block,
                        obligation: id.index(),
                    }
                )?;
            }
            w.next(&mut at)?;
        }
        w.admit(32, size_of::<Option<FuncId>>())?;
        let callee = match &node.inst {
            Inst::Call { callee, .. }
            | Inst::CallCannotUnwind { callee, .. }
            | Inst::Invoke { callee, .. } => Some(*callee),
            _ => glue,
        };
        if let Some(callee) = callee {
            self.context_scopes(a.module, block, callee, pc, w)?;
        }
        Ok(())
    }
    fn context_scopes<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        block: u32,
        callee: FuncId,
        pc: &trust_ir::proof::ProofContext,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        for (ids, assume) in [(&pc.assumes, true), (&pc.establishes, false)] {
            let mut at = 0;
            while let Some(id) = w.at(ids, at)? {
                if let Some(owner) = lookup::owner(module, *id, w)? {
                    w.admit(1, size_of::<bool>())?;
                    if owner != callee {
                        fixed_error!(
                            self,
                            w,
                            if assume {
                                ValidationError::ProofContextAssumeScopeMismatch {
                                    block,
                                    obligation: id.index(),
                                    callee: callee.index(),
                                    actual_owner: owner.index(),
                                }
                            } else {
                                ValidationError::ProofContextEstablishScopeMismatch {
                                    block,
                                    obligation: id.index(),
                                    callee: callee.index(),
                                    actual_owner: owner.index(),
                                }
                            }
                        )?;
                    }
                }
                w.next(&mut at)?;
            }
        }
        Ok(())
    }
}
