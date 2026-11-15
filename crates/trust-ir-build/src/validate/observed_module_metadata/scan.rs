// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn spans<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<usize>())?;
        let count = module.files.len();
        if count == 0 {
            return Ok(());
        }
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            work.admit(1, size_of::<Option<&[trust_ir::value::ScopeData]>>())?;
            if let Some(scopes) = &function.scopes {
                let mut at = 0;
                while let Some(scope) = work.at(scopes, at)? {
                    work.admit(2, size_of::<Option<trust_ir::value::SourceSpan>>())?;
                    if let Some(span) = &scope.span {
                        self.span(span, count, work)?;
                    }
                    work.admit(1, size_of::<Option<&trust_ir::value::InlinedAt>>())?;
                    if let Some(link) = &scope.inlined_at {
                        self.span(&link.span, count, work)?;
                    }
                    work.next(&mut at)?;
                }
            }
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    work.admit(1, size_of::<Option<trust_ir::value::SourceSpan>>())?;
                    if let Some(span) = &node.span {
                        self.span(span, count, work)?;
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.next(&mut f)?;
        }
        let mut d = 0;
        while let Some(diagnostic) = work.at(&module.obligation_diagnostics, d)? {
            work.admit(1, size_of::<Option<trust_ir::value::SourceSpan>>())?;
            if let Some(span) = &diagnostic.location {
                self.span(span, count, work)?;
            }
            work.next(&mut d)?;
        }
        Ok(())
    }
    fn span<O: ExecutionObserver>(
        &mut self,
        span: &trust_ir::value::SourceSpan,
        count: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, size_of::<u32>())?;
        if (span.file as usize) >= count {
            self.push(
                FixedError::Span {
                    file: span.file,
                    file_count: count,
                },
                work,
            )?;
        }
        Ok(())
    }
    pub(super) fn weights<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = work.at(&module.functions, f)? {
            let mut p = 0;
            while let Some(proof) = work.at(&function.proofs, p)? {
                work.admit(1, 0)?;
                if matches!(proof, trust_ir::ProofAnnotation::BranchWeights(_)) {
                    self.push(FixedError::Weights("branch_weights may not be attached at function scope; it belongs on a CondBr/Switch terminator node"),work)?;
                }
                work.next(&mut p)?;
            }
            let mut b = 0;
            while let Some(block) = work.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = work.at(&block.body, n)? {
                    let mut p = 0;
                    while let Some(proof) = work.at(&node.proofs, p)? {
                        work.admit(1, 0)?;
                        if let trust_ir::ProofAnnotation::BranchWeights(weights) = proof {
                            work.admit(2, size_of::<usize>())?;
                            let reason = match &node.inst {
                                Inst::CondBr { .. } if weights.len() != 2 => {
                                    Some("CondBr requires exactly 2 weights [taken, not_taken]")
                                }
                                Inst::CondBr { .. } => None,
                                Inst::Switch { cases, .. } => {
                                    let wanted = cases
                                        .len()
                                        .checked_add(1)
                                        .ok_or(ObservedValueError::CapacityOverflow)?;
                                    if weights.len() != wanted {
                                        Some(
                                            "Switch requires cases+1 weights (per-case then default)",
                                        )
                                    } else {
                                        None
                                    }
                                }
                                _ => Some("only CondBr/Switch nodes may carry branch_weights"),
                            };
                            if let Some(reason) = reason {
                                self.push(FixedError::Weights(reason), work)?;
                            }
                        }
                        work.next(&mut p)?;
                    }
                    work.next(&mut n)?;
                }
                work.next(&mut b)?;
            }
            work.next(&mut f)?;
        }
        Ok(())
    }
    pub(super) fn diagnostics<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if module.obligation_diagnostics.is_empty() {
            return Ok(());
        }
        let mut o = 0;
        while let Some(obligation) = work.at(&module.proof_obligations, o)? {
            work.reserve(&mut self.ids)?;
            work.admit(1, size_of::<u32>())?;
            self.ids.push(obligation.id.index());
            work.next(&mut o)?;
        }
        let mut d = 0;
        while let Some(diagnostic) = work.at(&module.obligation_diagnostics, d)? {
            work.admit(1, size_of::<u32>())?;
            let id = diagnostic.obligation.index();
            let mut found = false;
            let mut at = 0;
            while let Some(prior) = work.at(&self.ids, at)? {
                work.admit(1, 0)?;
                if *prior == id {
                    found = true;
                    break;
                }
                work.next(&mut at)?;
            }
            work.admit(1, 0)?;
            if !found {
                self.push(FixedError::Diagnostic(id), work)?;
            }
            work.next(&mut d)?;
        }
        Ok(())
    }
}
