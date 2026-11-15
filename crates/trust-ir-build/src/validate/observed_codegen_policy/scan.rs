// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        rule: Rule,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, 0)?;
        if matches!(rule, Rule::GlobalAsm) {
            if !module.global_asm.is_empty() {
                w.admit(1, size_of::<ValidationError>())?;
                self.pending = Some(ValidationError::GlobalAsmNotConsumable {
                    blocks: module.global_asm.len(),
                });
                self.emit(w)?;
            }
            return Ok(());
        }
        let mut f = 0;
        while let Some(function) = w.at(&module.functions, f)? {
            w.admit(1, 0)?;
            match rule {
                Rule::GateEvidence => self.gate(function, w)?,
                Rule::PanicKinds | Rule::PanicSites => self.asserts(function, rule, w)?,
                Rule::GlobalAsm => return Err(ObservedValueError::InvalidRange),
            }
            w.next(&mut f)?;
        }
        Ok(())
    }
    fn gate<O: ExecutionObserver>(&mut self, function: &Function, w: &mut Work<'_, '_, O>) -> R {
        w.admit(1, 0)?;
        if function.is_declaration() {
            return Ok(());
        }
        if let Some(trust_ir::BodyGate::Gated {
            authority,
            evidence: None,
        }) = &function.body_gate
        {
            let mut i = 0;
            while let Some((name, _)) = w.at(EVIDENCE_BOUND_GATE_AUTHORITIES, i)? {
                if w.equal(authority, name)? {
                    w.text(authority, &mut self.text)?;
                    w.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
                    self.pending = Some(ValidationError::UnevidencedGate {
                        function: function.id.index(),
                        authority: take(&mut self.text),
                    });
                    self.emit(w)?;
                    break;
                }
                w.next(&mut i)?;
            }
        }
        Ok(())
    }
    fn asserts<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        rule: Rule,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut b = 0;
        while let Some(block) = w.at(&function.blocks, b)? {
            let mut i = 0;
            while let Some(node) = w.at(&block.body, i)? {
                w.admit(1, 0)?;
                let report = match (rule, &node.inst) {
                    (Rule::PanicKinds, Inst::Assert { kind, .. }) => kind.is_unspecified(),
                    (Rule::PanicSites, Inst::Assert { site, .. }) => site.is_none(),
                    _ => false,
                };
                if report {
                    w.text(&function.name, &mut self.text)?;
                    w.admit(1, size_of::<ValidationError>() + size_of::<String>())?;
                    // Preserve the actual original diagnostic's u32 cast. This
                    // is data reporting, not a new source-address capability.
                    self.pending = Some(match rule {
                        Rule::PanicKinds => ValidationError::AssertPanicKindUnspecified {
                            function: take(&mut self.text),
                            block: block.id.index(),
                            inst_index: i as u32,
                        },
                        Rule::PanicSites => ValidationError::AssertPanicSiteMissing {
                            function: take(&mut self.text),
                            block: block.id.index(),
                            inst_index: i as u32,
                        },
                        _ => return Err(ObservedValueError::InvalidRange),
                    });
                    self.emit(w)?;
                }
                w.next(&mut i)?;
            }
            w.next(&mut b)?;
        }
        Ok(())
    }
}
