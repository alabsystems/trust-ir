// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking {
    pub(super) fn havoc<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        for proof in &function.proofs {
            work.admit(1, 0)?;
            if let Some(marker) = havoc_marker_name(proof) {
                self.location(function, work)?;
                work.text("' (function scope)", &mut self.text)?;
                self.marker(marker, work)?;
            }
        }
        for block in &function.blocks {
            work.admit(1, 0)?;
            for (index, node) in block.body.iter().enumerate() {
                work.admit(1, 0)?;
                for proof in &node.proofs {
                    work.admit(1, 0)?;
                    let (marker, legal) = match proof {
                        ProofAnnotation::FreshSymbolicHavoc => (
                            "FreshSymbolicHavoc",
                            matches!(node.inst, Inst::Undef { .. }),
                        ),
                        ProofAnnotation::RegionHavocStore => (
                            "RegionHavocStore",
                            matches!(
                                node.inst,
                                Inst::Store {
                                    volatile: false,
                                    ..
                                }
                            ),
                        ),
                        _ => continue,
                    };
                    if legal {
                        continue;
                    }
                    self.location(function, work)?;
                    work.text("' bb", &mut self.text)?;
                    let block = usize::try_from(block.id.index())
                        .map_err(|_| ObservedValueError::InvalidRange)?;
                    work.number(block, &mut self.text)?;
                    work.text(" instruction ", &mut self.text)?;
                    work.number(index, &mut self.text)?;
                    work.text(" (", &mut self.text)?;
                    // Exhaustive fixed opcode-to-static-token table only;
                    // variable instruction/type/constant payloads are untouched.
                    work.admit(67, 0)?;
                    work.text(instruction_kind(&node.inst), &mut self.text)?;
                    work.text(")", &mut self.text)?;
                    self.marker(marker, work)?;
                }
            }
        }
        Ok(())
    }
    fn location<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.text("function '", &mut self.text)?;
        work.text(&function.name, &mut self.text)
    }
    fn marker<O: ExecutionObserver>(
        &mut self,
        marker: &'static str,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, size_of::<ValidationError>())?;
        self.pending = Some(ValidationError::HavocMarkerMisplaced {
            location: take(&mut self.text),
            marker,
        });
        self.commit(work)
    }
}
