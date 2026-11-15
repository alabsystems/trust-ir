// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Exact ordinary source blocks; no observed implementation supplies the oracle.
use super::*;
pub(super) fn run(module: &Module, kind: Component) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    match kind {
        Component::Spans => {
            // Debug-info: when a source-file table is present, every SourceSpan::file
            // must index into it. (An empty table means spans are file-less, which is
            // the back-compat default — nothing to check.)
            if !module.files.is_empty() {
                let file_count = module.files.len();
                for func in &module.functions {
                    if let Some(scopes) = &func.scopes {
                        for scope in scopes {
                            // The scope's own opening span and, for an inlined scope,
                            // the call-site span of its chain link (WS4.19) both
                            // index the same file table.
                            let spans = scope
                                .span
                                .iter()
                                .chain(scope.inlined_at.iter().map(|link| &link.span));
                            for span in spans {
                                if (span.file as usize) >= file_count {
                                    errors.push(ValidationError::SpanFileIndexOutOfRange {
                                        file: span.file,
                                        file_count,
                                    });
                                }
                            }
                        }
                    }
                    for block in &func.blocks {
                        for node in &block.body {
                            if let Some(span) = &node.span
                                && (span.file as usize) >= file_count
                            {
                                errors.push(ValidationError::SpanFileIndexOutOfRange {
                                    file: span.file,
                                    file_count,
                                });
                            }
                        }
                    }
                }
                // An obligation diagnostic's source location is also a SourceSpan whose
                // `file` indexes module.files; a dangling index is exactly the
                // "dangling integer" the file table exists to prevent.
                for d in &module.obligation_diagnostics {
                    if let Some(span) = &d.location
                        && (span.file as usize) >= file_count
                    {
                        errors.push(ValidationError::SpanFileIndexOutOfRange {
                            file: span.file,
                            file_count,
                        });
                    }
                }
            }
        }
        Component::Weights => {
            // BranchWeights hints must sit on the right terminator with matching arity.
            for func in &module.functions {
                // Function scope is never a valid home for a per-edge BranchWeights hint
                // (it annotates a specific CondBr/Switch terminator, not the function).
                for p in &func.proofs {
                    if matches!(p, trust_ir::ProofAnnotation::BranchWeights(_)) {
                        errors.push(ValidationError::BranchWeightsMismatch {
                            reason: "branch_weights may not be attached at function scope; \
                             it belongs on a CondBr/Switch terminator node",
                        });
                    }
                }
                for block in &func.blocks {
                    for node in &block.body {
                        for p in &node.proofs {
                            if let trust_ir::ProofAnnotation::BranchWeights(weights) = p {
                                match &node.inst {
                                    trust_ir::Inst::CondBr { .. } => {
                                        if weights.len() != 2 {
                                            errors.push(ValidationError::BranchWeightsMismatch {
                                        reason: "CondBr requires exactly 2 weights [taken, not_taken]",
                                    });
                                        }
                                    }
                                    trust_ir::Inst::Switch { cases, .. } => {
                                        if weights.len() != cases.len() + 1 {
                                            errors.push(ValidationError::BranchWeightsMismatch {
                                        reason: "Switch requires cases+1 weights (per-case then default)",
                                    });
                                        }
                                    }
                                    _ => errors.push(ValidationError::BranchWeightsMismatch {
                                        reason: "only CondBr/Switch nodes may carry branch_weights",
                                    }),
                                }
                            }
                        }
                    }
                }
            }
        }
        Component::Diagnostics => {
            // Obligation diagnostics must reference an obligation that exists.
            if !module.obligation_diagnostics.is_empty() {
                let ob_ids: BTreeSet<u32> = module
                    .proof_obligations
                    .iter()
                    .map(|o| o.id.index())
                    .collect();
                for d in &module.obligation_diagnostics {
                    if !ob_ids.contains(&d.obligation.index()) {
                        errors.push(ValidationError::DanglingDiagnosticObligation {
                            obligation: d.obligation.index(),
                        });
                    }
                }
            }
        }
    }
    errors
}
