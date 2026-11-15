// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    unreachable_patterns,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Local {
    pub(super) fn restatement<O: ExecutionObserver>(
        &mut self,
        local: &ProofObligation,
        callee: FuncId,
        far: &ProofObligation,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        w.admit(4, size_of::<bool>())?;
        if local.function != Some(callee) {
            self.text("local restatement obligation #", w)?;
            self.number(local.id.index() as u64, w)?;
            self.text(" is scoped to ", w)?;
            if let Some(owner) = local.function {
                self.text("Some(", w)?;
                self.number(owner.index() as u64, w)?;
                self.text(")", w)?
            } else {
                self.text("None", w)?
            }
            self.text(", not the callee declaration #", w)?;
            self.number(callee.index() as u64, w)?;
            return Ok(false);
        }
        w.admit(
            32,
            2 * size_of::<trust_ir::proof::ObligationKindShape>() + size_of::<bool>(),
        )?;
        let same = if local.kind.shape() != far.kind.shape() {
            false
        } else {
            match (&local.kind, &far.kind) {
                (
                    ObligationKind::Custom {
                        namespace: a,
                        name: b,
                    },
                    ObligationKind::Custom {
                        namespace: c,
                        name: d,
                    },
                ) => w.text_equal(a, c)? && w.text_equal(b, d)?,
                _ => {
                    use trust_ir::proof::ObligationKindShape as K;
                    match local.kind.shape() {
                        K::Precondition
                        | K::Postcondition
                        | K::LoopInvariant
                        | K::TypeInvariant
                        | K::RefinementType
                        | K::TranslationValidation
                        | K::MemorySafety
                        | K::PanicFreedom
                        | K::TemporalSafety
                        | K::Liveness
                        | K::ArithmeticSafety
                        | K::BoundsCheck
                        | K::GiveBackRefinement
                        | K::Termination
                        | K::Ownership => true,
                        _ => return Err(ObservedValueError::UnsupportedValue),
                    }
                }
            }
        };
        if !same {
            self.text("local restatement obligation #", w)?;
            self.number(local.id.index() as u64, w)?;
            self.text(" has kind ", w)?;
            self.kind(&local.kind, w)?;
            self.text(", far obligation #", w)?;
            self.number(far.id.index() as u64, w)?;
            self.text(" has kind ", w)?;
            self.kind(&far.kind, w)?;
            return Ok(false);
        }
        w.admit(4, 2 * size_of::<Option<&trust_ir::proof::ProofFormula>>())?;
        match (&local.formula, &far.formula) {
            (Some(a), Some(b)) => {
                if a.structurally_eq_observed(b, w.session, w.site)? {
                    return Ok(true);
                }
                self.text("local restatement obligation #", w)?;
                self.number(local.id.index() as u64, w)?;
                self.text(" does not restate far obligation #", w)?;
                self.number(far.id.index() as u64, w)?;
                self.text("'s formula", w)?;
            }
            (None, _) => {
                self.text("local restatement obligation #", w)?;
                self.number(local.id.index() as u64, w)?;
                self.text(
                    " carries no formula; an inherited claim must be stated, not implied",
                    w,
                )?;
            }
            (_, None) => {
                self.text("far obligation #", w)?;
                self.number(far.id.index() as u64, w)?;
                self.text(
                    " carries no formula; a claim with no statement cannot be restated",
                    w,
                )?;
            }
        }
        Ok(false)
    }
    fn kind<O: ExecutionObserver>(&mut self, kind: &ObligationKind, w: &mut Work<'_, '_, O>) -> R {
        use trust_ir::proof::ObligationKindShape as K;
        w.admit(32, size_of::<K>())?;
        let text = match kind.shape() {
            K::Precondition => "precondition",
            K::Postcondition => "postcondition",
            K::LoopInvariant => "loop_invariant",
            K::TypeInvariant => "type_invariant",
            K::RefinementType => "refinement_type",
            K::TranslationValidation => "translation_validation",
            K::MemorySafety => "memory_safety",
            K::PanicFreedom => "panic_freedom",
            K::TemporalSafety => "temporal_safety",
            K::Liveness => "liveness",
            K::ArithmeticSafety => "arithmetic_safety",
            K::BoundsCheck => "bounds_check",
            K::GiveBackRefinement => "give_back_refinement",
            K::Termination => "termination",
            K::Ownership => "ownership",
            K::Custom => {
                let ObligationKind::Custom { namespace, name } = kind else {
                    return Err(ObservedValueError::InvalidRange);
                };
                self.text("custom:", w)?;
                self.text(namespace, w)?;
                self.text("/", w)?;
                return self.text(name, w);
            }
            _ => return Err(ObservedValueError::UnsupportedValue),
        };
        self.text(text, w)
    }
    pub(super) fn site<O: ExecutionObserver>(
        &mut self,
        site: Option<ObligationSite>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(8, size_of::<Option<ObligationSite>>())?;
        if let Some(site) = site {
            self.text("fn#", w)?;
            self.number(site.function.index() as u64, w)?;
            self.text("/bb", w)?;
            self.number(site.block.index() as u64, w)?;
            self.text("#", w)?;
            self.number(site.inst_index as u64, w)
        } else {
            self.text("no site", w)
        }
    }
    pub(super) fn bound<O: ExecutionObserver>(
        &mut self,
        bound: CoverageBound,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(8, size_of::<CoverageBound>())?;
        match bound {
            CoverageBound::Unbounded => self.text("Unbounded", w),
            CoverageBound::Unrecorded => self.text("Unrecorded", w),
            CoverageBound::UnwindBounded { depth } => {
                self.text("UnwindBounded { depth: ", w)?;
                self.number(depth, w)?;
                self.text(" }", w)
            }
            CoverageBound::ModelBounded { size } => {
                self.text("ModelBounded { size: ", w)?;
                self.number(size, w)?;
                self.text(" }", w)
            }
            _ => Err(ObservedValueError::UnsupportedValue),
        }
    }
}
