// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Local {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        cert: &ProofCertificate,
        w: &mut Work<'_, '_, O>,
    ) -> R<Verdict> {
        w.admit(8, size_of::<Option<(FuncId, ProofId)>>())?;
        let ProofEvidence::InheritedFromCallee {
            callee,
            obligation: far_id,
            external: None,
        } = &cert.evidence
        else {
            return Ok(Verdict::NotRouted);
        };
        let mut any_discharged = false;
        let mut local = None;
        let mut count = 0usize;
        let mut at = 0;
        while let Some(row) = w.at(&a.module.proof_obligations, at)? {
            w.admit(
                4,
                size_of::<usize>() + size_of::<Option<&ProofObligation>>() + size_of::<bool>(),
            )?;
            if row.id == cert.obligation {
                count = count
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                local = Some(row);
                any_discharged |= row.status == ProofStatus::Discharged;
            }
            w.next(&mut at)?;
        }
        if !any_discharged {
            return Ok(Verdict::NotRouted);
        }
        if count != 1 {
            self.text("discharged obligation #", w)?;
            self.number(cert.obligation.index() as u64, w)?;
            self.text(" does not resolve uniquely", w)?;
            return self.refused(w);
        }
        let local = local.ok_or(ObservedValueError::InvalidRange)?;
        if !function_exists(a.module, *callee, w)? {
            return Ok(Verdict::NamedElsewhere);
        }
        if !self.selector.grounds(a, *far_id, Currency::Kernel, w)? {
            return Ok(Verdict::NamedElsewhere);
        }
        let far = unique(a.module, *far_id, w)?;
        let Some(far) = far else {
            self.text("inherited obligation #", w)?;
            self.number(far_id.index() as u64, w)?;
            self.text(" does not resolve uniquely", w)?;
            return self.refused(w);
        };
        w.admit(3, 2 * size_of::<Option<FuncId>>())?;
        match far.function {
            Some(owner) if owner == *callee => {}
            Some(_) => return Ok(Verdict::NamedElsewhere),
            None => {
                self.text("inherited obligation #", w)?;
                self.number(far_id.index() as u64, w)?;
                self.text(" is scoped to no function; a same-module inheritance must cite a row its callee fn#",w)?;
                self.number(callee.index() as u64, w)?;
                self.text(" owns", w)?;
                return self.refused(w);
            }
        }
        if !self.restatement(local, *callee, far, w)? {
            return self.refused(w);
        }
        w.admit(16, 2 * size_of::<Option<ObligationSite>>())?;
        if local.site.is_some() && local.site != far.site {
            self.text("local restatement obligation #", w)?;
            self.number(local.id.index() as u64, w)?;
            self.text(" is sited at ", w)?;
            self.site(local.site, w)?;
            self.text(", but far obligation #", w)?;
            self.number(far.id.index() as u64, w)?;
            self.text(" is ", w)?;
            if far.site.is_some() {
                self.text("sited at ", w)?;
                self.site(far.site, w)?
            } else {
                self.text("unsited", w)?
            }
            self.text(
                "; an inheritance restates a claim, it cannot move it onto another check",
                w,
            )?;
            return self.refused(w);
        }
        self.coverage(a.module, cert, far, w)
    }
    fn coverage<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        cert: &ProofCertificate,
        far: &ProofObligation,
        w: &mut Work<'_, '_, O>,
    ) -> R<Verdict> {
        w.admit(8, size_of::<CoverageBound>())?;
        let needs = cert
            .assurance
            .map_or(CoverageBound::Unrecorded, |assurance| assurance.bound);
        if needs == CoverageBound::Unrecorded {
            return Ok(Verdict::Admitted);
        }
        let mut at = 0;
        while let Some(other) = w.at(&module.proof_certificates, at)? {
            w.admit(8, size_of::<Option<CoverageBound>>())?;
            if other.obligation == far.id
                && let Some(assurance) = other.assurance
            {
                w.local_push(&mut self.recorded, assurance.bound)?;
            }
            w.next(&mut at)?;
        }
        let mut at = 0;
        while let Some(bound) = w.at(&self.recorded, at)? {
            // Actual source-bound closed Copy decision table, no heap or callback.
            w.admit(16, 2 * size_of::<CoverageBound>() + size_of::<bool>())?;
            if !crate::linked::coverage_supports(*bound, needs) {
                self.text("the inheritance certificate claims coverage ", w)?;
                self.bound(needs, w)?;
                self.text(", but far obligation #", w)?;
                self.number(far.id.index() as u64, w)?;
                self.text(" records [", w)?;
                let mut pos = 0;
                while let Some(bound) = w.at(&self.recorded, pos)?.copied() {
                    if pos != 0 {
                        self.text(", ", w)?;
                    }
                    self.bound(bound, w)?;
                    w.next(&mut pos)?;
                }
                self.text("]; coverage does not grow across an inheritance edge", w)?;
                return self.refused(w);
            }
            w.next(&mut at)?;
        }
        Ok(Verdict::Admitted)
    }
}
fn unique<'a, O: ExecutionObserver>(
    module: &'a Module,
    id: ProofId,
    w: &mut Work<'_, '_, O>,
) -> R<Option<&'a ProofObligation>> {
    let mut found = None;
    let mut ambiguous = false;
    let mut at = 0;
    while let Some(row) = w.at(&module.proof_obligations, at)? {
        w.admit(3, size_of::<Option<&ProofObligation>>() + size_of::<bool>())?;
        if row.id == id {
            if found.is_some() {
                ambiguous = true;
            } else {
                found = Some(row);
            }
        }
        w.next(&mut at)?;
    }
    Ok(if ambiguous { None } else { found })
}
fn function_exists<O: ExecutionObserver>(
    module: &Module,
    id: FuncId,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    if let Some(function) = w.at(&module.functions, id.as_usize())? {
        w.admit(1, size_of::<bool>())?;
        if function.id == id {
            return Ok(true);
        }
    }
    let mut at = 0;
    while let Some(function) = w.at(&module.functions, at)? {
        w.admit(1, size_of::<bool>())?;
        if function.id == id {
            return Ok(true);
        }
        w.next(&mut at)?;
    }
    Ok(false)
}
