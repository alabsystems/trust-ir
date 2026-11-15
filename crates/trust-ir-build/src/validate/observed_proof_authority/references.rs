// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State {
    pub(super) fn references<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut f = 0;
        while let Some(function) = w.at(&a.module.functions, f)? {
            self.annotations(a, function.id, None, &function.proofs, w)?;
            let mut b = 0;
            while let Some(block) = w.at(&function.blocks, b)? {
                let mut n = 0;
                while let Some(node) = w.at(&block.body, n)? {
                    w.admit(1, size_of::<Option<u32>>())?;
                    if let Ok(index) = u32::try_from(n) {
                        self.annotations(
                            a,
                            function.id,
                            Some(ObligationSite::new(function.id, block.id, index)),
                            &node.proofs,
                            w,
                        )?;
                    } else {
                        self.unsited(function.id, &node.proofs, w)?;
                    }
                    w.next(&mut n)?;
                }
                w.next(&mut b)?;
            }
            w.next(&mut f)?;
        }
        Ok(())
    }
    fn unsited<O: ExecutionObserver>(
        &mut self,
        function: FuncId,
        anns: &[ProofAnnotation],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(ann) = w.at(anns, at)? {
            w.admit(32, size_of::<Option<ProofId>>())?;
            if let Some(id) = ann.backing_obligation() {
                fixed_error!(
                    self,
                    w,
                    ValidationError::ProofRefSiteMismatch {
                        function: function.index(),
                        obligation: id.index(),
                    }
                )?;
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn annotations<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        function: FuncId,
        node: Option<ObligationSite>,
        anns: &[ProofAnnotation],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(ann) = w.at(anns, at)? {
            w.admit(32, size_of::<Option<ProofId>>())?;
            if let Some(id) = ann.backing_obligation() {
                self.backref(a, function, node, anns, id, w)?;
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn backref<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        function: FuncId,
        node: Option<ObligationSite>,
        anns: &[ProofAnnotation],
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let fid = function.index();
        let oid = id.index();
        let Some(row) = lookup::last(a.module, id, w)? else {
            return fixed_error!(
                self,
                w,
                ValidationError::ProofRefUnresolved {
                    function: fid,
                    obligation: oid,
                    missing: true,
                }
            );
        };
        if !self.grounds(a, id, Currency::Kernel, w)? {
            fixed_error!(
                self,
                w,
                ValidationError::ProofRefUnresolved {
                    function: fid,
                    obligation: oid,
                    missing: false,
                }
            )?;
        }
        let (mut substantive, mut matches) = (false, false);
        let mut at = 0;
        while let Some(claim) = w.at(anns, at)? {
            // Exact existing finite shape/category table. No variable Custom
            // payload is cloned/rendered/parsed; every concrete row is paid.
            w.admit(
                256,
                size_of::<Option<trust_ir::proof::ObligationKind>>() + 2 * size_of::<bool>(),
            )?;
            if proof_ref_is_substantive_claim(claim) {
                substantive = true;
                if proof_ref_kind_can_back(&row.kind, claim, node.is_some()) {
                    matches = true;
                }
            }
            w.next(&mut at)?;
        }
        if !substantive {
            return fixed_error!(
                self,
                w,
                ValidationError::ProofRefWithoutClaim {
                    function: fid,
                    obligation: oid,
                }
            );
        }
        if !matches {
            return fixed_error!(
                self,
                w,
                ValidationError::ProofRefKindMismatch {
                    function: fid,
                    obligation: oid,
                    kind: obligation_kind_name(&row.kind),
                }
            );
        }
        if let Some(owner) = row.function
            && owner != function
        {
            return fixed_error!(
                self,
                w,
                ValidationError::ProofRefScopeMismatch {
                    function: fid,
                    obligation: oid,
                    owner: owner.index(),
                }
            );
        }
        if let Some(site) = node
            && row.site != Some(site)
        {
            fixed_error!(
                self,
                w,
                ValidationError::ProofRefSiteMismatch {
                    function: fid,
                    obligation: oid,
                }
            )?;
        }
        Ok(())
    }
}
