// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl Inherited {
    pub(super) fn local<O: ExecutionObserver>(
        &mut self,
        a: &Authority<'_>,
        cert: &ProofCertificate,
        callee: FuncId,
        obligation: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        if !function_exists(a.module, callee, w)? {
            fixed_error!(
                self,
                w,
                ValidationError::InheritedProofCalleeNotFound {
                    obligation: cert.obligation.index(),
                    callee: callee.index()
                }
            )?;
        }
        if !self.selector.grounds(a, obligation, Currency::Kernel, w)? {
            fixed_error!(
                self,
                w,
                ValidationError::InheritedProofNotDischarged {
                    obligation: cert.obligation.index(),
                    callee: callee.index(),
                    inherited_obligation: obligation.index()
                }
            )?;
        }
        if let Some(owner) = lookup::owner(a.module, obligation, w)? {
            w.admit(1, size_of::<bool>())?;
            if owner != callee {
                fixed_error!(
                    self,
                    w,
                    ValidationError::InheritedProofCalleeScopeMismatch {
                        obligation: cert.obligation.index(),
                        named_callee: callee.index(),
                        actual_owner: owner.index()
                    }
                )?;
            }
        }
        w.admit(1, size_of::<Option<LocalInheritance>>())?;
        self.local = Some(a.local_inheritance(a.module, cert, w.session, w.site)?);
        w.admit(4, size_of::<bool>())?;
        if matches!(self.local.as_ref(), Some(LocalInheritance::Refused(_))) {
            self.prepare(w)?;
            w.admit(
                1,
                size_of::<Option<LocalInheritance>>() + size_of::<String>(),
            )?;
            let Some(LocalInheritance::Refused(detail)) = self.local.take() else {
                return Err(ObservedValueError::InvalidRange);
            };
            self.errors
                .push(ValidationError::LocalInheritanceRestatementMismatch {
                    certificate_obligation: cert.obligation.index(),
                    detail,
                });
        }
        self.retire_local(w);
        w.admit(1, 0)
    }
}
fn function_exists<O: ExecutionObserver>(
    module: &Module,
    id: FuncId,
    w: &mut Work<'_, '_, O>,
) -> R<bool> {
    if let Some(f) = w.at(&module.functions, id.as_usize())? {
        w.admit(1, size_of::<bool>())?;
        if f.id == id {
            return Ok(true);
        }
    }
    let mut at = 0;
    while let Some(f) = w.at(&module.functions, at)? {
        w.admit(1, size_of::<bool>())?;
        if f.id == id {
            return Ok(true);
        }
        w.next(&mut at)?;
    }
    Ok(false)
}
