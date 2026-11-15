// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(spec) = work.at(&module.spec_modules, index)? {
            let trimmed = work.trim(&spec.name)?;
            if work.prefix(trimmed, TRUST_INTERNAL_SPEC_PREFIX, Case::AsciiInsensitive)? {
                let mut admitted = false;
                let mut candidate = 0;
                while let Some(name) = work.at(RESERVED_TRUST_INTERNAL_SPEC_MODULES, candidate)? {
                    if work.equal(&spec.name, name)? {
                        admitted = true;
                        break;
                    }
                    work.next(&mut candidate)?;
                }
                work.admit(1, 0)?;
                if !admitted {
                    self.begin(spec, work)?;
                    work.text("that namespace is reserved for the Trust compiler's own in-band disclosures and its occupants are a closed set; this name is not one of them, so it can only be an impersonation of a compiler-internal disclosure",&mut self.detail)?;
                    self.push(work)?;
                } else {
                    self.shape(spec, work)?;
                    if work.equal(&spec.name, CLEAN_ORIGIN_DISCLOSURE)? {
                        self.keys(module, spec, work)?;
                    }
                }
            }
            work.next(&mut index)?;
        }
        Ok(())
    }
    fn shape<O: ExecutionObserver>(&mut self, spec: &SpecModule, work: &mut Work<'_, '_, O>) -> R {
        work.admit(
            5,
            size_of::<[bool; 5]>() + size_of::<[&str; 5]>() + 2 * size_of::<bool>(),
        )?;
        let offenders = [
            !spec.vars.is_empty(),
            !spec.actions.is_empty(),
            !spec.anchors.is_empty(),
            !spec.waivers.is_empty(),
            !spec.proofs.is_empty(),
        ];
        let labels = ["vars", "actions", "anchors", "waivers", "proofs"];
        let mut any = false;
        let mut index = 0;
        while let Some(set) = work.at(&offenders, index)? {
            work.admit(1, 0)?;
            if *set {
                any = true;
            }
            work.next(&mut index)?;
        }
        if any {
            self.begin(spec, work)?;
            work.text("a reserved disclosure carries descriptive `invariants` rows and nothing else, but this one declares ",&mut self.detail)?;
            let mut first = true;
            let mut index = 0;
            while let Some(set) = work.at(&offenders, index)? {
                work.admit(1, 0)?;
                if *set {
                    if !first {
                        work.text(", ", &mut self.detail)?;
                    }
                    let label = work
                        .at(&labels, index)?
                        .ok_or(ObservedValueError::InvalidRange)?;
                    work.text(label, &mut self.detail)?;
                    first = false;
                }
                work.next(&mut index)?;
            }
            work.text("; those fields carry executable or certifying authority a disclosure may never claim",&mut self.detail)?;
            self.push(work)?;
        }
        work.admit(1, size_of::<SpecEnforcementMode>())?;
        if spec.enforcement != SpecEnforcementMode::DesignOnly {
            self.begin(spec, work)?;
            work.text("a reserved disclosure is non-certifying design-only material, but this one declares enforcement `",&mut self.detail)?;
            work.admit(2, size_of::<&str>())?;
            work.text(spec.enforcement.tag(), &mut self.detail)?;
            work.text("`", &mut self.detail)?;
            self.push(work)?;
        }
        work.admit(1, 0)?;
        match &spec.origin {
            SpecOrigin::Embedded => {}
            SpecOrigin::External(path) => {
                self.begin(spec, work)?;
                work.text("a reserved disclosure is minted in-process by the compiler and is therefore `embedded`, but this one claims origin `external(",&mut self.detail)?;
                work.text(path, &mut self.detail)?;
                work.text(")`", &mut self.detail)?;
                self.push(work)?;
            }
        }
        Ok(())
    }
}
