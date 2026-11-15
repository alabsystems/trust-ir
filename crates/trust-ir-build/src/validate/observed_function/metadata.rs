// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl Checking {
    pub(super) fn body_gate<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if let Some(trust_ir::BodyGate::Gated { authority, .. }) = &function.body_gate
            && work.blank(authority)?
        {
            self.detail("`Gated` carries a blank authority, so it names no gate while still reading as a positive license", |detail| ValidationError::InvalidBodyGate { function: function.id.index(), detail }, work)?;
        }
        work.admit(1, 0)?;
        if let Some(path) = &function.display_path {
            if work.blank(path)? {
                self.detail(
                    "display path is blank; omit the field instead",
                    |detail| ValidationError::InvalidDisplayPath {
                        function: function.id.index(),
                        detail,
                    },
                    work,
                )?;
            } else if work.contains_byte(path, b'\n')? {
                self.detail("display path contains a newline, which the canonical text form cannot round-trip", |detail| ValidationError::InvalidDisplayPath { function: function.id.index(), detail }, work)?;
            }
        }
        Ok(())
    }
    pub(super) fn symbols<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(1, 0)?;
        if let Some(section) = &function.section {
            if work.blank(section)? {
                self.detail(
                    "section name is blank; omit the field for the default text section",
                    |detail| ValidationError::InvalidFunctionSection {
                        function: function.id.index(),
                        detail,
                    },
                    work,
                )?;
            } else if work.contains_byte(section, b'\0')? {
                self.detail(
                    "section name contains NUL, which no object-file section table can spell",
                    |detail| ValidationError::InvalidFunctionSection {
                        function: function.id.index(),
                        detail,
                    },
                    work,
                )?;
            }
        }
        work.admit(1, 0)?;
        if trust_ir_laws::visibility_contradicts_linkage(function.linkage, function.visibility) {
            self.fixed(
                || ValidationError::ContradictoryFunctionVisibility {
                    function: function.id.index(),
                    linkage: function.linkage,
                    visibility: function.visibility,
                },
                work,
            )?;
        }
        Ok(())
    }
}
