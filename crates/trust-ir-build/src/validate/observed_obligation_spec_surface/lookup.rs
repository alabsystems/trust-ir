// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn machine<'a>(
        &mut self,
        rows: &'a [SpecModule],
        name: &str,
    ) -> R<Resolution<&'a SpecModule>> {
        self.admit(1, size_of::<Option<&SpecModule>>())?;
        let mut found = None;
        let mut index = 0usize;
        while let Some(row) = self.at(rows, index)? {
            if self.equal(&row.name, name)? {
                self.admit(1, size_of::<Option<&SpecModule>>())?;
                if found.is_some() {
                    return self.publish_value(Resolution::Ambiguous);
                }
                found = Some(row);
            }
            self.next(&mut index)?;
        }
        self.publish_value(match found {
            Some(row) => Resolution::Unique(row),
            None => Resolution::Missing,
        })
    }
    pub(super) fn temporal<'a>(
        &mut self,
        rows: &'a [SpecTemporal],
        name: &str,
    ) -> R<Resolution<&'a SpecTemporal>> {
        self.admit(1, size_of::<Option<&SpecTemporal>>())?;
        let mut found = None;
        let mut index = 0usize;
        while let Some(row) = self.at(rows, index)? {
            if self.equal(&row.name, name)? {
                self.admit(1, size_of::<Option<&SpecTemporal>>())?;
                if found.is_some() {
                    return self.publish_value(Resolution::Ambiguous);
                }
                found = Some(row);
            }
            self.next(&mut index)?;
        }
        self.publish_value(match found {
            Some(row) => Resolution::Unique(row),
            None => Resolution::Missing,
        })
    }
}
