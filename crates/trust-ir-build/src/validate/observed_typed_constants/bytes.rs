// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State<'_> {
    pub(super) fn bytes<O: ExecutionObserver>(
        &mut self,
        module: &Module,
        data: &[u8],
        utf8: bool,
        id: TyId,
        len: u64,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        match work.at(&module.types, id.as_usize())? {
            Some(Ty::U8) => {}
            Some(other) => {
                work.text("[u8; ", &mut self.expected)?;
                work.unsigned(u128::from(len), &mut self.expected)?;
                work.text("] (bytes constant)", &mut self.expected)?;
                work.text("array element ", &mut self.actual)?;
                self.render_actual_ty(other, work)?;
                self.mismatch_ready(work)?;
            }
            None => self.missing("ty.", id.index(), work)?,
        }
        work.admit(2, size_of::<bool>())?;
        if data.len() as u64 != len {
            work.unsigned(u128::from(len), &mut self.expected)?;
            work.text(" bytes", &mut self.expected)?;
            work.unsigned(data.len() as u128, &mut self.actual)?;
            work.text(" bytes", &mut self.actual)?;
            self.mismatch_ready(work)?;
        }
        if utf8 && !utf8_is_valid_observed(data, work.session, work.site)? {
            work.text("valid UTF-8 under the utf8 claim", &mut self.expected)?;
            work.text("invalid UTF-8 byte sequence", &mut self.actual)?;
            self.mismatch_ready(work)?;
        }
        if self.uniform_bytes(data, utf8, work)? {
            work.text("a bytes constant of ", &mut self.spelling)?;
            work.unsigned(data.len() as u128, &mut self.spelling)?;
            work.text(" equal bytes is spelled `splat[ ", &mut self.spelling)?;
            let byte = work.at(data, 0)?.ok_or(ObservedValueError::InvalidRange)?;
            work.unsigned(u128::from(*byte), &mut self.spelling)?;
            work.text("; ", &mut self.spelling)?;
            work.unsigned(data.len() as u128, &mut self.spelling)?;
            work.text(" ]`", &mut self.spelling)?;
            self.uniform_error(work)?;
        }
        Ok(())
    }
    fn uniform_bytes<O: ExecutionObserver>(
        &mut self,
        data: &[u8],
        utf8: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(4, size_of::<usize>() + size_of::<u8>())?;
        if utf8 || data.len() < 2 {
            return Ok(false);
        }
        let first = *work.at(data, 0)?.ok_or(ObservedValueError::InvalidRange)?;
        let mut at = 1;
        while let Some(byte) = work.at(data, at)? {
            work.admit(1, size_of::<bool>())?;
            if *byte != first {
                return Ok(false);
            }
            work.next(&mut at)?;
        }
        Ok(true)
    }
}
