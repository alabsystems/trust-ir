//! Consuming local state and exact bounded chunk copies under the same owner.
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn retire_certificate<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.session.retirement_record(
            w.site,
            size_of::<Option<&ProofCertificate>>() + size_of::<Option<bool>>() + 1,
            size_of::<Option<&ProofCertificate>>() + size_of::<Option<bool>>(),
        );
        self.certificate = None;
        self.lineage = None;
    }
    pub(super) fn retire_borrows<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.retire_certificate(w);
        w.session.retirement_record(
            w.site,
            size_of::<Option<&ProofObligation>>() + 1,
            size_of::<Option<&ProofObligation>>(),
        );
        self.row = None;
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.retire_borrows(w);
        w.session.retirement_record(
            w.site,
            size_of::<Option<ValidationError>>() + 1,
            size_of::<Option<ValidationError>>(),
        );
        if let Some(error) = self.pending.take() {
            let _ = retire_validation_error_observed(error, w.session, w.site);
        }
        retire_text(take(&mut self.field), w);
        retire_text(take(&mut self.detail), w);
    }
    pub(super) fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Vec<ValidationError>> {
        self.retire_scratch(w);
        if let Err(error) = result {
            let _ = retire_validation_errors_observed(take(&mut self.errors), w.session, w.site);
            w.session
                .retirement_record(w.site, size_of::<Self>() + 1, size_of::<Self>());
            return Err(error);
        }
        // Full owned output moved before the next header or publication fee.
        let output = take(&mut self.errors);
        w.session
            .retirement_record(w.site, size_of::<Self>() + 1, size_of::<Self>());
        match w.publication() {
            Ok(()) => Ok(output),
            Err(error) => {
                let _ = retire_validation_errors_observed(output, w.session, w.site);
                Err(error)
            }
        }
    }
}
pub(super) fn text<O: ExecutionObserver>(
    out: &mut String,
    mut input: &str,
    w: &mut Work<'_, '_, O>,
) -> R {
    loop {
        w.admit(1, size_of::<usize>())?;
        if input.is_empty() {
            return Ok(());
        }
        let mut n = input.len().min(1024);
        loop {
            w.admit(1, 0)?;
            if input.is_char_boundary(n) {
                break;
            }
            n -= 1;
        }
        w.admit(3, 3 * size_of::<usize>())?;
        let needed = out
            .len()
            .checked_add(n)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > out.capacity() {
            let requested = out
                .len()
                .checked_mul(2)
                .and_then(|v| v.checked_add(n))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(out.capacity())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            w.admit(images, images)?;
            out.try_reserve_exact(requested - out.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        if out.capacity() < needed {
            return Err(ObservedValueError::InvalidRange);
        }
        // Read+write append plus eventual consuming byte visit; copied
        // payload and its cleanup image are covered before construction.
        w.admit(
            n.checked_mul(3)
                .and_then(|v| v.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?,
            n.checked_mul(2)
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )?;
        out.push_str(&input[..n]);
        input = &input[n..];
    }
}
fn retire_text<O: ExecutionObserver>(text: String, w: &mut Work<'_, '_, O>) {
    w.session.retirement_record(
        w.site,
        size_of::<String>() + size_of::<Vec<u8>>() + 1,
        size_of::<String>() + size_of::<Vec<u8>>(),
    );
    let mut bytes = text.into_bytes();
    while !bytes.is_empty() {
        let n = bytes.len().min(1024);
        w.session.retirement_record(w.site, n + 1, n);
        bytes.truncate(bytes.len() - n);
    }
    w.session
        .retirement_record(w.site, size_of::<Vec<u8>>() + 1, size_of::<Vec<u8>>());
    drop(bytes);
}
