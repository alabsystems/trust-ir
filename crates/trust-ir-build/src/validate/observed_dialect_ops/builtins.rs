// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl<'a> State<'a> {
    pub(super) fn builtin<O: ExecutionObserver>(
        &mut self,
        op: &'a DialectInst,
        values: &'a ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        if work.eq(&op.dialect, "vector")? {
            return self.vector(op, values, work);
        }
        if work.eq(&op.dialect, "gpu")? {
            for name in [
                "thread_id_x",
                "thread_id_y",
                "thread_id_z",
                "block_id_x",
                "block_id_y",
                "block_id_z",
                "block_dim_x",
                "block_dim_y",
                "block_dim_z",
                "grid_dim_x",
                "grid_dim_y",
                "grid_dim_z",
                "barrier",
            ] {
                if work.eq(&op.op, name)? {
                    return Ok(true);
                }
            }
            return self.unknown(op, "gpu", work);
        }
        if work.eq(&op.dialect, "avx512")? {
            return self.avx(op, work);
        }
        if work.eq(&op.dialect, "ane")? {
            return self.ane(op, work);
        }
        if work.eq(&op.dialect, "trust_rust")? {
            return self.tls(op, work);
        }
        // Unknown namespaces remain opaque in the original builtin rule. The
        // optional frozen registry still closes the namespace set independently.
        Ok(true)
    }
    fn unknown<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        dialect: &str,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.text("unknown op ", &mut self.reason)?;
        work.quoted(&op.op, &mut self.reason)?;
        work.text(" in dialect ", &mut self.reason)?;
        work.quoted(dialect, &mut self.reason)?;
        Ok(false)
    }
    fn avx<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let kind = if work.eq(&op.op, "mask_cmp")? {
            0
        } else if work.eq(&op.op, "vpternlog")? {
            1
        } else if work.eq(&op.op, "compress")? {
            2
        } else if work.eq(&op.op, "expand")? {
            3
        } else {
            return self.unknown(op, "avx512", work);
        };
        work.admit(2, size_of::<bool>())?;
        if op.operands.len() != if kind == 1 { 3 } else { 2 } || op.result_tys.len() != 1 {
            return self.unknown(op, "avx512", work);
        }
        if kind == 0 {
            let Some(AttrValue::Str(predicate)) = work.attr(op, "predicate")? else {
                return self.unknown(op, "avx512", work);
            };
            let mut known = false;
            for name in [
                "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
            ] {
                if work.eq(predicate, name)? {
                    known = true;
                    break;
                }
            }
            if !known {
                return self.unknown(op, "avx512", work);
            }
        }
        if kind == 1 && !matches!(work.attr(op, "imm8")?, Some(AttrValue::U64(_))) {
            return self.unknown(op, "avx512", work);
        }
        // The original imm8 conversion truncates and the original decoder does not
        // validate version/result carrier shape; this rule must not narrow either.
        Ok(true)
    }
    fn ane<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let kind = if work.eq(&op.op, "tensor_conv")? {
            0
        } else if work.eq(&op.op, "tensor_matmul")? {
            1
        } else if work.eq(&op.op, "dma_transfer")? {
            2
        } else {
            return self.unknown(op, "ane", work);
        };
        work.admit(4, size_of::<bool>())?;
        if kind == 2 {
            if op.operands.len() != 3 || !op.result_tys.is_empty() {
                return self.unknown(op, "ane", work);
            }
            let _ = work.attr(op, "direction")?;
            return Ok(true);
        }
        if !(2..=3).contains(&op.operands.len()) || op.result_tys.len() != 1 {
            return self.unknown(op, "ane", work);
        }
        if kind == 0 {
            let _ = work.attr(op, "stride")?;
            let _ = work.attr(op, "padding")?;
        }
        // Default/truncated scalar spec fields and direction String are dead after
        // decode().map(|_|()); borrowing removes only these redundant owned copies.
        Ok(true)
    }
    fn tls<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        if let Some((role, name)) = bad_name(op, work)? {
            work.text("invalid dialect op name: ", &mut self.reason)?;
            work.text(role, &mut self.reason)?;
            if name.is_empty() {
                work.text(" name must not be empty", &mut self.reason)?
            } else {
                work.text(" name ", &mut self.reason)?;
                work.quoted(name, &mut self.reason)?;
                work.text(" contains an illegal character; dialect/op/attribute names must be non-empty and use only ASCII letters, digits, and '_' (no '.', whitespace, or delimiters)",&mut self.reason)?;
            }
            return Ok(false);
        }
        if !work.eq(&op.op, "thread_local_addr")? {
            return self.unknown(op, "trust_rust", work);
        }
        if !self.tls_header(op, work)? {
            return Ok(false);
        }
        let (mut schema, mut symbol) = (None, None);
        let mut at = 0;
        while let Some(attr) = work.at(&op.attrs, at)? {
            if work.eq(&attr.name, "schema")?
                && schema.is_none()
                && let AttrValue::Str(value) = &attr.value
            {
                schema = Some(value.as_str());
                work.next(&mut at)?;
                continue;
            }
            if work.eq(&attr.name, "symbol")?
                && symbol.is_none()
                && let AttrValue::Str(value) = &attr.value
            {
                symbol = Some(value.as_str());
                work.next(&mut at)?;
                continue;
            }
            self.payload(work)?;
            work.text(
                "unexpected, duplicate, or ill-typed attribute ",
                &mut self.reason,
            )?;
            work.quoted(&attr.name, &mut self.reason)?;
            return Ok(false);
        }
        let matched = match schema {
            Some(s) => work.eq(s, "trust-rust.thread-local-addr/v1")?,
            None => false,
        };
        if !matched {
            self.payload(work)?;
            work.text(
                "schema attribute does not match version 1",
                &mut self.reason,
            )?;
            return Ok(false);
        }
        work.admit(1, size_of::<bool>())?;
        if symbol.is_none_or(str::is_empty) {
            self.payload(work)?;
            work.text(
                "symbol attribute must be a non-empty string",
                &mut self.reason,
            )?;
            return Ok(false);
        }
        Ok(true)
    }
    fn tls_header<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<bool>())?;
        if op.version != 1 {
            self.payload(work)?;
            work.text("expected payload version 1, got ", &mut self.reason)?;
            work.unsigned(u128::from(op.version), &mut self.reason)?;
            return Ok(false);
        }
        work.admit(1, size_of::<bool>())?;
        if !op.operands.is_empty() {
            self.payload(work)?;
            work.text("expected zero operands, got ", &mut self.reason)?;
            work.unsigned(op.operands.len() as u128, &mut self.reason)?;
            return Ok(false);
        }
        work.admit(2, size_of::<bool>())?;
        if op.result_tys.len() != 1 || !matches!(op.result_tys.first(), Some(Ty::Ptr)) {
            self.payload(work)?;
            work.text(
                "expected exactly one Ptr result type, got ",
                &mut self.reason,
            )?;
            self.raw_types(&op.result_tys, work)?;
            return Ok(false);
        }
        work.admit(1, size_of::<bool>())?;
        if op.attrs.len() != 2 {
            self.payload(work)?;
            work.text(
                "expected exactly schema and symbol attributes, got ",
                &mut self.reason,
            )?;
            work.unsigned(op.attrs.len() as u128, &mut self.reason)?;
            work.text(" attributes", &mut self.reason)?;
            return Ok(false);
        }
        Ok(true)
    }
    fn payload<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.text(
            "lowering pass \"trust_rust.thread_local_addr.decode\" failed: ",
            &mut self.reason,
        )
    }
}
fn bad_name<'a, O: ExecutionObserver>(
    op: &'a DialectInst,
    work: &mut Work<'_, '_, O>,
) -> R<Option<(&'static str, &'a str)>> {
    for (name, role) in [(&op.dialect, "dialect"), (&op.op, "op")] {
        if !valid(name, work)? {
            return Ok(Some((role, name)));
        }
    }
    let mut at = 0;
    while let Some(attr) = work.at(&op.attrs, at)? {
        if !valid(&attr.name, work)? {
            return Ok(Some(("attribute", &attr.name)));
        }
        work.next(&mut at)?;
    }
    Ok(None)
}
fn valid<O: ExecutionObserver>(name: &str, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.admit(1, size_of::<bool>())?;
    if name.is_empty() {
        return Ok(false);
    }
    let mut at = 0;
    while let Some(b) = work.at(name.as_bytes(), at)? {
        work.admit(1, 0)?;
        if !(b.is_ascii_alphanumeric() || *b == b'_') {
            return Ok(false);
        }
        work.next(&mut at)?;
    }
    Ok(true)
}
