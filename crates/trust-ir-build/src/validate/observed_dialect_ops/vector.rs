// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Clone, Copy)]
pub(super) struct Spec<'a> {
    pub(super) kind: usize,
    pub(super) vector: &'a Ty,
    pub(super) elem: &'a Ty,
    pub(super) lanes: u32,
}
impl<'a> State<'a> {
    pub(super) fn vector<O: ExecutionObserver>(
        &mut self,
        op: &'a DialectInst,
        values: &'a ObservedValueTypes,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        // The real Option<Vec<Ty>> collector stops at the first missing operand.
        // Borrowed rows omit dead clones only; preserve that exact fallback boundary.
        let mut at = 0;
        let mut all = true;
        while let Some(id) = work.at(&op.operands, at)? {
            let Some(ty) = values.get_observed(*id, work.session, work.site)? else {
                all = false;
                break;
            };
            work.reserve(&mut self.operand_tys)?;
            work.admit(1, size_of::<&Ty>())?;
            self.operand_tys.push(ty);
            work.next(&mut at)?;
        }
        let Some(spec) = self.vector_payload(op, work)? else {
            return Ok(false);
        };
        if !all {
            return Ok(true);
        }
        let mut at = 0;
        while let Some(actual) = work.at(&self.operand_tys, at)?.copied() {
            let (expected, role) = match (spec.kind, at) {
                (0, _) => (spec.elem, "lane"),
                (2, 1) => (spec.elem, "lane value"),
                (3, _) => (spec.vector, "mask"),
                (6, 0) => (spec.vector, "multiplicand"),
                (6, 1) => (spec.vector, "multiplier"),
                (6, _) => (spec.vector, "addend"),
                _ => (spec.vector, "vector"),
            };
            if !actual.structural_eq_observed(expected, work.session, work.site)? {
                self.q(op, work)?;
                work.text(" ", &mut self.reason)?;
                work.text(role, &mut self.reason)?;
                work.text(" operand ", &mut self.reason)?;
                work.unsigned(at as u128, &mut self.reason)?;
                work.text(" (%", &mut self.reason)?;
                let id = work
                    .at(&op.operands, at)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                work.unsigned(u128::from(id.index()), &mut self.reason)?;
                work.text(") type ", &mut self.reason)?;
                self.display_ty(actual, work)?;
                work.text(" does not match expected ", &mut self.reason)?;
                self.display_ty(expected, work)?;
                return Ok(false);
            }
            work.next(&mut at)?;
        }
        Ok(true)
    }
    pub(super) fn vector_payload<'o, O: ExecutionObserver>(
        &mut self,
        op: &'o DialectInst,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Spec<'o>>> {
        let mut kind = None;
        for (index, name) in [
            "pack_lanes",
            "extract_lane",
            "insert_lane",
            "mask_to_bits",
            "reduce",
            "shuffle",
            "fma",
        ]
        .iter()
        .enumerate()
        {
            if work.eq(&op.op, name)? {
                kind = Some(index);
                break;
            }
        }
        let Some(kind) = kind else {
            work.text("unknown vector op ", &mut self.reason)?;
            work.quoted(&op.op, &mut self.reason)?;
            work.text("; expected one of [\"pack_lanes\", \"extract_lane\", \"insert_lane\", \"mask_to_bits\", \"reduce\", \"shuffle\", \"fma\"]",&mut self.reason)?;
            return Ok(None);
        };
        work.admit(1, size_of::<bool>())?;
        if op.version != 1 {
            self.q(op, work)?;
            work.text(" version ", &mut self.reason)?;
            work.unsigned(u128::from(op.version), &mut self.reason)?;
            work.text(" is unsupported; expected version 1", &mut self.reason)?;
            return Ok(None);
        }
        if kind != 0
            && !self.vector_count(
                op,
                if kind == 2 {
                    2
                } else if kind == 6 {
                    3
                } else {
                    1
                },
                false,
                work,
            )?
        {
            return Ok(None);
        }
        if !self.vector_count(op, 1, true, work)? {
            return Ok(None);
        }
        self.vector_body(op, kind, work)
    }
    fn vector_body<'o, O: ExecutionObserver>(
        &mut self,
        op: &'o DialectInst,
        kind: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<Spec<'o>>> {
        let vector = if matches!(kind, 1 | 3 | 4) {
            let key = if kind == 3 { "mask_ty" } else { "vector_ty" };
            match work.attr(op, key)? {
                Some(AttrValue::Ty(ty)) => ty,
                _ => {
                    self.q(op, work)?;
                    work.text(" requires Ty attribute ", &mut self.reason)?;
                    work.quoted(key, &mut self.reason)?;
                    return Ok(None);
                }
            }
        } else {
            work.at(&op.result_tys, 0)?
                .ok_or(ObservedValueError::InvalidRange)?
        };
        let Some((elem, lanes)) = self.vector_shape(op, vector, kind, work)? else {
            return Ok(None);
        };
        if kind == 0 {
            work.admit(1, size_of::<bool>())?;
            if op.operands.len() != lanes as usize {
                self.q(op, work)?;
                work.text(" expects ", &mut self.reason)?;
                work.unsigned(u128::from(lanes), &mut self.reason)?;
                work.text(" lane operand(s), got ", &mut self.reason)?;
                work.unsigned(op.operands.len() as u128, &mut self.reason)?;
                return Ok(None);
            }
        }
        if matches!(kind, 1 | 2) && !self.lane(op, lanes, work)? {
            return Ok(None);
        }
        if kind == 4 && !self.reduce_kind(op, work)? {
            return Ok(None);
        }
        if matches!(kind, 1 | 4) {
            let actual = work
                .at(&op.result_tys, 0)?
                .ok_or(ObservedValueError::InvalidRange)?;
            if !actual.structural_eq_observed(elem, work.session, work.site)? {
                self.q(op, work)?;
                work.text(" result type ", &mut self.reason)?;
                self.raw_ty(actual, work)?;
                work.text(" does not match vector element type ", &mut self.reason)?;
                self.raw_ty(elem, work)?;
                return Ok(None);
            }
        }
        if kind == 3 && !self.mask_result(op, lanes, work)? {
            return Ok(None);
        }
        if kind == 5 && !self.shuffle(op, lanes, work)? {
            return Ok(None);
        }
        Ok(Some(Spec {
            kind,
            vector,
            elem,
            lanes,
        }))
    }
    pub(super) fn vector_count<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        expected: usize,
        result: bool,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        work.admit(1, size_of::<usize>() + size_of::<bool>())?;
        let actual = if result {
            op.result_tys.len()
        } else {
            op.operands.len()
        };
        if actual == expected {
            return Ok(true);
        }
        self.q(op, work)?;
        work.text(" expects ", &mut self.reason)?;
        work.unsigned(expected as u128, &mut self.reason)?;
        work.text(
            if result {
                " result type(s), got "
            } else {
                " operand(s), got "
            },
            &mut self.reason,
        )?;
        work.unsigned(actual as u128, &mut self.reason)?;
        Ok(false)
    }
}
