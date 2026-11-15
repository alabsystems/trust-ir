// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    dead_code,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
impl State<'_> {
    pub(super) fn vector_shape<'t, O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        ty: &'t Ty,
        kind: usize,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<(&'t Ty, u32)>> {
        work.admit(16, size_of::<Option<(&Ty, u32)>>())?;
        if let Ty::Vector(elem, lanes) = ty {
            let integer = matches!(
                (elem.as_ref(), *lanes),
                (Ty::I8, 16 | 8) | (Ty::I16, 8) | (Ty::I32, 4) | (Ty::I64, 2)
            );
            let float = matches!((elem.as_ref(), *lanes), (Ty::F32, 4) | (Ty::F64, 2));
            let mask = matches!((elem.as_ref(), *lanes), (Ty::Bool, 16 | 8 | 4 | 2));
            if match kind {
                0 => integer || float,
                3 => mask,
                6 => float,
                _ => integer,
            } {
                return Ok(Some((elem, *lanes)));
            }
        }
        self.q(op, work)?;
        work.text(match kind{0=>" supports only <16 x i8>, <8 x i16>, <4 x i32>, <2 x i64>, <8 x i8>, <4 x f32>, and <2 x f64> lane vectors, got ",3=>" supports only logical <16 x bool>, <8 x bool>, <4 x bool>, and <2 x bool> masks, got ",6=>" supports only <4 x f32> and <2 x f64> float lane vectors, got ",_=>" supports only <16 x i8>, <8 x i16>, <4 x i32>, <2 x i64>, and <8 x i8> lane vectors, got "},&mut self.reason)?;
        self.raw_ty(ty, work)?;
        Ok(None)
    }
    pub(super) fn lane<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        lanes: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let Some(AttrValue::U64(raw)) = work.attr(op, "lane")? else {
            self.q(op, work)?;
            work.text(" requires U64 attribute \"lane\"", &mut self.reason)?;
            return Ok(false);
        };
        work.admit(2, size_of::<Option<u32>>())?;
        let Ok(lane) = u32::try_from(*raw) else {
            self.q(op, work)?;
            work.text(" lane attribute ", &mut self.reason)?;
            work.unsigned(u128::from(*raw), &mut self.reason)?;
            work.text(" does not fit in u32", &mut self.reason)?;
            return Ok(false);
        };
        if lane >= lanes {
            self.q(op, work)?;
            work.text(" lane ", &mut self.reason)?;
            work.unsigned(u128::from(lane), &mut self.reason)?;
            work.text(" is out of range for ", &mut self.reason)?;
            work.unsigned(u128::from(lanes), &mut self.reason)?;
            work.text(" lane vector", &mut self.reason)?;
            return Ok(false);
        }
        Ok(true)
    }
    pub(super) fn reduce_kind<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let Some(AttrValue::Str(raw)) = work.attr(op, "kind")? else {
            self.q(op, work)?;
            work.text(" requires Str attribute \"kind\"", &mut self.reason)?;
            return Ok(false);
        };
        if work.eq(raw, "add")? || work.eq(raw, "or")? {
            return Ok(true);
        }
        self.q(op, work)?;
        work.text(" unsupported reduce kind ", &mut self.reason)?;
        work.quoted(raw, &mut self.reason)?;
        work.text("; expected \"add\" or \"or\"", &mut self.reason)?;
        Ok(false)
    }
    pub(super) fn shuffle<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        lanes: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let Some(AttrValue::Bytes(raw)) = work.attr(op, "indices")? else {
            self.q(op, work)?;
            work.text(" requires Bytes attribute \"indices\"", &mut self.reason)?;
            return Ok(false);
        };
        work.admit(1, size_of::<bool>())?;
        if raw.len() != lanes as usize {
            self.q(op, work)?;
            work.text(" expects ", &mut self.reason)?;
            work.unsigned(u128::from(lanes), &mut self.reason)?;
            work.text(" shuffle index/indices, got ", &mut self.reason)?;
            work.unsigned(raw.len() as u128, &mut self.reason)?;
            return Ok(false);
        }
        let mut at = 0;
        while let Some(index) = work.at(raw, at)? {
            work.admit(1, size_of::<bool>())?;
            if u32::from(*index) >= lanes {
                self.q(op, work)?;
                work.text(" shuffle index ", &mut self.reason)?;
                work.unsigned(u128::from(*index), &mut self.reason)?;
                work.text(" for result lane ", &mut self.reason)?;
                work.unsigned(at as u128, &mut self.reason)?;
                work.text(" is out of range for ", &mut self.reason)?;
                work.unsigned(u128::from(lanes), &mut self.reason)?;
                work.text(" lane vector", &mut self.reason)?;
                return Ok(false);
            }
            work.next(&mut at)?;
        }
        Ok(true)
    }
    pub(super) fn mask_result<O: ExecutionObserver>(
        &mut self,
        op: &DialectInst,
        lanes: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let result = work
            .at(&op.result_tys, 0)?
            .ok_or(ObservedValueError::InvalidRange)?;
        work.admit(4, size_of::<bool>())?;
        if !(matches!(result, Ty::I32) || (lanes == 2 && matches!(result, Ty::I64))) {
            self.q(op, work)?;
            work.text(" <", &mut self.reason)?;
            work.unsigned(u128::from(lanes), &mut self.reason)?;
            work.text(" x bool> mask_to_bits result must be ", &mut self.reason)?;
            work.text(
                if lanes == 2 { "i32 or i64" } else { "i32" },
                &mut self.reason,
            )?;
            work.text(", got ", &mut self.reason)?;
            self.raw_ty(result, work)?;
            return Ok(false);
        }
        match work.attr(op, "bit_order")? {
            None => Ok(true),
            Some(AttrValue::Str(value)) => {
                if work.eq(value, "lsb_lane0")? {
                    Ok(true)
                } else {
                    self.q(op, work)?;
                    work.text(" unsupported bit_order ", &mut self.reason)?;
                    work.quoted(value, &mut self.reason)?;
                    work.text("; expected \"lsb_lane0\"", &mut self.reason)?;
                    Ok(false)
                }
            }
            Some(_) => {
                self.q(op, work)?;
                work.text(" requires Str attribute \"bit_order\"", &mut self.reason)?;
                Ok(false)
            }
        }
    }
}
